{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

import           Control.Monad        hiding (fmap)
import           Data.Aeson           (ToJSON, FromJSON)
import           Data.List.NonEmpty   (NonEmpty (..))
import           Data.Map             as Map
import           Data.Text            (pack, Text)
import           GHC.Generics         (Generic)
import           Plutus.Contract
import qualified PlutusTx             as PlutusTx
import           PlutusTx.Prelude     hiding (Semigroup(..), unless)
import qualified PlutusTx.Prelude     as Plutus
import           Ledger               hiding (singleton)
import           Ledger.Constraints   as Constraints
import qualified Ledger.Scripts       as Scripts
import qualified Ledger.Typed.Scripts as Scripts hiding (validatorHash)
import           Ledger.Value         as Value
import           Ledger.Ada           as Ada
import           Playground.Contract  (ensureKnownCurrencies, printSchemas, stage, printJson)
import           Playground.TH        (mkKnownCurrencies, mkSchemaDefinitions)
import           Playground.Types     (KnownCurrency (..))
import           Prelude              (IO, Semigroup (..), Show (..), String)
import           Schema               (ToSchema)
import           Text.Printf          (printf)
import System.Random as R

{-# OPTIONS_GHC -fno-warn-unused-imports #-}
data Raffle = Raffle {
      lGameHost :: !PubKeyHash
    , lDeadline :: !POSIXTime
    , lTicketPrice :: !Integer
    , lCurrency :: !CurrencySymbol
    , lToken :: !TokenName
    } deriving (Show, Generic, ToJSON, FromJSON, ToSchema)

PlutusTx.unstableMakeIsData ''Raffle
PlutusTx.makeLift ''Raffle

data Participant = Participant
    { pParticipant :: !PubKeyHash
    , pAmount :: !Integer
    } deriving (Show)

PlutusTx.unstableMakeIsData ''Participant
PlutusTx.makeLift ''Participant

data RaffleAction = BuyTicket Participant | Close {clWinner :: !(Maybe PubKeyHash)}
    deriving (Show)

PlutusTx.unstableMakeIsData ''RaffleAction
PlutusTx.makeLift ''RaffleAction

data RaffleDatum = RaffleDatum
    { adRaffle :: !Raffle
    , adParticipants :: ![Participant]
    } deriving Show

PlutusTx.unstableMakeIsData ''RaffleDatum
PlutusTx.makeLift ''RaffleDatum

{-# INLINABLE mkValidator #-}
mkValidator :: RaffleDatum -> RaffleAction -> ScriptContext -> Bool
mkValidator ad redeemer ctx =    
    case redeemer of
        BuyTicket p@Participant{..}     ->
                traceIfFalse "The amount is insuficient" $ sufficientAmount p       &&
                traceIfFalse "Too Late" correctBuySlotRange
        Close winner                    ->
                -- We don't care how gets to close the raffle since it won't change the outcome, so we don't check
                traceIfFalse "Too soon to close the raffle" correctCloseSlotRange  &&
                case winner of
                    --If there is no winner that would mean that there were no participants
                    Nothing         ->
                        traceIfFalse "Expected game host to recieve token" (getsValue (lGameHost raffleInfo) tokenValue)
                    Just winnerPkh  ->
                        traceIfFalse "Expected winner to be in the list of participants" (winnerInList winnerPkh)      &&
                        traceIfFalse "Expected winner to recieve token" (getsValue winnerPkh tokenValue)  &&
                        traceIfFalse "Expected game host to get the total amount of money betted" hostRecievedTotalAmount
    where
        info :: TxInfo
        info = scriptContextTxInfo ctx

        raffleInfo :: Raffle
        raffleInfo = adRaffle ad

        tokenValue :: Value
        tokenValue = Value.singleton (lCurrency raffleInfo) (lToken raffleInfo) 1

        sufficientAmount :: Participant -> Bool
        sufficientAmount p = (pAmount p) >= (lTicketPrice raffleInfo)

        correctBuySlotRange :: Bool
        correctBuySlotRange = to (lDeadline raffleInfo) `contains` txInfoValidRange info

        correctCloseSlotRange :: Bool
        correctCloseSlotRange = from (lDeadline raffleInfo) `contains` txInfoValidRange info

        winnerInList :: PubKeyHash -> Bool
        winnerInList w = w `elem` (PlutusTx.Prelude.map pParticipant $ adParticipants ad)

        getsValue :: PubKeyHash -> Value -> Bool
        getsValue h v =
            let
                [o] = [o' | o' <- txInfoOutputs info, txOutValue o' == v]
            in
                txOutAddress o == pubKeyHashAddress h

        outputTokens :: [Value]
        outputTokens = PlutusTx.Prelude.map txOutValue $ txInfoOutputs info

        hostRecievedTotalAmount :: Bool
        hostRecievedTotalAmount = getsValue (lGameHost raffleInfo) totalValue
            where
                total :: Integer
                total = (length (adParticipants ad)) * (lTicketPrice raffleInfo)
                totalValue :: Value
                totalValue = Value.singleton Ada.adaSymbol Ada.adaToken total


data Typed
instance Scripts.ValidatorTypes Typed where
    type instance DatumType Typed = RaffleDatum
    type instance RedeemerType Typed = RaffleAction

typedValidator :: Scripts.TypedValidator Typed
typedValidator =  Scripts.mkTypedValidator @Typed
    $$(PlutusTx.compile [|| mkValidator ||])
    $$(PlutusTx.compile [|| wrap ||])
    where
        wrap = Scripts.wrapValidator @RaffleDatum @RaffleAction

validator :: Validator
validator = Scripts.validatorScript typedValidator

data StartParams = StartParams
    { spDeadline :: !POSIXTime
    , spTicketPrice :: !Integer
    , spCurrency :: !CurrencySymbol
    , spToken :: !TokenName
    } deriving (Generic, ToJSON, FromJSON, ToSchema)

data BuyParams = BuyParams 
    { bpCurrency :: !CurrencySymbol
    , bpToken :: !TokenName   
    } deriving (Generic, ToJSON, FromJSON, ToSchema)

data CloseParams = CloseParams 
    { cpCurrency :: !CurrencySymbol
    , cpToken :: !TokenName
    } deriving (Generic, ToJSON, FromJSON, ToSchema)

type RaffleSchema =
    Endpoint  "start" StartParams .\/
    Endpoint "buyTicket" BuyParams .\/
    Endpoint "close" CloseParams

start :: StartParams -> Contract w s Text ()
start StartParams{..} = do
    pkh <- pubKeyHash <$> ownPubKey
    let a = Raffle
                { lGameHost = pkh
                , lDeadline = spDeadline
                , lTicketPrice = spTicketPrice
                , lCurrency = spCurrency
                , lToken = spToken
                }
        d = RaffleDatum
                { adRaffle = a
                , adParticipants = []
                }
        v = Value.singleton spCurrency spToken 1
        tx = mustPayToTheScript d v
    
    ledgerTx <- submitTxConstraints typedValidator tx
    void $ awaitTxConfirmed $ txId ledgerTx
    logInfo @String $ printf "started raffle %s for token %s" (show a) (show v)

buyTicket :: BuyParams -> Contract w s Text ()
buyTicket BuyParams{..} = do 
    (oref, o, d@RaffleDatum{..}) <- findAuction bpCurrency bpToken
    logInfo @String $ printf "found auction utxo with datum %s" (show d)

    pkh <- pubKeyHash <$> ownPubKey
    let ticketPrice = lTicketPrice adRaffle
        p = Participant {pParticipant = pkh, pAmount = ticketPrice}
        newParticipantsList = adParticipants ++ [p]
        d' = d { adParticipants = newParticipantsList }
        v = Ada.lovelaceValueOf ticketPrice <> (txOutValue $ txOutTxOut o)
        r = Redeemer $ PlutusTx.toData $ BuyTicket p

        lookups = Constraints.typedValidatorLookups typedValidator  <>
                Constraints.otherScript validator                   <>
                Constraints.unspentOutputs (Map.singleton oref o)
        
        tx      = mustPayToTheScript d' v                   <>
                  mustValidateIn (to $ lDeadline adRaffle) <>
                  mustSpendScriptOutput oref r

    ledgerTx <- submitTxConstraintsWith lookups tx
    void $ awaitTxConfirmed $ txId ledgerTx
    logInfo @String $ printf "bouth ticket for token (%s, %s)" (show bpCurrency) (show bpToken)

close :: CloseParams -> Contract w s Text ()
close CloseParams{..} = do 
    (oref, o, d@RaffleDatum{..}) <- findAuction cpCurrency cpToken
    logInfo @String $ printf "found auction utxo with datum %s" (show d)

    let v = Value.singleton cpCurrency cpToken 1
        -- Choose a winner randomly
        winner = case adParticipants of
            []   -> Nothing
            ps   -> Just $ pParticipant (ps !! (giveRandomInteger $ length ps))

        r = Redeemer $ PlutusTx.toData $ Close {clWinner = winner}
        
        lookups = Constraints.typedValidatorLookups typedValidator <>
                Constraints.otherScript validator <>
                Constraints.unspentOutputs (Map.singleton oref o)
        
        tx = case winner of 
                Nothing     -> do
                    mustPayToPubKey (lGameHost adRaffle) v <> mustSpendScriptOutput oref r
                Just w      -> do
                    mustPayToPubKey w v <> mustValidateIn (from $ lDeadline adRaffle) <> mustPayToPubKey hostPubKey (Ada.lovelaceValueOf totalFunds) <> mustSpendScriptOutput oref r
                        where
                            hostPubKey = lGameHost $ adRaffle
                            totalFunds = (length adParticipants) * (lTicketPrice adRaffle)
    ledgerTx <- submitTxConstraintsWith lookups tx
    void $ awaitTxConfirmed $ txId ledgerTx
    logInfo @String "Game Over!"

findAuction :: CurrencySymbol -> TokenName -> Contract w s Text (TxOutRef, TxOutTx, RaffleDatum)
findAuction cs tn = do 
    utxos <- utxoAt $ scriptAddress validator 
    let xs = [(oref, o) | (oref, o) <- Map.toList utxos, Value.valueOf (txOutValue $ txOutTxOut o) cs tn == 1]
    case xs of 
        [(oref, o)] -> case txOutDatumHash $ txOutTxOut o of 
            Nothing     -> throwError "unexpected output type"
            Just h      -> case Map.lookup h $ txData $ txOutTxTx o of 
                Nothing         -> throwError "datum not found"
                Just (Datum e)  -> case PlutusTx.fromData e of 
                    Nothing                 -> throwError "datum was from type"
                    Just d@RaffleDatum{..} 
                        | lCurrency adRaffle == cs && lToken adRaffle == tn   -> return (oref, o, d)
                        | otherwise                                             -> throwError "action token missmatch"

        _           -> throwError "auction utxo not found"

giveRandomInteger :: Integer -> Integer
giveRandomInteger l = let (i, g) = R.randomR (0, l-1) $ mkStdGen 42 :: (Integer, StdGen) in i

endpoints :: Contract () RaffleSchema Text ()
endpoints = (start' `select` buyTicket' `select` close') >> endpoints
        where
                start' = endpoint @"start" >>= start
                buyTicket' = endpoint @"buyTicket" >>= buyTicket
                close' = endpoint @"close" >>= close

mkSchemaDefinitions ''RaffleSchema

myToken :: KnownCurrency
myToken = KnownCurrency (ValidatorHash "f") "Token" (TokenName "T" :| [])

mkKnownCurrencies ['myToken]
