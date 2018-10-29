module GenSemantics where

import Semantics
import Test.QuickCheck
import qualified Data.Map as M
import qualified Data.Set as S

positiveAmount :: Gen Integer
positiveAmount = fmap abs arbitrary

-- Comment out this line to test with negative values too
amount = positiveAmount

arbitraryMoneyAux :: Int -> Gen Money
arbitraryMoneyAux s
 | s > 0 = oneof [(AvailableMoney . IdentCC) <$> amount
                 ,(AddMoney <$> arbitraryMoneyAux (s - 1)) <*> arbitraryMoneyAux (s - 1)
                 ,ConstMoney <$> amount
                 ,(MoneyFromChoice . IdentChoice) <$> amount <*> amount <*> arbitraryMoneyAux (s - 1)]
 | s == 0 = oneof [(AvailableMoney . IdentCC) <$> amount
                  ,ConstMoney <$> arbitrary]
 | otherwise = error "Negative size in arbitraryMoney"
 
arbitraryMoney :: Gen Money
arbitraryMoney = sized arbitraryMoneyAux

arbitraryObservationAux :: Int -> Gen Observation
arbitraryObservationAux s
 | s > 0 = oneof [BelowTimeout <$> amount
                 ,AndObs <$> arbitraryObservationAux (s - 1) <*> arbitraryObservationAux (s - 1) 
                 ,OrObs <$> arbitraryObservationAux (s - 1) <*> arbitraryObservationAux (s - 1)
                 ,NotObs <$> arbitraryObservationAux (s - 1)  
                 ,(PersonChoseThis . IdentChoice) <$> amount <*> amount <*> amount
                 ,(PersonChoseSomething . IdentChoice) <$> amount <*> amount
                 ,ValueGE <$> arbitraryMoneyAux (s - 1) <*> arbitraryMoneyAux (s - 1)
                 ,pure TrueObs,pure FalseObs]
 | s == 0 = oneof [BelowTimeout <$> amount
                  ,(PersonChoseThis . IdentChoice) <$> amount <*> amount <*> amount
                  ,(PersonChoseSomething . IdentChoice) <$> amount <*> amount
                  ,pure TrueObs,pure FalseObs]
 | otherwise = error "Negative size in arbitraryObservation"


arbitraryObservation :: Gen Observation
arbitraryObservation = sized arbitraryObservationAux

arbitraryContractAux :: Int -> Gen Contract
arbitraryContractAux s
 | s > 0 = oneof [pure Null
                 ,(CommitCash . IdentCC) <$> amount <*> amount <*> arbitraryMoneyAux (s - 1) <*> amount <*> amount <*> arbitraryContractAux (s - 1) <*> arbitraryContractAux (s - 1) 
                 ,(RedeemCC . IdentCC) <$> amount <*> arbitraryContractAux (s - 1)
                 ,(Pay . IdentPay) <$> amount <*> amount <*> amount <*> arbitraryMoneyAux (s - 1) <*> amount <*> arbitraryContractAux (s - 1)
                 ,Both <$> arbitraryContractAux (s - 1) <*> arbitraryContractAux (s - 1)
                 ,Choice <$> arbitraryObservationAux (s - 1) <*> arbitraryContractAux (s - 1) <*> arbitraryContractAux (s - 1)
                 ,When <$> arbitraryObservationAux (s - 1) <*> amount <*> arbitraryContractAux (s - 1) <*> arbitraryContractAux (s - 1)]
 | s == 0 = oneof [pure Null]
 | otherwise = error "Negative size in arbitraryObservation"

arbitraryContract :: Gen Contract
arbitraryContract = sized arbitraryContractAux

arbitraryCC :: Gen CC
arbitraryCC = (CC . IdentCC) <$> amount <*> amount <*> amount <*> amount

arbitraryRC :: Gen RC
arbitraryRC = (RC . IdentCC) <$> amount <*> amount <*> amount

arbitraryRPEntry :: Gen ((IdentPay, Person), Cash)
arbitraryRPEntry = (\x y z -> ((IdentPay x, y), z)) <$> amount <*> amount <*> amount

arbitraryICEntry :: Gen ((IdentChoice, Person), ConcreteChoice)
arbitraryICEntry = (\x y z -> ((IdentChoice x, y), z)) <$> amount <*> amount <*> amount

arbitraryInputAux :: Int -> Gen Input
arbitraryInputAux s = (\w x y z -> Input (S.fromList w) (S.fromList x) (M.fromList y) (M.fromList z))
                      <$> vectorOf s arbitraryCC <*> vectorOf s arbitraryRC <*> vectorOf s arbitraryRPEntry <*> vectorOf s arbitraryICEntry

arbitraryInput :: Gen Input
arbitraryInput = sized arbitraryInputAux



