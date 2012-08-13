{-# LANGUAGE GADTs #-}
module Predicate (
    constructVarPred, 
    constructConstPred,
    getPred,
    EqPred
    ) where

data EqPred where
    EqVar   :: String -> String -> EqPred
    EqConst :: String -> Int    -> EqPred
    deriving (Eq, Ord)

instance Show EqPred where
    show (EqVar l r)   = l ++ "==" ++ r
    show (EqConst l r) = l ++ "==" ++ show r

constructVarPred :: String -> String -> EqPred
constructVarPred x y
    | x < y     = EqVar x y
    | otherwise = EqVar y x

constructConstPred :: String -> Int -> EqPred
constructConstPred = EqConst

getPred :: EqPred -> Either (String, String) (String, Int) 
getPred (EqVar l r)   = Left (l, r)
getPred (EqConst l r) = Right (l, r)

