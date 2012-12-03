{-# LANGUAGE GADTs #-}
module Predicate (
    constructVarPred, 
    constructConstPred,
    getPred,
    EqPred,
    PredEither,
    NSEQPred(..),
    consistencyPreds,
    toVarPair
    ) where

import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)

import Safe
import Data.Maybe

type Var  = (String, Section)

type Pred = (EqPred, Section)

effectiveSection :: Section -> Section -> Section
effectiveSection StateSection StateSection = StateSection
effectiveSection _            _            = LabelSection

data Section = StateSection | LabelSection
    deriving (Eq, Ord)

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

type PredEither = Either (String, String) (String, Int)

getPred :: EqPred -> PredEither
getPred (EqVar l r)   = Left (l, r)
getPred (EqConst l r) = Right (l, r)

toVarPair :: EqPred -> Maybe (String, String)
toVarPair (EqVar x y) = Just (x, y)
toVarPair _           = Nothing

data NSEQPred where
    NsEqVar   :: String -> String -> NSEQPred
    NsEqConst :: String -> Int    -> NSEQPred
    deriving (Eq, Ord)

aggregate :: (Ord a) => [(a, b)] -> Map a [b]
aggregate args = foldl f Map.empty args
    where
    f mp (a, b) = case Map.lookup a mp of
        Just x -> Map.insert a (b:x) mp
        Nothing -> Map.insert a [b] mp

help :: Maybe [a] -> [a]
help Nothing  = []
help (Just x) = x

--Assumes predicate pairs respect an arbitrary total ordering on variables
consistencyPreds :: [(String, String)] -> [(String, String, String)]
consistencyPreds preds = concat $ map func vars
    where
    set1 = Set.fromList $ map fst preds
    vars = Set.toList set1
    set2 = Set.fromList $ map snd preds
    map1 = aggregate $ filter (\x -> snd x `Set.member` set1) preds
    map2 = aggregate $ filter (\x -> fst x `Set.member` set2) preds 
    setc = Set.fromList $ preds
    func :: String -> [(String, String, String)]
    func var = concat $ map (func2 var) $ help $ Map.lookup var map1
        where
        func2 :: String -> String -> [(String, String, String)]
        func2 varx vary = catMaybes $ map (func3 varx vary) $ fromJustNote "consistencyPreds" $ Map.lookup vary map2 
            where
            func3 :: String -> String -> String -> Maybe (String, String, String)
            func3 varx vary varz 
                | (varx, varz) `Set.member` setc = Just (varx, vary, varz)
                | otherwise = Nothing

{-
(x, y) (y, z) (x, z)
only pairs where second element of tuple also occurs as a first for the first lookup
only pairs where first element of tuple occurs as a second

what about:

x==y && y==8 && x==8


-}

