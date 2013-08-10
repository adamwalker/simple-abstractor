{-# LANGUAGE GADTs #-}
module AdamAbstractor.Predicate (
    VarType(..),
    constructVarPred, 
    constructConstPred,
    EqPred(..),
    consistencyPreds,
    VarAbsType(..),
    Section(..),
    eSectVarPred,
    eSectConstPred,
    eSectVar
    ) where

import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)

import Safe
import Data.Maybe

import Interface

type Slice = Maybe (Int, Int)

data VarType p = Enum String | Pred p
    deriving (Show, Eq, Ord)

data Section = StateSection | LabelSection | OutcomeSection
    deriving (Show, Eq, Ord)

eSectVarPred :: Section -> Section -> String -> Maybe (Int, Int) -> String -> Maybe (Int, Int) ->  (BAVar (VarType EqPred) (VarType EqPred), EqPred)
eSectVarPred StateSection   StateSection   x s1 y s2 = (StateVar (Pred pred) 1, pred) where pred = constructVarPred   x s1 y s2
eSectVarPred LabelSection   StateSection   x s1 y s2 = (LabelVar (Pred pred) 1, pred) where pred = constructLabelPred x s1 y s2
eSectVarPred StateSection   LabelSection   x s1 y s2 = (LabelVar (Pred pred) 1, pred) where pred = constructLabelPred y s2 x s1 
eSectVarPred OutcomeSection StateSection   x s1 y s2 = (OutVar (Pred pred) 1, pred)   where pred = constructVarPred   x s1 y s2
eSectVarPred StateSection   OutcomeSection x s1 y s2 = (OutVar (Pred pred) 1, pred)   where pred = constructVarPred   x s1 y s2
eSectVarPred LabelSection   OutcomeSection x s1 y s2 = (OutVar (Pred pred) 1, pred)   where pred = constructVarPred   x s1 y s2
eSectVarPred OutcomeSection LabelSection   x s1 y s2 = (OutVar (Pred pred) 1, pred)   where pred = constructVarPred   x s1 y s2
eSectVarPred LabelSection   LabelSection   x s1 y s2 = (LabelVar (Pred pred) 1, pred) where pred = constructVarPred   x s1 y s2
eSectVarPred x              y              _ _  _ _  = error $ "effectiveSection: " ++ show x ++ " " ++ show y

eSectConstPred :: Section -> String -> Maybe (Int, Int) -> Int -> (BAVar (VarType EqPred) (VarType EqPred), EqPred)
eSectConstPred StateSection   x s y = (StateVar (Pred pred) 1, pred) where pred = constructConstPred x s y
eSectConstPred LabelSection   x s y = (LabelVar (Pred pred) 1, pred) where pred = constructConstPred x s y
eSectConstPred OutcomeSection x s y = (OutVar   (Pred pred) 1, pred) where pred = constructConstPred x s y

eSectVar :: Section -> String -> Int -> BAVar (VarType EqPred) (VarType EqPred)
eSectVar StateSection   n = StateVar (Enum n)
eSectVar LabelSection   n = LabelVar (Enum n)
eSectVar OutcomeSection n = OutVar   (Enum n)

--The variable declatarion section
data VarAbsType where
    Abs    :: VarAbsType
    NonAbs :: VarAbsType
    
data EqPred where
    EqVar   :: String -> Maybe (Int, Int) -> String -> Maybe (Int, Int) -> EqPred
    EqConst :: String -> Maybe (Int, Int) -> Int    -> EqPred
    deriving (Eq, Ord)

showSlice :: Slice -> String
showSlice Nothing       = ""
showSlice (Just (l, u)) = "[" ++ show l ++ ":" ++ show u ++ "]"

instance Show EqPred where
    show (EqVar l s1 r s2) = l ++ showSlice s1 ++ "==" ++ r ++ showSlice s2
    show (EqConst l s1 r)  = l ++ showSlice s1 ++ "==" ++ show r

constructVarPred :: String -> Maybe (Int, Int) -> String -> Maybe (Int, Int) -> EqPred
constructVarPred x s1 y s2
    | x < y     = EqVar x s1 y s2
    | otherwise = EqVar y s2 x s1

constructConstPred :: String -> Maybe (Int, Int) -> Int -> EqPred
constructConstPred = EqConst

--first argument is the label
constructLabelPred :: String -> Maybe (Int, Int) -> String -> Maybe (Int, Int) -> EqPred
constructLabelPred = EqVar

aggregate :: (Ord a) => [(a, b)] -> Map a [b]
aggregate = foldl f Map.empty
    where
    f mp (a, b) = case Map.lookup a mp of
        Just x -> Map.insert a (b:x) mp
        Nothing -> Map.insert a [b] mp

help :: Maybe [a] -> [a]
help Nothing  = []
help (Just x) = x

--Assumes predicate pairs respect an arbitrary total ordering on variables
consistencyPreds :: [(String, String)] -> [(String, String, String)]
consistencyPreds preds = concatMap func vars
    where
    set1 = Set.fromList $ map fst preds
    vars = Set.toList set1
    set2 = Set.fromList $ map snd preds
    map1 = aggregate $ filter (\x -> snd x `Set.member` set1) preds
    map2 = aggregate $ filter (\x -> fst x `Set.member` set2) preds 
    setc = Set.fromList preds
    func :: String -> [(String, String, String)]
    func var = concatMap (func2 var) $ help $ Map.lookup var map1
        where
        func2 :: String -> String -> [(String, String, String)]
        func2 varx vary = mapMaybe (func3 varx vary) $ fromJustNote "consistencyPreds" $ Map.lookup vary map2 
            where
            func3 :: String -> String -> String -> Maybe (String, String, String)
            func3 varx vary varz 
                | (varx, varz) `Set.member` setc = Just (varx, vary, varz)
                | otherwise = Nothing

