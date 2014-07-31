{-# LANGUAGE GADTs #-}
module AdamAbstractor.Predicate (
    VarType(..),
    constructVarPred, 
    constructConstPred,
    EqPred(..),
    LabEqPred(..),
    VarAbsType(..),
    Section(..),
    eSectVarPred,
    eSectConstPred,
    eSectVar,
    labEqPredVars
    ) where

import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)

import Safe
import Data.Maybe

import Synthesis.Interface

type Slice = Maybe (Int, Int)

data VarType p = Enum String | Pred p
    deriving (Show, Eq, Ord)

data Section = StateSection | LabelSection | OutcomeSection
    deriving (Show, Eq, Ord)

eSectVarPred :: Section -> Section -> String -> Maybe (Int, Int) -> String -> Maybe (Int, Int) -> (BAVar (VarType EqPred) (VarType LabEqPred), Maybe String, Maybe (Int, Int))
eSectVarPred StateSection   StateSection   x s1 y s2 = (StateVar (Pred pred) 1, Nothing, Nothing) where pred = constructVarPred x s1 y s2
eSectVarPred LabelSection   StateSection   x s1 y s2 = (LabelVar (Pred pred) 1, Nothing, Nothing) where pred = constructLabPred x s1 y s2 False
eSectVarPred StateSection   LabelSection   x s1 y s2 = (LabelVar (Pred pred) 1, Nothing, Nothing) where pred = constructLabPred y s2 x s1 False
eSectVarPred OutcomeSection StateSection   x s1 y s2 = (OutVar (Pred pred) 1,   Nothing, Nothing) where pred = constructLabPred x s1 y s2 True
eSectVarPred StateSection   OutcomeSection x s1 y s2 = (OutVar (Pred pred) 1,   Nothing, Nothing) where pred = constructLabPred x s1 y s2 True
eSectVarPred LabelSection   OutcomeSection x s1 y s2 = (OutVar (Pred pred) 1,   Nothing, Nothing) where pred = constructLabPred x s1 y s2 True
eSectVarPred OutcomeSection LabelSection   x s1 y s2 = (OutVar (Pred pred) 1,   Nothing, Nothing) where pred = constructLabPred x s1 y s2 True
eSectVarPred LabelSection   LabelSection   x s1 y s2 = (LabelVar (Pred pred) 1, Nothing, Nothing) where pred = constructLabPred x s1 y s2 True
eSectVarPred OutcomeSection OutcomeSection x s1 y s2 = (OutVar (Pred pred) 1,   Nothing, Nothing) where pred = constructLabPred x s1 y s2 True
eSectVarPred x              y              _ _  _ _  = error $ "effectiveSection: " ++ show x ++ " " ++ show y

eSectConstPred :: Section -> String -> Maybe (Int, Int) -> Int -> (BAVar (VarType EqPred) (VarType LabEqPred), Maybe String, Maybe (Int, Int))
eSectConstPred StateSection   x s y = (StateVar (Pred pred) 1, Just x, Nothing) where pred = constructConstPred x s y
eSectConstPred LabelSection   x s y = (LabelVar (Pred pred) 1, Just x, Nothing) where pred = constructConstLabPred x s y
eSectConstPred OutcomeSection x s y = (OutVar   (Pred pred) 1, Just x, Nothing) where pred = constructConstLabPred x s y

eSectVar :: Section -> String -> Int -> Maybe (Int, Int) -> (BAVar (VarType EqPred) (VarType LabEqPred), Maybe String, Maybe (Int, Int))
eSectVar StateSection   n s sl = (StateVar (Enum n) s, Nothing, sl)
eSectVar LabelSection   n s sl = (LabelVar (Enum n) s, Nothing, sl)
eSectVar OutcomeSection n s sl = (OutVar   (Enum n) s, Nothing, sl)

--The variable declatarion section
data VarAbsType where
    Abs    :: VarAbsType
    NonAbs :: VarAbsType
    
data EqPred where
    EqVar   :: String -> Maybe (Int, Int) -> String -> Maybe (Int, Int) -> EqPred
    EqConst :: String -> Maybe (Int, Int) -> Int    -> EqPred
    deriving (Eq, Ord)

data LabEqPred where
    LabEqVar   :: String -> Maybe (Int, Int) -> String -> Maybe (Int, Int) -> Bool -> LabEqPred
    LabEqConst :: String -> Maybe (Int, Int) -> Int    -> LabEqPred
    deriving (Eq, Ord)

labEqPredVars :: LabEqPred -> [String]
labEqPredVars (LabEqVar v1 _ v2 _ _) = [v1, v2]
labEqPredVars (LabEqConst v1 _ _)    = [v1]

showSlice :: Slice -> String
showSlice Nothing       = ""
showSlice (Just (l, u)) = "[" ++ show l ++ ":" ++ show u ++ "]"

instance Show EqPred where
    show (EqVar l s1 r s2) = l ++ showSlice s1 ++ "==" ++ r ++ showSlice s2
    show (EqConst l s1 r)  = l ++ showSlice s1 ++ "==" ++ show r

instance Show LabEqPred where
    show (LabEqVar l s1 r s2 _) = l ++ showSlice s1 ++ "==" ++ r ++ showSlice s2
    show (LabEqConst l s1 r)    = l ++ showSlice s1 ++ "==" ++ show r

constructVarPred :: String -> Maybe (Int, Int) -> String -> Maybe (Int, Int) -> EqPred
constructVarPred x s1 y s2
    | x < y     = EqVar x s1 y s2
    | otherwise = EqVar y s2 x s1

constructConstPred :: String -> Maybe (Int, Int) -> Int -> EqPred
constructConstPred = EqConst

constructLabPred :: String -> Maybe (Int, Int) -> String -> Maybe (Int, Int) -> Bool -> LabEqPred
constructLabPred x s1 y s2 False = LabEqVar x s1 y s2 False
constructLabPred x s1 y s2 True
    | x < y     = LabEqVar x s1 y s2 True
    | otherwise = LabEqVar y s2 x s1 True

constructConstLabPred :: String -> Maybe (Int, Int) -> Int -> LabEqPred
constructConstLabPred = LabEqConst

