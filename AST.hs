{-# LANGUAGE GADTs, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module AST where

import Data.Functor
import Data.Foldable
import Data.Traversable

import Predicate

--Top
data Spec = Spec {
    stateDecls :: [Decl],
    labelDecls :: [Decl],
    trans      :: CtrlExpr String (Either String Int)
}

--Variable declaration section
data Decl = Decl {
    vars    :: [String],
    absType :: VarAbsType
}

--The transition section
data CtrlExpr a v where
    Assign :: a -> ValExpr v                   -> CtrlExpr a v
    Signal :: String -> ValExpr v              -> CtrlExpr a v
    CaseC  :: [(BinExpr v, CtrlExpr a v)]      -> CtrlExpr a v
    Conj   :: [CtrlExpr a v]                   -> CtrlExpr a v
    deriving (Show, Functor, Foldable, Traversable)

--newtype CtrlExpr2 v a = CtrlExpr2 (CtrlExpr a v) deriving (Functor, Foldable, Traversable)

data ValExpr v where
    Lit       :: v                             -> ValExpr v
    CaseV     :: [(BinExpr v, ValExpr v)]      -> ValExpr v
    deriving (Show, Functor, Foldable, Traversable)

data BinOpType = And | Or deriving (Show)
data PredType  = Eq | Neq deriving (Show)

data BinExpr v where
    TrueE  ::                                        BinExpr v
    FalseE ::                                        BinExpr v
    Not    :: BinExpr v                           -> BinExpr v
    Bin    :: BinOpType -> BinExpr v -> BinExpr v -> BinExpr v
    Pred   :: PredType -> ValExpr v -> ValExpr v  -> BinExpr v
    deriving (Show, Functor, Foldable, Traversable)

