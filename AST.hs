{-# LANGUAGE GADTs #-}
module AST where

data CtrlExpr where
    Assign :: String -> ValExpr                -> CtrlExpr
    Signal :: String -> ValExpr                -> CtrlExpr
    CaseC  :: [(BinExpr, CtrlExpr)]            -> CtrlExpr
    IfC    :: BinExpr -> CtrlExpr -> CtrlExpr  -> CtrlExpr
    Conj   :: [CtrlExpr]                       -> CtrlExpr
    deriving (Show)

data ValExpr where
    StringLit :: String                        -> ValExpr
    IntLit    :: Int                           -> ValExpr
    CaseV     :: [(BinExpr, ValExpr)]          -> ValExpr
    IfV       :: BinExpr -> ValExpr -> ValExpr -> ValExpr
    deriving (Show)

data BinOpType = And | Or deriving (Show)
data PredType  = Eq | Neq deriving (Show)

data BinExpr where
    TrueE  ::                                    BinExpr
    FalseE ::                                    BinExpr
    Not    :: BinExpr                         -> BinExpr
    Bin    :: BinOpType -> BinExpr -> BinExpr -> BinExpr
    Pred   :: PredType -> ValExpr -> ValExpr  -> BinExpr
    Atom   :: String                          -> BinExpr
    deriving (Show)

