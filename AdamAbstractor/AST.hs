{-# LANGUAGE GADTs, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module AdamAbstractor.AST where

import Data.Functor
import Data.Foldable
import Data.Traversable
import Data.Bifunctor as B
import Data.Bitraversable as B
import Data.Bifoldable as B
import Control.Applicative

import AdamAbstractor.Predicate hiding (EqPred)

--Variable declaration section

data Type where
    BoolType ::             Type
    IntType  :: Int      -> Type
    EnumType :: [String] -> Type

data Decl = Decl {
    vars    :: [String],
    absType :: VarAbsType,
    varType :: Type
}

--The transition section
--a = Type of things that can be assigned
--p = Type of atomic predicates
--v = Type of atomic values
data CtrlExpr a p v where
    Assign :: a -> ValExpr p v                 -> CtrlExpr a p v
    Signal :: String -> ValExpr p v            -> CtrlExpr a p v
    CaseC  :: [(BinExpr p, CtrlExpr a p v)]    -> CtrlExpr a p v
    Conj   :: [CtrlExpr a p v]                 -> CtrlExpr a p v
    deriving (Functor, Foldable, Traversable)

instance Bifunctor (CtrlExpr a) where
    bimap f g (Assign x y)  = Assign x (bimap f g y) 
    bimap f g (Signal x y)  = Signal x (bimap f g y)
    bimap f g (CaseC cases) = CaseC $ map (bimap (fmap f) (bimap f g)) cases
    bimap f g (Conj  parts) = Conj  $ map (bimap f g) parts

instance Bifoldable (CtrlExpr a) where
    bifoldr = error "BiFoldable: CtrlExpr"

instance Bitraversable (CtrlExpr a) where
    bisequenceA (Assign x y)  = Assign x <$> bisequenceA y
    bisequenceA (Signal x y)  = Signal x <$> bisequenceA y
    bisequenceA (CaseC cases) = CaseC <$> sequenceA (map (bisequenceA . bimap sequenceA bisequenceA) cases)
    bisequenceA (Conj  parts) = Conj  <$> sequenceA (map bisequenceA parts)

--newtype CtrlExpr2 v a = CtrlExpr2 (CtrlExpr a v) deriving (Functor, Foldable, Traversable)

type Slice = Maybe (Int, Int)

data ASTEqPred v = ASTEqPred {
    predTyp :: PredType,
    var1    :: ValExpr (ASTEqPred v) v,
    var2    :: ValExpr (ASTEqPred v) v
} deriving (Show)

instance Functor ASTEqPred where
    fmap func (ASTEqPred typ var1 var2) = ASTEqPred typ (B.bimap (fmap func) func var1) (B.bimap (fmap func) func var2)

instance Foldable    ASTEqPred where
    foldr = error "foldr: ASTEqPred"

instance Traversable ASTEqPred where
    sequenceA (ASTEqPred predTyp var1 var2) = ASTEqPred predTyp <$> help var1 <*> help var2
        where
        help :: Applicative f => ValExpr (ASTEqPred (f a)) (f a) -> f (ValExpr (ASTEqPred a) a)
        help = bisequenceA . B.first sequenceA 

data ValExpr p v where
    Lit       :: v                               -> ValExpr p v
    CaseV     :: [(BinExpr p, ValExpr p v)]      -> ValExpr p v
    deriving (Show, Functor, Foldable, Traversable)

instance Bifunctor ValExpr where
    bimap f g (Lit x)       = Lit $ g x
    bimap f g (CaseV cases) = CaseV $ fmap (bimap (fmap f) (bimap f g)) cases

instance Bifoldable ValExpr where
    bifoldr = error "bifoldr: valExpr"

instance Bitraversable ValExpr where
    bisequenceA (Lit x)       = Lit   <$> x
    bisequenceA (CaseV cases) = CaseV <$> sequenceA (map (bisequenceA . bimap sequenceA bisequenceA) cases)

data BinOpType = And | Or | Imp deriving (Show)
data PredType  = Eq | Neq deriving (Show)

data BinExpr p where
    TrueE  ::                                        BinExpr p
    FalseE ::                                        BinExpr p
    Not    :: BinExpr p                           -> BinExpr p
    Bin    :: BinOpType -> BinExpr p -> BinExpr p -> BinExpr p
    Pred   :: p                                   -> BinExpr p
    deriving (Show, Functor, Foldable, Traversable)

