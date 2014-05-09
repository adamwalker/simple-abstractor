{-# LANGUAGE RecordWildCards, PolymorphicComponents, ScopedTypeVariables, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module AdamAbstractor.TopLevel where

import Control.Applicative
import Data.Foldable
import Data.Traversable hiding (mapM)
import Data.Bifunctor as B
import Data.Bitraversable

import Text.Parsec hiding ((<|>))
import qualified Text.Parsec.Token as T
import Text.Parsec.Language

import AdamAbstractor.AST hiding (Pred)
import AdamAbstractor.Predicate as Predicate

stdDef = emptyDef {T.identStart = letter <|> char '_'
                  ,T.identLetter = alphaNum <|> char '_'
                  ,T.commentStart = "/*"
                  ,T.commentEnd = "*/"
                  ,T.commentLine = "//"
                  }

data Decls = Decls {
    stateDecls   :: [Decl],
    labelDecls   :: [Decl],
    outcomeDecls :: [Decl]
}

data BinExp  a = BinExp  {unBinExp  :: BinExpr (ASTEqPred a)} deriving (Functor, Foldable, Traversable)
data CtrlExp a = CtrlExp {unCtrlExp :: CtrlExpr String (ASTEqPred a) a} 

instance Functor CtrlExp where
    fmap f (CtrlExp cexp) = CtrlExp $ bimap (fmap f) f cexp

instance Foldable    CtrlExp where
    foldr = error "foldr: CtrlExp"

instance Traversable CtrlExp where
    sequenceA (CtrlExp cexp) = CtrlExp <$> bisequenceA (B.first sequenceA cexp)

