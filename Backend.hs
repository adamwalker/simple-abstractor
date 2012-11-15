{-# LANGUAGE OverloadedStrings #-}

module Backend where

import Control.Monad
import Control.Monad.ST.Lazy 
import Data.Bits

import Data.Text.Lazy hiding (intercalate, map, take, length)
import Text.PrettyPrint.Leijen.Text

import CuddExplicitDeref

data AST v = T
           | F
           | Lit      v
           | Not      (AST v)
           | And      (AST v) (AST v)
           | Or       (AST v) (AST v)
           | Conj     [AST v]
           | Case     [(AST v, AST v)]
           | EqVar    [v] [v]
           | EqConst  [v] Int
           | Exists   (v -> AST v)
           | Let      (AST v) (AST v -> AST v)

prettyPrint :: (Show v) => AST v -> Doc
prettyPrint T             = text "True"
prettyPrint F             = text "False"
prettyPrint (Lit v)       = text $ pack $ show v
prettyPrint (Not e)       = text "!" <+> prettyPrint e
prettyPrint (And x y)     = parens $ prettyPrint x <+> text "&&" <+> prettyPrint y
prettyPrint (Or x y)      = parens $ prettyPrint x <+> text "||" <+> prettyPrint y
prettyPrint (Conj es)     = text "CONJ" <+> lbrace <$$> indent 4 (vcat $ map ((<> semi) . prettyPrint) es) <$$> rbrace
prettyPrint (Case cases)  = text "case" <+> lbrace <$$> indent 4 (vcat $ map (uncurry f) cases) <$$> rbrace
    where
    f c v = prettyPrint c <+> colon <+> prettyPrint v <+> semi
prettyPrint (EqVar x y)   = text (pack (show x)) <+> text "==" <+> text (pack (show y))
prettyPrint (EqConst x c) = text (pack (show x)) <+> text "==" <+> text (pack (show c))
prettyPrint (Exists func) = undefined
prettyPrint (Let x f)     = undefined

conj :: STDdManager s u -> [DDNode s u] -> ST s (DDNode s u)
conj m nodes = go (bone m) nodes
    where
    go accum []     = return accum
    go accum (n:ns) = do
        accum' <- band m accum n
        deref m accum
        deref m n
        go accum' ns

ccase :: STDdManager s u -> [(DDNode s u, DDNode s u)] -> ST s (DDNode s u)
ccase m = go (bzero m) (bzero m)
    where
    go accum neg [] = do
        deref m neg
        return accum
    go accum neg ((cond, cas): cs) = do
        --alive == cond, cas, accum, neg
        econd  <- band m cond (bnot neg)
        clause <- band m econd cas
        deref m econd
        deref m cas
        --alive == cond, accum, neg, clause
        accum' <- bor m clause accum
        deref m accum
        deref m clause
        --alive == cond, neg, accum'
        neg' <- bor m cond neg
        deref m cond
        deref m neg
        --alive == accum', neg'
        go accum' neg' cs

compile :: STDdManager s u ->  AST (DDNode s u) -> ST s (DDNode s u)
compile m = compile' where
    compile' T             = return $ bone m
    compile' F             = return $ bzero m
    compile' (Lit v)       = return v
    compile' (Not x)       = liftM bnot $ compile' x
    compile' (And x y)     = do
        x <- compile' x
        y <- compile' y
        res <- band m x y 
        deref m x
        deref m y
        return res
    compile' (Or x y)      = do
        x <- compile' x
        y <- compile' y
        res <- bor m x y
        deref m x
        deref m y
        return res
    compile' (Conj es)     = do
        es <- sequence $ map compile' es
        conj m es
    compile' (Case cs)     = do
        cs <- sequence $ map func cs 
        ccase m cs
        where
        func (x, y) = do
            x <- compile' x
            y <- compile' y
            return (x, y)
    compile' (EqVar x y)   = xeqy m x y
    compile' (EqConst x c) = computeCube m x $ take (length x) $ map (testBit c) [0..]
    compile' (Exists f)    = undefined
    compile' (Let x f)     = undefined

