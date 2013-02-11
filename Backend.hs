{-# LANGUAGE OverloadedStrings, RecordWildCards, PolymorphicComponents #-}

module Backend (
    AST(..),
    prettyPrint,
    compile,
    conj,
    disj
    ) where

import Control.Monad
import Control.Monad.ST.Lazy 
import Data.Bits
import Control.Monad.State

import Data.Text.Lazy hiding (intercalate, map, take, length)
import Text.PrettyPrint.Leijen.Text

import CuddExplicitDeref
import Interface

data AST f v c pred var = T
                      | F
                      | Not      (AST f v c pred var)
                      | And      (AST f v c pred var) (AST f v c pred var)
                      | Or       (AST f v c pred var) (AST f v c pred var)
                      | Imp      (AST f v c pred var) (AST f v c pred var)
                      | XNor     (AST f v c pred var) (AST f v c pred var)
                      | Conj     [AST f v c pred var]
                      | Disj     [AST f v c pred var]
                      | Case     [(AST f v c pred var, AST f v c pred var)]
                      | EqVar    (Either f var) var
                      | EqConst  (Either f var) Int
                      | Pred     pred
                      | Exists   (v -> AST f v c pred var)
                      | QuantLit v
                      | Let      (AST f v c pred var) (c -> AST f v c pred var)
                      | LetLit   c

testAST = Let (And T F) (\x -> LetLit x `Or` (Exists $ \v -> LetLit x `And` QuantLit v `Or` Pred "pp"))

prettyPrint :: (Show p, Show v) => AST Doc Doc Doc p v -> Doc
prettyPrint = prettyPrint' 0
    where
    prettyPrint' ng = prettyPrint''
        where
        prettyPrint'' T             = text "True"
        prettyPrint'' F             = text "False"
        prettyPrint'' (Not e)       = text "!" <+> prettyPrint'' e
        prettyPrint'' (And x y)     = parens $ prettyPrint'' x <+> text "&&"  <+> prettyPrint'' y
        prettyPrint'' (Or x y)      = parens $ prettyPrint'' x <+> text "||"  <+> prettyPrint'' y
        prettyPrint'' (Imp x y)     = parens $ prettyPrint'' x <+> text "->"  <+> prettyPrint'' y
        prettyPrint'' (XNor x y)    = parens $ prettyPrint'' x <+> text "<->" <+> prettyPrint'' y
        prettyPrint'' (Conj es)     = text "CONJ" <+> lbrace <$$> indent 4 (vcat $ map ((<> semi) . prettyPrint'') es) <$$> rbrace
        prettyPrint'' (Disj es)     = text "Disj" <+> lbrace <$$> indent 4 (vcat $ map ((<> semi) . prettyPrint'') es) <$$> rbrace
        prettyPrint'' (Case cases)  = text "case" <+> lbrace <$$> indent 4 (vcat $ map (uncurry f) cases) <$$> rbrace
            where  
            f c v =   prettyPrint'' c <+> colon <+> prettyPrint'' v <+> semi
        prettyPrint'' (EqVar (Right x) y)   = text (pack (show x)) <+> text "==" <+> text (pack (show y))
        prettyPrint'' (EqVar (Left x) y)   = x <+> text "==" <+> text (pack (show y))
        prettyPrint'' (EqConst (Right x) c) = text (pack (show x)) <+> text "==" <+> text (pack (show c))
        prettyPrint'' (EqConst (Left x) c) = x <+> text "==" <+> text (pack (show c))
        prettyPrint'' (Pred x)      = parens $ text $ pack $ "predicate: " ++ show x
        prettyPrint'' (Exists func) = text "exists" <+> parens (text $ pack $ "tvar" ++ show ng) <+> lbrace <$$> indent 4 (prettyPrint' (ng + 1)$ func (text $ pack $ "tvar" ++ show ng)) <$$> rbrace
        prettyPrint'' (QuantLit x)  = x
        prettyPrint'' (Let x f)     = text "let" <+> text "tmp" <+> text ":=" <+> prettyPrint'' x <+> text "in" <$$> indent 4 (prettyPrint'' $ f (text "tmp"))
        prettyPrint'' (LetLit x)    = x

block :: (STDdManager s u -> DDNode s u -> DDNode s u -> ST s (DDNode s u)) -> (STDdManager s u -> DDNode s u) -> STDdManager s u -> [DDNode s u] -> ST s (DDNode s u)
block func s m nodes = do
    ref (s m)
    go (s m) nodes
    where
    go accum []     = return accum
    go accum (n:ns) = do
        accum' <- func m accum n
        deref m accum
        deref m n
        go accum' ns

conj = block band bone
disj = block bor  bzero

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

compile :: STDdManager s u -> VarOps pdb p v s u -> AST [DDNode s u] (DDNode s u) (DDNode s u) p v -> StateT pdb (ST s) (DDNode s u)
compile m VarOps{..} = compile' where
    compile' T             = do
        lift $ ref $ bone m
        return $ bone m
    compile' F             = do
        lift $ ref $ bzero m
        return $ bzero m
    compile' (Not x)       = liftM bnot $ compile' x
    compile' (And x y)     = do
        x <- compile' x
        y <- compile' y
        res <- lift $ band m x y 
        lift $ deref m x
        lift $ deref m y
        return res
    compile' (Or x y)      = do
        x <- compile' x
        y <- compile' y
        res <- lift $ bor m x y
        lift $ deref m x
        lift $ deref m y
        return res
    compile' (XNor x y)      = do
        x <- compile' x
        y <- compile' y
        res <- lift $ bxnor m x y
        lift $ deref m x
        lift $ deref m y
        return res
    compile' (Imp x y)      = do
        x <- compile' x
        y <- compile' y
        res <- lift $ bor m (bnot x) y
        lift $ deref m x
        lift $ deref m y
        return res
    compile' (Conj es)     = do
        es <- sequence $ map compile' es
        lift $ conj m es
    compile' (Disj es)     = do
        es <- sequence $ map compile' es
        lift $ disj m es
    compile' (Case cs)     = do
        cs <- sequence $ map func cs 
        lift $ ccase m cs
        where
        func (x, y) = do
            x <- compile' x
            y <- compile' y
            return (x, y)
    compile' (EqVar x y)   = do
        x <- either return getVar x
        y <- getVar y
        lift $ xeqy m x y
    compile' (EqConst x c) = do
        x <- either return getVar x
        lift $ computeCube m x $ take (length x) $ map (testBit c) [0..]
    compile' (Pred x)      = do
        res <- getPred x
        lift $ ref res
        return res
    compile' (Exists f)    = withTmp $ \x -> do
        res' <- compile' $ f x
        res  <- lift $ bexists m res' x
        lift $ deref m res'
        return res
    compile' (QuantLit x)  = do
        lift $ ref x
        return x
    compile' (Let x f)     = do
        bind <- compile' x
        res  <- compile' (f bind)
        lift $ deref m bind
        return res
    compile' (LetLit x)    = do
        lift $ ref x
        return x

