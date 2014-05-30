{-# LANGUAGE OverloadedStrings, RecordWildCards, PolymorphicComponents, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

module AdamAbstractor.Backend (
    AST(..),
    Leaf(..),
    prettyPrint,
    compile,
    conj,
    disj,
    eqVar,
    eqConst
    ) where

import Control.Monad
import Control.Monad.ST
import Data.Bits
import Control.Monad.State hiding (mapM)
import Data.Functor
import Data.Foldable
import Data.Traversable hiding (mapM)
import Control.Applicative
import Data.Bifunctor

import Data.Text.Lazy hiding (intercalate, map, take, length)
import Text.PrettyPrint.Leijen.Text

import Util
import Cudd.Imperative
import Synthesis.Interface

-- v   == type of single bit variables bound by exists statements 
-- c   == type of single bit variables bound by let statements
data AST v c leaf = T
                  | F
                  | Not      (AST v c leaf)
                  | And      (AST v c leaf) (AST v c leaf)
                  | Or       (AST v c leaf) (AST v c leaf)
                  | Imp      (AST v c leaf) (AST v c leaf)
                  | XNor     (AST v c leaf) (AST v c leaf)
                  | Conj     [AST v c leaf]
                  | Disj     [AST v c leaf]
                  | Case     [(AST v c leaf, AST v c leaf)]
                  | Exists   (v -> AST v c leaf)
                  | QuantLit v
                  | Let      (AST v c leaf) (c -> AST v c leaf)
                  | LetLit   c
                  | Leaf     leaf
                  deriving (Functor)

bind :: (l -> AST v c m) -> AST v c l -> AST v c m
bind f T             = T
bind f F             = F
bind f (Not x)       = Not  (bind f x)
bind f (And x y)     = And  (bind f x) (bind f y)
bind f (Or x y)      = Or   (bind f x) (bind f y)
bind f (Imp x y)     = Imp  (bind f x) (bind f y)
bind f (XNor x y)    = XNor (bind f x) (bind f y)
bind f (Conj xs)     = Conj $ map (bind f) xs
bind f (Disj xs)     = Disj $ map (bind f) xs
bind f (Case cases)  = Case $ fmap (bimap (bind f) (bind f)) cases
bind f (Exists func) = Exists $ \v -> bind f (func v)
bind f (QuantLit x)  = QuantLit x
bind f (Let x func)  = Let (bind f x) (\c -> bind f (func c))
bind f (LetLit x)    = LetLit x
bind f (Leaf x)      = f x

instance Monad (AST v c) where
    return = Leaf
    (>>=)  = flip bind

instance Applicative (AST v c) where
    pure    = Leaf 
    f <*> v = f `ap` v

-- f   == type of anonymous free variables 
-- var == type of free variable identifiers
data Leaf f var   = EqVar     (Either f var) var
                  | EqConst   (Either f var) Int
                  | ConstLeaf Bool
                  deriving (Foldable, Functor, Traversable)

eqVar   x y = Leaf $ EqVar x y
eqConst x y = Leaf $ EqConst x y

type TheAST v c f var = AST v c (Leaf f var)

prettyPrint :: Show v => AST Doc Doc (Leaf Doc v) -> Doc
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
        prettyPrint'' (Leaf (EqVar (Right x) y))   = text (pack (show x)) <+> text "==" <+> text (pack (show y))
        prettyPrint'' (Leaf (EqVar (Left x) y))    = x <+> text "==" <+> text (pack (show y))
        prettyPrint'' (Leaf (EqConst (Right x) c)) = text (pack (show x)) <+> text "==" <+> text (pack (show c))
        prettyPrint'' (Leaf (EqConst (Left x) c))  = x <+> text "==" <+> text (pack (show c))
        prettyPrint'' (Leaf (ConstLeaf val))       = if val == True then text (pack "True") else text (pack "False")
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
ccase m x = do
    ref $ bzero m
    ref $ bzero m
    go (bzero m) (bzero m) x
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

compile :: STDdManager s u -> VarOps pdb v s u -> AST  (DDNode s u) (DDNode s u) (Leaf [DDNode s u] (v, Maybe String)) -> StateT pdb (ST s) (DDNode s u)
compile m VarOps{..} = compile' where
    binOp func m x y = do
        x <- compile' x
        y <- compile' y
        res <- lift $ func m x y 
        lift $ deref m x
        lift $ deref m y
        return res

    compile' T             = do
        lift $ ref $ bone m
        return $ bone m
    compile' F             = do
        lift $ ref $ bzero m
        return $ bzero m
    compile' (Not x)       = liftM bnot $ compile' x
    compile' (And x y)     = binOp band m x y
    compile' (Or x y)      = binOp bor m x y
    compile' (XNor x y)    = binOp bxnor m x y
    compile' (Imp x y)     = binOp bimp m x y
        where
        bimp m x y = bor m (bnot x) y
    compile' (Conj es)     = do
        es <- mapM compile' es
        lift $ conj m es
    compile' (Disj es)     = do
        es <- mapM compile' es
        lift $ disj m es
    compile' (Case cs)     = do
        cs <- mapM func cs 
        lift $ ccase m cs
        where
        func (x, y) = do
            x <- compile' x
            y <- compile' y
            return (x, y)
    compile' (Leaf (EqVar x y))   = do
        x <- either return (uncurry getVar) x
        y <- uncurry getVar y
        lift $ xeqy m x y
    compile' (Leaf (EqConst x c)) = do
        x <- either return (uncurry getVar) x
        lift $ computeCube m x $ bitsToBoolArrBe (length x) c
    compile' (Leaf (ConstLeaf True))  = compile' T
    compile' (Leaf (ConstLeaf False)) = compile' F
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

