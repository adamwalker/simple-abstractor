module AdamAbstractor.Resolve (
    resolve,
    doDecls,
    SymTab
    ) where

import qualified Data.Map as Map
import Data.Map (Map)
import Data.Traversable
import Control.Arrow
import Data.List
import Control.Monad
import Data.EitherR

import AdamAbstractor.AST
import AdamAbstractor.Analysis
import AdamAbstractor.Predicate

type SymTab = Map String (Either (VarAbsType, Section, Int) Int)

resolve :: (Traversable t) => SymTab -> t (Either (String, Slice) Int) -> Either String (t (Either VarInfo Int))
resolve = traverse . func

func :: SymTab -> Either (String, Slice) Int -> Either String (Either VarInfo Int)
func mp lit = case lit of 
    Left (str, slice) -> case Map.lookup str mp of
        Nothing                     -> Left  $ "Var doesn't exist: " ++ str
        Just (Left (typ, sect, sz)) -> Right $ Left $ VarInfo str typ sz sect slice
        Just (Right c)              -> Right $ Right $ getBits slice c
    Right x -> Right $ Right x

constructSymTab :: (Ord a) => [(a, b)] -> Either a (Map a b)
constructSymTab = foldM func (Map.empty) 
    where
    func mp (key, val) = case Map.lookup key mp of
        Nothing -> Right $ Map.insert key val mp
        Just _  -> Left key

doDecls :: [Decl] -> [Decl] -> [Decl] -> Either String SymTab
doDecls sd ld od = fmapL ("Variable already exists: " ++) $ constructSymTab $ concat [concatMap (go StateSection) sd, concatMap (go LabelSection) ld, concatMap (go OutcomeSection) od]
    where
    go sect (Decl vars atyp vtype) = concatMap go' vars
        where
        go' var = (var, Left (atyp, sect, sz)) : map (second Right) consts
        sz      = doTypeSz vtype
        consts  = doTypeconsts vtype

--Logarithm to base 2. Equivalent to floor(log2(x))
log2 :: Int -> Int
log2 0 = 0
log2 1 = 0
log2 n 
    | n>1 = 1 + log2 (n `div` 2)
    | otherwise = error "log2: negative argument"

typeSize :: Int -> Int
typeSize 0 = error "Enum with no items"
typeSize 1 = error "Enum with one item"
typeSize i = 1 + log2 (i - 1)

doTypeSz BoolType      = 1
doTypeSz (IntType n)   = n
doTypeSz (EnumType es) = typeSize $ length es

doTypeconsts BoolType      = []
doTypeconsts (IntType n)   = []
doTypeconsts (EnumType es) = zip es [0..]

