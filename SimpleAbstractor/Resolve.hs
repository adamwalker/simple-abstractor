module SimpleAbstractor.Resolve (
    resolve,
    doDecls,
    SymTab
    ) where

import qualified Data.Map as Map
import Data.Map (Map)
import Data.Traversable
import Control.Arrow
import Data.List
import Control.Monad as M
import Data.EitherR
import Control.Error.Util

import SimpleAbstractor.AST
import SimpleAbstractor.Analysis
import SimpleAbstractor.Predicate

type SymbolType = Either (VarAbsType, Section, Int) Int
type SymTab     = Map String SymbolType

--Resolving symbols in the AST
resolve :: (Traversable t) => SymTab -> t (Either (String, Slice) Int) -> Either String (t (Either VarInfo Int))
resolve = traverse . func

func :: SymTab -> Either (String, Slice) Int -> Either String (Either VarInfo Int)
func mp lit = case lit of 
    Left (str, slice) -> case Map.lookup str mp of
        Nothing                     -> Left  $ "Var doesn't exist: " ++ str
        Just (Left (typ, sect, sz)) -> Right $ Left $ VarInfo str typ sz sect slice
        Just (Right c)              -> Right $ Right $ getBits slice c
    Right x -> Right $ Right x

--Constructing the symbol table
addSymbol :: (Ord a) => Map a b -> (a, b) -> Either a (Map a b)
addSymbol mp (key, val) =  case Map.lookup key mp of
    Nothing -> Right $ Map.insert key val mp
    Just _  -> Left key

addSymbols :: (Ord a) => Map a b -> [(a, b)] -> Either a (Map a b)
addSymbols im = foldM addSymbol im 

type TypeMap = Map String Int

doType :: (String, Type) -> (SymTab, TypeMap) -> Either String (SymTab, TypeMap)
doType (name, typ) (st, tm) = do
    st' <- addSymbols st $ map (second Right) $ doTypeconsts typ
    tm' <- addSymbol  tm (name, doTypeSz typ)
    return (st', tm')

doTypes :: [(String, Type)] -> Either String (SymTab, TypeMap)
doTypes types = foldM (flip doType) (Map.empty, Map.empty) types

doDecl :: TypeMap -> Section -> Decl -> Either String [(String, SymbolType)]
doDecl _ sect (Decl vars atyp (Right vtype)) = return $ concatMap go' vars
    where
    go' var = (var, Left (atyp, sect, sz)) : map (second Right) consts
    sz      = doTypeSz vtype
    consts  = doTypeconsts vtype
doDecl typMap sect (Decl vars atyp (Left typ)) = do
    size <- note ("Type doesnt exist: " ++ typ) $ Map.lookup typ typMap
    return $ map (\var -> (var, Left (atyp, sect, size))) vars

doDecls :: [(String, Type)] -> [Decl] -> [Decl] -> [Decl] -> Either String SymTab
doDecls td sd ld od = fmapL ("Variable already exists: " ++) $ do
    (st, tm) <- doTypes td
    sd       <- M.mapM (doDecl tm StateSection)   sd
    ld       <- M.mapM (doDecl tm LabelSection)   ld 
    od       <- M.mapM (doDecl tm OutcomeSection) od
    addSymbols st $ concat [concat sd, concat ld, concat od]

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

