module AdamAbstractor.Resolve (
    resolve,
    doDecls
    ) where

import qualified Data.Map as Map
import Data.Map (Map)
import Data.Traversable
import Control.Arrow

import AdamAbstractor.AST
import AdamAbstractor.Analysis
import AdamAbstractor.Predicate

resolve :: (Traversable t) => Map String (Either (VarAbsType, Section, Int) Int) -> t (Either String Int) -> Either String (t (Either VarInfo Int))
resolve = traverse . func

func :: Map String (Either (VarAbsType, Section, Int) Int) -> Either String Int -> Either String (Either VarInfo Int)
func mp lit = case lit of 
    Left str -> case Map.lookup str mp of
        Nothing                     -> Left  $ "Var doesn't exist: " ++ str
        Just (Left (typ, sect, sz)) -> Right $ Left $ VarInfo str typ sz sect 
        Just (Right c)              -> Right $ Right c
    Right x -> Right $ Right x

doDecls :: [Decl] -> [Decl] -> [Decl] -> Map String (Either (VarAbsType, Section, Int) Int)
doDecls sd ld od = Map.unions [Map.fromList $ concatMap (go StateSection) sd, Map.fromList $ concatMap (go LabelSection) ld, Map.fromList $ concatMap (go OutcomeSection) od]
    where
    go sect (Decl vars atyp vtype) = concatMap go' vars
        where
        go' var = (var, Left (atyp, sect, sz)) : map (second Right) consts
        sz      = doTypeSz vtype
        consts  = doTypeconsts vtype

doTypeSz BoolType      = 1
doTypeSz (IntType n)   = n
doTypeSz (EnumType es) = error "resolve.hs"

doTypeconsts BoolType      = []
doTypeconsts (IntType n)   = []
doTypeconsts (EnumType es) = error "resolve.hs"

