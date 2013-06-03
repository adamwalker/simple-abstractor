module AdamAbstractor.Resolve (
    resolve,
    doDecls
    ) where

import qualified Data.Map as Map
import Data.Map (Map)
import Data.Traversable

import AdamAbstractor.AST
import AdamAbstractor.Analysis
import AdamAbstractor.Predicate

resolve :: (Traversable t) => Map String (VarAbsType, Section) -> t (Either String Int) -> Either String (t (Either VarInfo Int))
resolve = traverse . func

func :: Map String (VarAbsType, Section) -> Either String Int -> Either String (Either VarInfo Int)
func mp lit = case lit of 
    Left str -> case Map.lookup str mp of
        Nothing          -> Left  $ "Var doesn't exist: " ++ str
        Just (typ, sect) -> Right $ Left $ VarInfo str typ sect
    Right x -> Right $ Right x

doDecls :: [Decl] -> [Decl] -> [Decl] -> Map String (VarAbsType, Section)
doDecls sd ld od = Map.unions [Map.fromList $ concatMap (go StateSection) sd, Map.fromList $ concatMap (go LabelSection) ld, Map.fromList $ concatMap (go OutcomeSection) od]
    where
    go sect (Decl vars typ) = map go' vars
        where
        go' var = (var, (typ, sect))
