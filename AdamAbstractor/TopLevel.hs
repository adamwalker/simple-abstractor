{-# LANGUAGE RecordWildCards, PolymorphicComponents, ScopedTypeVariables #-}
module AdamAbstractor.TopLevel where

import Control.Monad.ST
import Control.Monad.State
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Applicative

import Text.Parsec hiding ((<|>))
import qualified Text.Parsec.Token as T
import Text.Parsec.Language
import Control.Error
import Safe
import Control.Arrow
import Data.List

import CuddST
import CuddExplicitDeref

import AdamAbstractor.Analysis
import AdamAbstractor.AST hiding (Pred)
import AdamAbstractor.Backend as Backend
import AdamAbstractor.Parser
import AdamAbstractor.Predicate as Predicate
import AdamAbstractor.Resolve
import AdamAbstractor.CompileHelpers

import qualified RefineCommon
import qualified TermiteGame as Game
import Interface

import qualified EqSMTSimple


stdDef = emptyDef {T.reservedNames = reservedNames 
                  ,T.reservedOpNames = reservedOps
                  ,T.identStart = letter <|> char '_'
                  ,T.identLetter = alphaNum <|> char '_'
                  ,T.commentStart = "/*"
                  ,T.commentEnd = "*/"
                  ,T.commentLine = "//"
                  }

fromLeft = either id (error "fromLeft")

spToLeonid :: SymTab -> EqPred -> EqSMTSimple.Pred 
spToLeonid mp (Predicate.EqVar x sx y sy) = EqSMTSimple.EqPred (x, szx, slx) (y, szy, sly)
    where
    (_, _, szx) = fromLeft $ fromJustNote "theory solver" $ Map.lookup x mp
    slx = maybe (0, szx-1) id sx
    (_, _, szy) = fromLeft $ fromJustNote "theory solver" $ Map.lookup y mp
    sly = maybe (0, szy-1) id sy
spToLeonid mp (Predicate.EqConst x sx c)  = EqSMTSimple.EqConst (x, szx, slx) c
    where
    (_, _, szx) = fromLeft $ fromJustNote "theory solver" $ Map.lookup x mp
    slx = maybe (0, szx-1) id sx

lpToLeonid :: SymTab -> LabEqPred -> EqSMTSimple.Pred 
lpToLeonid mp (LabEqVar x sx y sy _) = EqSMTSimple.EqPred (x, szx, slx) (y, szy, sly)
    where
    (_, _, szx) = fromLeft $ fromJustNote "theory solver" $ Map.lookup x mp
    slx = maybe (0, szx-1) id sx
    (_, _, szy) = fromLeft $ fromJustNote "theory solver" $ Map.lookup y mp
    sly = maybe (0, szy-1) id sy
lpToLeonid mp (LabEqConst x sx c)  = EqSMTSimple.EqConst (x, szx, slx) c
    where
    (_, _, szx) = fromLeft $ fromJustNote "theory solver" $ Map.lookup x mp
    slx = maybe (0, szx-1) id sx

leonidToSP :: SymTab -> EqSMTSimple.Pred -> EqPred
leonidToSP st (EqSMTSimple.EqPred (x, _, (sx1, sx2)) (y, _, (sy1, sy2))) = constructVarPred x slx' y sly' 
    where
    (_, StateSection, szx) = fromLeft $ fromJustNote "theory solver" $ Map.lookup x st
    (_, StateSection, szy) = fromLeft $ fromJustNote "theory solver" $ Map.lookup y st
    slx'                   = if sx2 - sx1 == szx then Nothing else Just (sx1, sx2)
    sly'                   = if sy2 - sy1 == szy then Nothing else Just (sy1, sy2)
leonidToSP st (EqSMTSimple.EqConst (x, _, (s1, s2)) c) = if sect==StateSection then Predicate.EqConst x sl' c else error "leonidToSP"
    where
    (_, sect, szx) = fromLeft $ fromJustNote "theory solver" $ Map.lookup x st
    sl'            = if s2 - s1 == szx then Nothing else Just (s1, s2)

compileDNF :: STDdManager s u -> VarOps pdb (BAVar (VarType EqPred) lp) s u -> [[(EqPred, Bool)]] -> StateT pdb (ST s) (DDNode s u)
compileDNF m ops dnf = Backend.compile m ops $ Backend.Disj $ map (Backend.Conj . map func) dnf
    where
    func (pred, val) = Backend.EqConst (Right ((StateVar (Pred pred) 1), undefined)) (boolToInt val)
    boolToInt False = 0
    boolToInt True  = 1

ts :: SymTab -> STDdManager s u -> RefineCommon.TheorySolver s u (VarType EqPred) (VarType LabEqPred) String
ts st m = RefineCommon.TheorySolver ucs ucsl quant gvl
    where
    ucs  sp    = fmap fst $ ucsl sp []
    ucsl sp lp = fmap gunc $ EqSMTSimple.unsatCore $ map (spToLeonid st *** head) (mapMaybe func sp) ++ map (lpToLeonid st *** head) (mapMaybe func lp)
        where
        func (Enum _, _) = Nothing
        func (Pred p, a) = Just (p, a)
        sPreds = mapMaybe func sp
        lPreds = mapMaybe func lp
        theMap = Map.fromList $ map (((spToLeonid st) &&& Left) . fst) sPreds ++ map (((lpToLeonid st) &&& Right) . fst) lPreds
        gunc :: [(EqSMTSimple.Pred, Bool)] -> ([(VarType EqPred, [Bool])], [(VarType LabEqPred, [Bool])])
        gunc leonids = (lefts x, rights x)
            where
            x    = map func leonids
            func (pred, val) = 
                case fromJustNote "asdf" $ flip Map.lookup theMap pred of
                    Left  x -> Left  (Pred x, [val])
                    Right x -> Right (Pred x, [val])
    --TODO: investigate why having this return non-true causes stupid predicates to be introduced and makes synthesis slow
    quant preds ops = if (length p < 2) then return (bone m) else compileDNF m ops $ map (map (first $ leonidToSP st)) $ EqSMTSimple.eQuant lvars p
        where
        p = map (lpToLeonid st *** head) $ mapMaybe func preds
        func (Enum _, _) = Nothing
        func (Pred p, a) = Just (p, a)
        lvars = nub $ concatMap (fmap funcy . gvl . fst) preds
        --TODO: is below optimal?
        funcy var = (var, sz, (0, sz-1))
            where
            (_, _, sz) = fromLeft $ fromJustNote "asdf" $ Map.lookup var st
    gvl (Pred (Predicate.LabEqVar x _ _ _ False)) = [x]
    gvl (Pred (Predicate.LabEqVar x _ y _ True))  = [x, y]
    gvl (Pred (Predicate.LabEqConst x _ _))       = [x]
    gvl (Enum x)                                  = [x]

data Decls = Decls {
    stateDecls   :: [Decl],
    labelDecls   :: [Decl],
    outcomeDecls :: [Decl]
}

lexer = T.makeTokenParser (stdDef {T.reservedNames = T.reservedNames stdDef ++ ["STATE", "LABEL", "OUTCOME", "INIT", "GOAL", "TRANS", "FAIR", "CONT", "LABELCONSTRAINTS"]})

data Rels a = Rels {
    init         :: BinExpr a,
    goal         :: [BinExpr a],
    fair         :: [BinExpr a],
    cont         :: BinExpr a,
    slRel        :: BinExpr a,
    trans        :: CtrlExpr String a
}

data Spec = Spec {
    decls :: Decls,
    rels  :: Rels (Either (String, Slice) Int)
}

T.TokenParser {..} = lexer

parseDecls = Decls
    <$  reserved "STATE"
    <*> sepEndBy (decl lexer) semi
    <*  reserved "LABEL"
    <*> sepEndBy (decl lexer) semi
    <*  reserved "OUTCOME"
    <*> sepEndBy (decl lexer) semi

parseRels = Rels
    <$  reserved "INIT"
    <*> binExpr lexer
    <*  reserved "GOAL"
    <*> sepEndBy (binExpr lexer) semi
    <*  reserved "FAIR"
    <*> sepEndBy (binExpr lexer) semi
    <*  reserved "CONT"
    <*> binExpr lexer
    <*  reserved "LABELCONSTRAINTS"
    <*> binExpr lexer
    <*  reserved "TRANS"
    <*> (AdamAbstractor.AST.Conj <$> sepEndBy (ctrlExpr lexer) semi)

spec = Spec <$> parseDecls <*> parseRels

top = whiteSpace *> spec <* eof

makeAbs :: STDdManager s u -> String -> String -> Either String (Game.Abstractor s u (VarType EqPred) (VarType LabEqPred) (), RefineCommon.TheorySolver s u (VarType EqPred) (VarType LabEqPred) String)
makeAbs m fres ivars = do
    (Spec Decls{..} Rels{..}) <- fmapL show $ parse top "" fres
    theMap                    <- doDecls stateDecls labelDecls outcomeDecls
    resolved                  <- Rels <$> resolve theMap init 
                                      <*> mapM (resolve theMap) goal 
                                      <*> mapM (resolve theMap) fair 
                                      <*> resolve theMap cont 
                                      <*> resolve theMap slRel
                                      <*> resolve theMap trans
    res1 <- theAbs m resolved (map (ivFunc theMap) (words ivars))
    return (res1, ts theMap m)

theAbs :: STDdManager s u -> Rels ValType -> [(VarType EqPred, Int, Maybe String)] -> Either String (Game.Abstractor s u (VarType EqPred) (VarType LabEqPred) ())
theAbs m Rels{..} ivars = func <$> updateAbs
    where
    func (R ua)          = Game.Abstractor {..}
        where
        fairAbs ops                 = lift $ mapM (compileBin m ops) fair
        goalAbs ops                 = lift $ mapM (compileBin m ops) goal
        initAbs ops                 = lift $ compileBin m ops init
        contAbs ops                 = lift $ compileBin m ops cont
        stateLabelConstraintAbs ops = lift $ compileBin m ops slRel
        updateAbs x y               = lift $ ua x y
        initialState                = ()
        initialVars                 = ivars
    updateAbs                   =  compileUpdate trans m

ivFunc :: SymTab -> String -> (VarType EqPred, Int, Maybe String)
ivFunc theMap var = case Map.lookup var theMap of
    Nothing                             -> error "ivFunc: var doesnt exist"
    Just (Right _)                      -> error "ivfunc: not a var"
    Just (Left (_, StateSection, size)) -> (Enum var, size, Nothing)
    Just (Left (_, _, _))               -> error "ivfunc: not a state var"
