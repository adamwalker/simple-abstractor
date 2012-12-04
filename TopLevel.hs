{-# LANGUAGE RecordWildCards, PolymorphicComponents #-}
module TopLevel where

import System.Environment
import Control.Monad.ST.Lazy
import Control.Monad.State
import Data.Functor
import qualified Data.Map as Map
import Data.Map (Map)

import Text.Parsec hiding ((<|>))

import CuddST
import CuddExplicitDeref

import Analysis
import AST
import Backend
import Parser
import Predicate
import Resolve
import qualified Refine

doMain = do
    [fname] <- getArgs
    fres <- readFile fname
    let res = runST $ doIt fres
    print res

doIt :: String -> ST s (Either String Bool)
doIt fres = do
    m <- cuddInitSTDefaults
    case funcy m fres of 
        Left  err        -> return $ Left err
        Right abstractor -> liftM Right $ Refine.absRefineLoop m (hack m abstractor) ts (error "No abstractor state")
            where
            ts    = Refine.TheorySolver ucs ucsl quant
            ucs   = const Nothing
            ucsl  = const $ const Nothing
            quant _ _ _ _ _ c d e _ = return $ Refine.EQuantRet c d e (bone m) undefined

data Abstractor s u = Abstractor {
    pred :: forall pdb. VarOps pdb Pred Var s u -> EqPred -> DDNode s u   -> StateT pdb (ST s) (DDNode s u),
    pass :: forall pdb. VarOps pdb Pred Var s u -> String -> [DDNode s u] -> StateT pdb (ST s) (DDNode s u),
    goal :: forall pdb. VarOps pdb Pred Var s u -> StateT pdb (ST s) (DDNode s u),
    init :: forall pdb. VarOps pdb Pred Var s u -> StateT pdb (ST s) (DDNode s u)
}

data TheState sp lp s u = TheState {
    ip   :: Map sp (Refine.VarInfo s u),
    iv   :: Map String [Refine.VarInfo s u],
    sp   :: Map sp (Refine.VarInfo s u),
    sv   :: Map String [Refine.VarInfo s u],
    lp   :: Map lp (Refine.VarInfo s u, Refine.VarInfo s u),
    lv   :: Map String ([Refine.VarInfo s u], Refine.VarInfo s u),
    op   :: Map sp (DDNode s u),
    ov   :: Map String [DDNode s u],
    offs :: Int 
}

hack :: STDdManager s u -> Abstractor s u -> Refine.Abstractor s u o EqPred EqPred
hack m Abstractor{..} = Refine.Abstractor{..}
    where
    goalAbs   _ ipm ivm spm svm offs _               = do
        let st = TheState ipm ivm spm svm (error "TopLevel: hack 0") (error "TopLevel: hack 1") undefined undefined offs
        (x, TheState{..}) <- runStateT (goal ops) st
        return $ Refine.GoalAbsRet sp sv offs x (error "TopLevel: hack 2")
    initAbs   _ offs _                               = do
        let st = TheState Map.empty Map.empty Map.empty Map.empty (error "TopLevel: hack 3") (error "TopLevel: hack 4") undefined undefined offs
        (x, TheState{..}) <- runStateT (init ops) st
        return $ Refine.InitAbsRet sp sv x offs (error "TopLevel: hack 5")
    updateAbs _ ipm ivm spm svm lpm lvm offs _ ps vs = do
        let st = TheState ipm ivm spm svm lpm lvm Map.empty Map.empty offs
        (x, TheState{..}) <- flip runStateT st $ do
            x <- mapM (uncurry $ pred ops) ps
            y <- mapM (uncurry $ pass ops) vs
            return $ x ++ y
        cb <- nodesToCube m $ Map.elems op ++ concat (Map.elems ov)
        x <- mapM (flip (bexists m) cb) x
        return $ Refine.UpdateAbsRet sp sv lp lv offs x (error "TopLevel: hack 6")
    ops = VarOps {..}
        where
        getPred (pred, StateSection) = do
            theMap <- gets sp
            case Map.lookup pred theMap of
                Just var -> return $ fst var
                Nothing -> do
                    initMap <- gets ip
                    case Map.lookup pred initMap of
                        Just var -> do
                            modify $ \st -> st {sp = Map.insert pred var (sp st)}
                            return $ fst var
                        Nothing -> do
                            st <- get
                            newVar <- lift $ bvar m $ offs st
                            modify $ \st -> st {sp = Map.insert pred (newVar, offs st) (sp st)}
                            modify $ \st -> st {offs = offs st + 1}
                            return newVar
        getPred (pred, LabelSection) = do
            theMap <- gets lp
            case Map.lookup pred theMap of
                Just var -> return $ fst $ fst var
                Nothing -> do
                    st <- get
                    newVar <- lift $ bvar m $ offs st
                    newEn  <- lift $ bvar m $ offs st + 1
                    modify $ \st -> st {lp = Map.insert pred ((newVar, offs st), (newEn, offs st + 1)) (lp st)}
                    modify $ \st -> st {offs = offs st + 2}
                    return $ newVar
        getPred (pred, OutcomeSection) = do
             theMap <- gets op
             case Map.lookup pred theMap of
                 Just var -> return var
                 Nothing  -> do
                     st <- get
                     newVar <- lift $ bvar m $ offs st
                     modify $ \st -> st {op = Map.insert pred newVar (op st), offs = offs st + 2}
                     return newVar
        getVar  (nm,  StateSection, sz) = do
            theMap <- gets sv
            case Map.lookup nm theMap of
                Just var -> return $ map fst var
                Nothing -> do
                    initMap <- gets iv
                    case Map.lookup nm initMap of
                        Just var -> do
                            modify $ \st -> st {sv = Map.insert nm var (sv st)}
                            return $ map fst var
                        Nothing -> do
                            st <- get
                            let inds = take sz $ iterate (+1) (offs st)
                            newVar <- lift $ sequence $ map (bvar m) inds
                            modify $ \st -> st {sv = Map.insert nm (zip newVar inds) (sv st)}
                            modify $ \st -> st {offs = offs st + sz}
                            return newVar
        getVar  (nm,  LabelSection, sz) = do
            theMap <- gets lv
            case Map.lookup nm theMap of
                Just var -> return $ map fst $ fst var
                Nothing -> do
                    st <- get
                    let inds = take sz $ iterate (+1) (offs st)
                    newVar <- lift $ sequence $ map (bvar m) inds
                    newEn  <- lift $ bvar m $ offs st + sz
                    modify $ \st -> st {lv = Map.insert nm ((zip newVar inds), (newEn, offs st + sz)) (lv st)}
                    modify $ \st -> st {offs = offs st + sz + 1}
                    return newVar
        getVar  (nm, OutcomeSection, sz) = do
            theMap <- gets ov
            case Map.lookup nm theMap of 
                Just var -> return var
                Nothing -> do
                    st <- get
                    let inds = take sz $ iterate (+1) (offs st)
                    newVar <- lift $ sequence $ map (bvar m) inds
                    modify $ \st -> st {ov = Map.insert nm newVar (ov st)}
                    modify $ \st -> st {offs = offs st + sz}
                    return newVar
        withTmp func = do
            ind <- gets offs
            var <- lift $ bvar m ind
            modify $ \st -> st {offs = offs st + 1}
            func var

funcy :: STDdManager s u -> String -> Either String (Abstractor s u)
funcy m contents = do
    (Spec sdecls ldecls odecls init goal trans) <- either (Left . show) Right $ parse top "" contents
    let theMap                                  =  doDecls sdecls ldecls odecls
    tr                                          <- resolve theMap trans
    ir                                          <- resolveBin theMap init
    gr                                          <- resolveBin theMap goal
    func m tr ir gr

func :: STDdManager s u -> CtrlExpr String (Either VarInfo Int) -> BinExpr (Either VarInfo Int) -> BinExpr (Either VarInfo Int) -> Either String (Abstractor s u)
func m trans initt goall = func <$> abstract trans
    where
    func Return{..} = Abstractor {..}
        where
        pred ops (Predicate.EqVar v1 v2) = compile m ops . abs2Tsl where Abs2Return {..} = abs2Ret v1 v2
        pred ops (Predicate.EqConst v c) = error "func: not implemented"
        pass ops var                     = compile m ops . passTSL where PassThroughReturn {..} = either (error "func") id $ passRet var
        goal ops                         = compile m ops tsl where (tsl, _) = binExpToTSL goall
        init ops                         = compile m ops tsl where (tsl, _) = binExpToTSL initt


