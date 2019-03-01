{-# LANGUAGE CPP                 #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE BangPatterns        #-}

module ConstraintSolver (plugin, splitOnMany) where

import Module     (mkModuleName, Module, getModule, moduleEnvElts, moduleEnvToList, filterModuleEnv, moduleEnvKeys, moduleName)
import NameCache  (nsNames)
import GHC        (getModuleInfo)
import OccName    (mkTcOcc, mkVarOcc, mkMethodOcc, mkDefaultMethodOcc)
import Plugins    (Plugin (..), defaultPlugin)
import TcType
import Bag        (bagToList, unitBag)
import TcEvidence
import TcEnv      (tcLookupIdMaybe, getInLocalScope)
import TcPluginM
import TcRnTypes
import TcRnMonad  (foldlM, getCtLocM, captureConstraints, readMutVar)
import qualified TcRnMonad  as TcRn (getTopEnv, getGblEnv)
import Class
import CoreUtils
import MkCore
import TyCon
import Type
import CoreSyn
import Unify
import Data.Maybe
import Control.Monad
import qualified Data.List as L
import FastString
import Unique
import Id
import Var
import Outputable
import UniqFM
import TcSimplify
import TcSMonad  (runTcS)
import Data.List
import Data.Bifunctor
import Data.Hashable
import Data.Either
import DataCon
import TysWiredIn
import Control.Monad.IO.Class (MonadIO (..))
import HscTypes
import UniqDFM (udfmToList)
import Name (Name, getOccString, occNameString, occEnvElts, nameOccName)
import Avail
import HsExpr (LHsExpr, GRHS (..), GRHSs (..), HsMatchContext (..), Match (..), MatchGroup (..), MatchGroupTc (..))
import HsBinds (LHsBinds, HsLocalBindsLR (..), HsBindLR (..))
import HsExtension (GhcTc, GhcRn, noExt)
import RdrName
import RnEnv
import HsUtils (nlHsVar, mkLHsWrap)
import TcExpr (tcMonoExpr)
import TcHsSyn (zonkTopLExpr)
import SrcLoc (noLoc, noSrcSpan)
import IfaceEnv (newGlobalBinder)
import qualified IfaceEnv as IF (lookupOrig)
import NameSet (emptyNameSet)
import BasicTypes (Origin (..), LexicalFixity (..))

plugin :: Plugin
plugin = defaultPlugin {
  tcPlugin = const (Just installHasFun)
  }

installHasFun :: TcPlugin
installHasFun =
  TcPlugin { tcPluginInit  = lookupHasFunTyCon
           , tcPluginSolve = hasFunSolver
           , tcPluginStop  = \_ -> pure ()
           }

lookupHasFunTyCon :: TcPluginM (Class, (TyCon, TyCon), Module)
lookupHasFunTyCon = do
    Found _ md   <- findImportedModule hasFunModule Nothing
    Found _ pmd  <- findImportedModule proxyModule Nothing    
    hasFunTcNm <- lookupOrig md (mkTcOcc "HasFunction")
    cls <- tcLookupClass hasFunTcNm
    prxBinding <- lookupOrig pmd (mkTcOcc "Proxy")    
    prx <- tcLookupTyCon prxBinding
    let sym = typeSymbolKindCon     
    pure (cls, (prx, sym), md)
  where
    hasFunModule    = mkModuleName "HasFunction"
    proxyModule     = mkModuleName "Data.Proxy"

findClassConstraint :: Class -> Ct -> Maybe (Ct, (Type, Type))
findClassConstraint cls ct = do
    (cls', [lab, sig]) <- getClassPredTys_maybe (ctPred ct)
    guard (cls' == cls)
    return (ct, (lab, sig))

hasFunSolver :: (Class, (TyCon, TyCon), Module) -> [Ct] -> [Ct] -> [Ct] ->
                 TcPluginM TcPluginResult
hasFunSolver (hasFunCls, prx, md) _ _ wanteds = do
  funBs <- mapM (\(_, (lab, _)) -> case isStrLitTy lab of
           Just funName -> do
             let funStr = unpackFS funName
             maybe (Left (Just funName)) (Right . (funName, )) <$> lookupInScope funStr             
           Nothing -> pure (Left Nothing)
               ) our_wanteds
  (solved, newWanteds) <- result funBs >>= tcPluginResult md
  return $! TcPluginOk solved newWanteds
  where
    our_wanteds = mapMaybe (findClassConstraint hasFunCls) wanteds
    result funBs = mapM (\(x, r) -> wrap x [] hasFunCls prx $ solve r) $
                     zipWith inside our_wanteds funBs
    inside (ct, (t1, t2)) fb = (ct, (t1, t2, fb))
    
tcPluginResult :: Module -> [CtSolution] -> TcPluginM ([(EvTerm, Ct)], [Ct])
tcPluginResult md =
  foldlM (\(solved, newWanteds) sol -> case sol of
             CtSolved ct ev -> pure (((ev, ct) : solved), newWanteds)
             BindingNotFound ct s -> do
               notFound <- bindingNotFound md s
               pure ((undefined, ct) : solved, notFound : newWanteds)
             NeedMoreCt ct s ps   -> do
               wantedCt <- missingConstraints md s ps 
               pure ((undefined, ct) : solved, wantedCt : newWanteds)
             Unmatched ct s tl tr -> do
               wantedCt <- wrongType md s tl tr
               pure ((undefined, ct) : solved, wantedCt : newWanteds)
             LabWrongKind _ct _t    -> error "Panic: impossible case"
         ) ([], [])

bindingNotFound :: Module -> FastString -> TcPluginM Ct
bindingNotFound md s = do
  loc <- unsafeTcPluginTcM $ getCtLocM (GivenOrigin UnkSkol) Nothing
  notFoundBinding <- lookupOrig md (mkTcOcc "BindingNotFound")    
  notFoundErr <- tcLookupTyCon notFoundBinding
  mkNonCanonical <$> newWanted loc (mkTyConApp notFoundErr [mkStrLitTy s])

missingConstraints :: Module -> FastString -> [PredType] -> TcPluginM Ct
missingConstraints md s ps = do
  loc <- unsafeTcPluginTcM $ getCtLocM (GivenOrigin UnkSkol) Nothing
  missingCtxBinding <- lookupOrig md (mkTcOcc "MissingConstraints")    
  missingCtxErr <- tcLookupTyCon missingCtxBinding
  mkNonCanonical <$> newWanted loc (mkTyConApp missingCtxErr [head ps, mkStrLitTy s])

wrongType :: Module -> FastString -> Type -> Type -> TcPluginM Ct
wrongType md s tl tr = do
  loc <- unsafeTcPluginTcM $ getCtLocM (GivenOrigin UnkSkol) Nothing
  notFoundBinding <- lookupOrig md (mkTcOcc "CannotMatchType")    
  notFoundErr <- tcLookupTyCon notFoundBinding
  mkNonCanonical <$> newWanted loc (mkTyConApp notFoundErr [mkStrLitTy s, tl, tr])

data CtSolution = CtSolved Ct EvTerm
                | BindingNotFound Ct FastString
                | NeedMoreCt Ct FastString [PredType]
                | Unmatched Ct FastString Type Type
                | LabWrongKind Ct Type                

solveDicts :: [PredType] -> TcPluginM [EvBind]
solveDicts ps = do
  let nubbedPs = nubBy eqType ps
  evVars <- mapM newEvVar nubbedPs
  loc <- unsafeTcPluginTcM $ getCtLocM (GivenOrigin UnkSkol) Nothing      
  let new_wanteds = map (uncurry3 unifyItemToCt) (zipWith3 (,,) (repeat loc) nubbedPs evVars)
      wCs         = mkSimpleWC new_wanteds
  (_, evBinds') <- unsafeTcPluginTcM $ second evBindMapBinds <$> runTcS (solveWanteds wCs)
  let evBinds = bagToList evBinds'
  pure evBinds

  where uncurry3 f (x, y, z) = f x y z    

-- returns evidence of a given pred type or the same predtype
-- in the order of input pred types .
evidenceOf :: [PredType] -> [EvBind] -> [Either PredType EvBind]
evidenceOf ps evbs = map lookupDc ps
  where lookupDc p = maybe (Left p) Right (L.find (\gv -> exprType (Var (eb_lhs gv)) `eqType` p) evbs)

wrap :: Ct -> [EvBind] -> Class -> (TyCon, TyCon) ->
        (Type, Type, Either (Maybe FastString) (FastString, CoreExpr)) ->
        TcPluginM CtSolution 
wrap ct _ _ _ (lab, _, Left Nothing) = pure (LabWrongKind ct lab)
wrap ct _ _ _ (_, _, Left (Just bn)) = pure (BindingNotFound ct bn)
wrap ct _ cls prx (lab, reqSig, Right (bn, e)) = do
  case tcSubstMapMaybe reqSig (exprType e) of
    Nothing -> pure (Unmatched ct bn reqSig (exprType e))
    Just tcv -> do
      let ps = dicts tcv
      evBinds <- solveDicts ps
      case evidenceOf ps evBinds of
        evs | (all isRight evs) -> do
          evExpr <- unsafeTcPluginTcM $ evidenceExpr cls prx tyVars reqSig lab tcv e evs evBinds
          case eqType (noForall (substTy tcv givenSig)) (noForall (substTy tcv reqSig)) of
            True -> pure (CtSolved (substDict tcv ct) evExpr)
            False -> pure (Unmatched ct bn reqSig (exprType e))
        evs -> pure (NeedMoreCt ct bn (lefts evs))
  where
    substDict tcv ctd@CDictCan {} =
      ctd { cc_ev = (cc_ev ctd) { ctev_pred = substTy tcv (ctev_pred (cc_ev ctd)) } }
    substDict _ ctd = ctd
    (tyVars, givenSig) = splitForAllTys (exprType e)
    (funArgs, _) = splitFunTys givenSig
    dicts tcv = map (substTy tcv) (takeWhile isPredTy funArgs)
    
evidenceExpr :: Class -> (TyCon, TyCon) -> [TyVar] -> Type -> Type -> TCvSubst -> CoreExpr -> [Either Type EvBind] -> [EvBind] -> TcM EvTerm
evidenceExpr cls (prx, sym) tyVars reqSig lab tcv expr evs evBinds = do
  pure appDc
  
  where
    lamExpr = lams (labPx : lefts evs)
              (\(_ : vs) -> letsEvBind evBinds $
                           mkCoreApps expr (map Type (mappedTys tcv) ++
                                            map evidence (zipEv evs vs)
                                           )
              )
    
    appDc = evDFunAppWithCon dc [lab, (substTy tcv (noForall reqSig))] lamExpr
    labPx = mkTyConApp prx [mkTyConTy sym, lab]
    mappedTys (TCvSubst _ tcEnv _coEnv) = case traverse (lookupUFM tcEnv) tyVars of
                                            Just vs -> vs
                                            Nothing -> error "Panic: var not found @mappedTys"

    evidence (Left (_, v)) = Var v
    evidence (Right ev) = Var . eb_lhs $ ev

    dc = tyConSingleDataCon tyCon
    tyCon = classTyCon cls    

    zipEv (Left pt : ls ) (v : vs) = Left (pt, v) : zipEv ls vs
    zipEv (Right ev : ls)  vs      = Right ev : zipEv ls vs
    zipEv []              []       = []
    zipEv _               _        = error "Panic: invariant failed @zipEv"

evDFunAppWithCon :: DataCon -> [Type] -> CoreExpr -> EvTerm
evDFunAppWithCon dc tys v =
#if __GLASGOW_HASKELL__ >= 806
  evDFunApp (dataConWorkId dc) tys [v]
#else
  EvDFunApp (dataConWorkId dc) tys [] -- (map EvId vs)
#endif  

solve :: (Type, Type, Either (Maybe FastString) (FastString, Var)) -> (Type, Type, Either (Maybe FastString) (FastString, CoreExpr))
solve = (thd . fmap . fmap) Var
  where thd f (x, y, z) = (x, y, f z)

lams :: [Type] -> ([Var] -> CoreExpr) -> CoreExpr
lams tys gen = mkCoreLams vs $ gen vs
  where vs = map newVar tys

newVar :: Type -> Var
newVar ty = mkSysLocal (mkFastString "x") (mkBuiltinUnique i) ty
  where i = hash (showSDocUnsafe (ppr ty))

tcSubstMapMaybe :: Type -> Type -> Maybe TCvSubst
tcSubstMapMaybe t1 t2 = subVars
  where subVars = tcMatchTyKi (noForall t2) (noForall t1)

noForall :: Type -> Type
noForall = splitDicts . snd . splitForAllTys
  where splitDicts a = 
          let (funArgs, res) = splitFunTys a
          in  mkFunTys (dropWhile isPredTy funArgs) res

unifyItemToCt :: CtLoc
                -> PredType
                -> EvVar
                -> CtEvidence
unifyItemToCt loc pred_type evVar =
  CtWanted pred_type (EvVarDest evVar) WDeriv loc

letsEvBind :: [EvBind] -> CoreExpr -> CoreExpr
letsEvBind es = mkLets [Rec $ map (\evB -> (eb_lhs evB, getEvBExpr $ eb_rhs evB)) es]
  where
#if __GLASGOW_HASKELL__ >= 806
    getEvBExpr (EvExpr e) = e
#elif __GLASGOW_HASKELL__ >= 804
    getEvBExpr (EvId i)   = Var i
#endif                                
    getEvBExpr _          = error "Panic: nonExpr in EvBind. TODO: Replace with ghc panic"

lookupInScope :: String -> TcPluginM (Maybe Id)
lookupInScope str = do
  mn <- case splitOnMany '.' str of
    [x] -> unsafeTcPluginTcM $ lookupOccRn_maybe (mkVarUnqual (fsLit x))
    xs  -> unsafeTcPluginTcM $ lookupOccRn_maybe (mkRdrQual (mkModName (init xs)) (mkVarOcc (last xs)))
  case mn of
    Just n  -> unsafeTcPluginTcM $ tcLookupIdMaybe n
    Nothing -> pure Nothing

  where mkModName = mkModuleName . intercalate "."

splitOnMany :: Char -> String -> [String]
splitOnMany delim s =
  let (spl, cur) = foldl' (\(spl, cur) a -> case a == delim of
                              True -> (reverse cur : spl, [])
                              False -> (spl, a : cur)
                          ) ([], []) s
  in reverse (reverse cur : spl)
  











