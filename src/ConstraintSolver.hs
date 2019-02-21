{-# LANGUAGE CPP                 #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE BangPatterns        #-}

module ConstraintSolver (plugin) where

import Data.Functor.Identity
import Module     (mkModuleName, Module)
import OccName    (mkTcOcc, mkVarOcc, mkDataOcc)
import Plugins    (Plugin (..), defaultPlugin)
import TcType
import Bag        (bagToList)
import TcEvidence
import TcEnv      (tcLookupIdMaybe, getInLocalScope)
import TcMType    (newEvVars)
import TcPluginM
import TcRnTypes
import TcRnMonad
import Class
import CoreUtils
import MkCore
import TyCon
import Type
import CoreSyn
import Unify
import Data.Maybe
import Control.Monad
import qualified Debug.Trace as DT
import qualified Data.List as L
import FastString
import Unique
import Type
import Id
import Var
import CoreSyn
import Outputable
import TyCoRep
import TyCon
import DataCon
import MkCore
import MkId
import CoreUtils
import TysWiredIn
import BasicTypes
import NameEnv
import NameSet
import Coercion
import UniqFM
import TcSimplify
import TcSMonad  (runTcS)
import Name      (Name)
import Data.List
import Control.Monad
import Data.Bifunctor
import Data.Either
import Data.Hashable

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

lookupHasFunTyCon :: TcPluginM (Class, TyCon, Module)
lookupHasFunTyCon = do
    Found _ md   <- findImportedModule hasFunModule Nothing
    hasFunTcNm <- lookupOrig md (mkTcOcc "HasFunction")
    cls <- tcLookupClass hasFunTcNm
    prxBinding <- lookupOrig md (mkTcOcc "Proxy")    
    prx <- tcLookupTyCon prxBinding
    pure (cls, prx, md)
  where
    hasFunModule = mkModuleName "HasFunction"

findClassConstraint :: Class -> Ct -> Maybe (Ct, (Type, Type))
findClassConstraint cls ct = do
    (cls', [lab, sig]) <- getClassPredTys_maybe (ctPred ct)
    guard (cls' == cls)
    return (ct, (lab, sig))

hasFunSolver :: (Class, TyCon, Module) -> [Ct] -> [Ct] -> [Ct] ->
                 TcPluginM TcPluginResult
hasFunSolver (hasFunCls, prx, md) givens deriveds wanteds = do
  Found _ md'   <- findImportedModule (mkModuleName "Main") Nothing  
  funBs <- mapM (\(_, (lab, _)) -> case isStrLitTy lab of
           Just funName -> do
             let funStr = unpackFS funName
             funBinding <- lookupOrig md' (mkVarOcc funStr)
             maybe (Left (Just funName)) (Right . (funName, )) <$> (unsafeTcPluginTcM $ do 
                                                                       f <- getInLocalScope
                                                                       case (f funBinding) of
                                                                         True -> tcLookupIdMaybe funBinding
                                                                         False -> pure Nothing
                                                                   )
           Nothing -> pure (Left Nothing)
               ) our_wanteds
  (solved, newWanteds) <- result funBs >>= tcPluginResult md
  return $! TcPluginOk solved newWanteds
  where
    our_wanteds = mapMaybe (findClassConstraint hasFunCls) wanteds
    result funBs = mapM (\(x, r) -> wrap x [] hasFunCls prx $ solve r) $
                     zipWith inside our_wanteds funBs
    inside (ct, (t1, t2)) fb = (ct, (t1, t2, fb))
    thd ((x, y, z), ct) = (z, ct)
    
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
             LabWrongKind ct t    -> error "Panic: impossible case"
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
evidenceOf ps evbs = pprTraceIt "ps & evs" (ps, evbs) `seq` map lookupDc ps
  where lookupDc p = maybe (Left p) Right (L.find (\gv -> pprTraceIt "LkpDC: " (exprType (Var (eb_lhs gv)), p)
                                                    `seq` exprType (Var (eb_lhs gv)) `eqType` p) evbs)

wrap :: Ct -> [EvBind] -> Class -> TyCon ->
        (Type, Type, Either (Maybe FastString) (FastString, CoreExpr)) ->
        TcPluginM CtSolution 
wrap ct _ _ _ (lab, _, Left Nothing) = pure (LabWrongKind ct lab)
wrap ct _ _ _ (_, _, Left (Just bn)) = pure (BindingNotFound ct bn)
wrap ct givens cls prx (lab, reqSig, Right (bn, e)) = do
  case tcSubstMapMaybe reqSig (exprType e) of
    Nothing -> pure (Unmatched ct bn reqSig (exprType e))
    Just tcv -> do
      let ps = dicts tcv
      evBinds <- solveDicts ps
      case evidenceOf ps evBinds of
        evs -> do
          let evExpr = EvExpr (appDc tcv e evs)
          case pprTraceIt "Types: " (substDict tcv ct, (noForall (substTy tcv givenSig)), (noForall (substTy tcv reqSig)))
               `seq` eqType (noForall (substTy tcv givenSig)) (noForall (substTy tcv reqSig)) of
            True -> pure (CtSolved (substDict tcv ct) evExpr)
            False -> pure (Unmatched ct bn reqSig (exprType e))
        -- (ps, _) -> pure (NeedMoreCt ct bn ps)          
  where
    substDict tcv ct@CDictCan {} =
      ct { cc_ev = (cc_ev ct) { ctev_pred = substTy tcv (ctev_pred (cc_ev ct)) } }
    tyCon = classTyCon cls    
    dc = tyConSingleDataCon tyCon
    (tyVars, givenSig) = splitForAllTys (exprType e)
    (funArgs, _) = splitFunTys givenSig
    dicts tcv = map (substTy tcv) (takeWhile isPredTy funArgs)
    mappedTys (TCvSubst _ tcEnv _coEnv) = case traverse (lookupUFM tcEnv) tyVars of
                                            Just vs -> vs
                                            Nothing -> error "Panic: var not found @concTys"
    sigWithPx = mkFunTy (mkTyConApp prx [lab])
    appDc tcv e evs = mkCoreConApps dc [ Type lab
                                       , Type (substTy tcv (noForall reqSig))
                                       , lams (mkTyConApp prx [lab] : lefts evs)
                                         (\(_ : vs) -> letsEvBind (rights evs) $
                                                      mkCoreApps e (map Type (mappedTys tcv) ++
                                                                    map evidence (zipEv evs vs)
                                                                   )
                                         )
                                       ]
    evidence (Left (pt, v)) = Var v
    evidence (Right ev) = Var . eb_lhs $ ev

    zipEv (Left pt : ls ) (v : vs) = Left (pt, v) : zipEv ls vs
    zipEv (Right ev : ls)  vs      = Right ev : zipEv ls vs
    zipEv []              []       = []
        
solve :: (Type, Type, Either (Maybe FastString) (FastString, Var)) -> (Type, Type, Either (Maybe FastString) (FastString, CoreExpr))
solve = (thd . fmap . fmap) Var
  where thd f (x, y, z) = (x, y, f z)

lam :: Type -> (Var -> CoreExpr) -> CoreExpr
lam ty gen = Lam v $ gen v
  where v = newVar ty

lams :: [Type] -> ([Var] -> CoreExpr) -> CoreExpr
lams tys gen = mkCoreLams vs $ gen vs
  where vs = map newVar tys

newVar :: Type -> Var
newVar ty = mkSysLocal (mkFastString "x") (mkBuiltinUnique i) ty
  where i = hash (showSDocUnsafe (ppr ty))

unifyType :: Type -> Type -> Coercion
unifyType t1 t2 = coType
  where coType = mkUnivCo (PluginProv "hasfunction-plugin") Nominal t1
                          (substTy (tcSubstMap t1 t2) (noForall t2))

tcSubstMap :: Type -> Type -> TCvSubst
tcSubstMap t1 = fromMaybe emptyTCvSubst . tcSubstMapMaybe t1
        
tcSubstMapMaybe :: Type -> Type -> Maybe TCvSubst
tcSubstMapMaybe t1 t2 = pprTraceIt "tcSubstMapMaybe" ((noForall t2), (noForall t1), subVars) `seq` subVars
  where subVars = tcUnifyTyWithTFs True (noForall t2) (noForall t1)

unifyTypeCt :: Type -> Type -> TcPluginM Ct
unifyTypeCt t1 t2 = do
  loc <- unsafeTcPluginTcM $ getCtLocM (GivenOrigin UnkSkol) Nothing
  mkNonCanonical <$> (newWanted loc (coercionType (unifyType t1 t2)))

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

letsA :: Applicative f => [CoreExpr] -> ([Id] -> f CoreExpr) -> f CoreExpr
letsA es gen = mkLets (zipWith NonRec vs es) <$> gen vs
  where vs = map (newVar . exprType) es

letsEvBind :: [EvBind] -> CoreExpr -> CoreExpr
letsEvBind es exp = mkLets [Rec $ map (\evB -> (eb_lhs evB, getEvBExpr $ eb_rhs evB)) es] exp
  where
#if __GLASGOW_HASKELL__ >= 806
    getEvBExpr (EvExpr e) = e
#elif __GLASGOW_HASKELL__ >= 804
    getEvBExpr (EvId i)   = Var i
#endif                                
    getEvBExpr e          = error "Panic: nonExpr in EvBind. TODO: Replace with ghc panic"

