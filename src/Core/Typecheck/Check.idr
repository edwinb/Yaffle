module Core.Typecheck.Check

-- Typechecker for raw TT terms

import Core.Context
import Core.Env
import Core.Error
import Core.Evaluate
import Core.Evaluate.Convert
import Core.Syntax.Raw
import Core.TT
import Core.TT.Universes

parameters {auto c : Ref Ctxt Defs}
  topType : FC -> Term vars
  topType fc = TType fc (MN "top" 0)

  export
  inferPrim : FC -> Constant -> (Term vars, Term vars)
  inferPrim fc (I i)    = (PrimVal fc (I i),    PrimVal fc $ IntType)
  inferPrim fc (I8 i)   = (PrimVal fc (I8 i),   PrimVal fc $ Int8Type)
  inferPrim fc (I16 i)  = (PrimVal fc (I16 i),  PrimVal fc $ Int16Type)
  inferPrim fc (I32 i)  = (PrimVal fc (I32 i),  PrimVal fc $ Int32Type)
  inferPrim fc (I64 i)  = (PrimVal fc (I64 i),  PrimVal fc $ Int64Type)
  inferPrim fc (BI i)   = (PrimVal fc (BI i),   PrimVal fc $ IntegerType)
  inferPrim fc (B8 i)   = (PrimVal fc (B8 i),   PrimVal fc $ Bits8Type)
  inferPrim fc (B16 i)  = (PrimVal fc (B16 i),  PrimVal fc $ Bits16Type)
  inferPrim fc (B32 i)  = (PrimVal fc (B32 i),  PrimVal fc $ Bits32Type)
  inferPrim fc (B64 i)  = (PrimVal fc (B64 i),  PrimVal fc $ Bits64Type)
  inferPrim fc (Str s)  = (PrimVal fc (Str s),  PrimVal fc $ StringType)
  inferPrim fc (Ch c)   = (PrimVal fc (Ch c),   PrimVal fc $ CharType)
  inferPrim fc (Db d)   = (PrimVal fc (Db d),   PrimVal fc $ DoubleType)
  inferPrim fc WorldVal = (PrimVal fc WorldVal, PrimVal fc $ WorldType)
  inferPrim fc t  = (PrimVal fc t, topType fc)

  -- Check the raw term has the given type
  export
  check : {vars : _} ->
          RigCount -> Env Term vars -> RawC -> Term vars -> Core (Term vars)

  -- Infer a type for a raw term. Return a pair of the checked term and
  -- its type
  export
  infer : {vars : _} ->
          RigCount -> Env Term vars -> RawI -> Core (Term vars, Term vars)
  infer rig env (RAnnot fc tm ty)
      = do (ty', tyty) <- infer erased env ty
           lvl <- uniVar fc
           chkConvert fc env tyty (TType fc lvl)
           tm' <- check rig env tm ty'
           pure (tm', ty')
  infer rigc env (RVar fc n)
      = case defined n env of
             Just (MkIsDefined rigb p) =>
                do rigSafe rigb rigc
                   let binder = getBinder p env
                   let bty = binderType binder
                   pure (Local fc (Just (isLet binder)) _ p, bty)
             Nothing =>
                do defs <- get Ctxt
                   [(pname, i, def)] <- lookupCtxtName n (gamma defs)
                        | ns => ambiguousName fc n (map fst ns)
                   rigSafe (multiplicity def) rigc
                   let nt = fromMaybe Func (defNameType $ definition def)
                   pure (Ref fc nt (Resolved i), embed (type def))
    where
      rigSafe : RigCount -> RigCount -> Core ()
      rigSafe lhs rhs = when (lhs < rhs)
                             (throw (LinearMisuse fc n lhs rhs))

  infer rig env (RApp fc fn arg)
      = do (fn', fnty) <- infer rig env fn
           case !(nf env fnty) of
             VBind fc x (Pi _ rigf _ ty) sc =>
               do let checkRig = rigMult rigf rig
                  arg' <- check checkRig env arg !(quote env ty)
                  argnf <- nf env arg'
                  pure (App fc fn' arg', !(quote env !(sc argnf)))
             t => throw (NotFunctionType fc !(get Ctxt) env !(quote env t))
  infer rig env (RLet fc rigl n val ty sc)
      = do ty' <- check erased env ty (topType fc)
           val' <- check (rigMult rig rigl) env val ty'
           let env' = Let fc rigl val' ty' :: env
           (sc', scty) <- infer rig env' sc
           let letTy = Bind fc n (Let fc rigl val' ty') scty
           pure (Bind fc n (Let fc rigl val' ty') sc', letTy)
  infer rig env (RPi fc rigp n argty retty)
      = do su <- uniVar fc
           tu <- uniVar fc
           ty' <- check erased env argty (TType fc su)
           let env' = Pi fc rigp Explicit ty' :: env
           retty' <- check erased env' retty (TType fc tu)
           maxu <- uniVar fc
           addConstraint (ULE fc su fc maxu)
           addConstraint (ULE fc tu fc maxu)
           pure (Bind fc n (Pi fc rigp Explicit ty') retty', TType fc maxu)
  infer _ _ (RPrimVal fc c) = pure (inferPrim fc c)
  infer _ _ (RType fc)
      = do u <- uniVar fc
           t <- uniVar fc
           addConstraint (ULT fc u fc t)
           pure (TType fc u, TType fc t)

  checkCon : {bound, vars : _} ->
             Int ->
             Bounds bound ->
             FC -> RigCount ->
             Env Term vars ->
             Env Term (bound ++ vars) ->
             Name -> List Name ->
             (conApp : Term (bound ++ vars)) ->
             (conTy : Value vars) ->
             (rhs : RawC) ->
             (scr : Term (bound ++ vars)) ->
             (scrTy : Term (bound ++ vars)) ->
             (rhsTy : Term (bound ++ vars)) ->
             Core (CaseScope (bound ++ vars))
  checkCon i bs fc rig valenv env cname [] app ty rhs scr scrTy rhsTy
      = do rhsExp <- replace env !(nf env scr) app
                                 !(nf env rhsTy)
           rhs' <- check rig env rhs rhsExp
           pure (RHS rhs')

  checkCon i bs fc rig valenv env cname (arg :: args) app (VBind _ x (Pi _ rigp p aty) sc) rhs scr scrTy rhsTy
      = do -- Extend the environment with the constructor argument name
           argty <- quote valenv aty
           let varty = refsToLocals bs argty
           let env' = PVar fc rig Explicit varty :: env
           -- Check the rest of the scope; apply the current constructor
           -- application to the new variable, and substitute the variable into
           -- the constructor type
           let argn = MN "carg" i
           casesc <- checkCon (i + 1) (Add arg argn bs) fc rig
                              valenv env' cname args
                              (App fc (weaken app) (Local fc (Just False) _ First))
                              !(sc (VApp fc Bound argn [<] (pure Nothing)))
                              rhs (weaken scr) (weaken scrTy) (weaken rhsTy)
           pure (Arg arg casesc)
  -- I wouldn't expect to see this happen since we've done an arity check, but
  -- here for completeness
  checkCon _ bs fc _ _ _ cname _ _ _ _ _ _ _
      = throw (GenericMsg fc ("Can't match on " ++ show cname))

  -- Check a case alternative.
  -- We need to replace any occurrence of 'scr' in 'rhsTy' with whatever
  -- the typechecked lhs turns out to be before checking the rhs.
  checkAlt : {vars : _} ->
             FC -> RigCount -> Env Term vars ->
             (scr : Term vars) ->
             (scrTy : Term vars) ->
             (rhsTy : Term vars) ->
             RawCaseAlt -> Core (CaseAlt vars)
  checkAlt fc rig env scr scrTy rhsTy (RConCase n args rhs)
      = do defs <- get Ctxt
           [(cname, i, def)] <- lookupCtxtName n (gamma defs)
                | ns => ambiguousName fc n (map fst ns)
           let DCon _ tag arity = definition def
                | _ => throw (GenericMsg fc ("Can't match on " ++ show cname))
           let True = arity == length args
                | _ => throw (GenericMsg fc (show cname ++ " has arity " ++ show arity))
           let conty = embed (type def)
           concase <- checkCon 0 None fc rig env env cname args
                               (Ref fc (DataCon tag arity) cname)
                               !(nf env conty)
                               rhs scr scrTy rhsTy
           pure (ConCase n tag concase)
  checkAlt fc rig env scr scrTy rhsTy (RConstCase c rhs)
      = do c' <- check rig env (RInf fc (RPrimVal fc c)) scrTy
           rhsExp <- replace env !(nf env scr) c' !(nf env rhsTy)
           rhs' <- check rig env rhs rhsExp
           pure (ConstCase c rhs')
  checkAlt fc rig env scr scrTy rhsTy (RDefaultCase rhs)
      = do rhs' <- check rig env rhs rhsTy
           pure (DefaultCase rhs')

  -- Declared above as
  -- check : {vars : _} ->
  --         RigCount -> Env Term vars -> RawC -> Term vars -> Core (Term vars)
  check rig env (RInf fc tm) exp
      = do (tm', ty') <- infer rig env tm
           chkConvert fc env ty' exp
           pure tm'
  check {vars} rig env (RLam fc n scope) ty
      = do tnf <- nf env ty
           case !(quote env tnf) of
                Bind _ x (Pi _ rigp p aty) rty =>
                    do let env' = Lam fc rigp p aty :: env
                       sc' <- check rig env' scope rty
                       pure (Bind fc n (Lam fc rigp p aty)
                                  (renameTop n sc'))
                _ => throw (NotFunctionType fc !(get Ctxt) env ty)
  check rig env (RCase fc sc alts) exp
      = do (sc', scTy') <- infer rig env sc
           alts <- traverse (checkAlt fc rig env sc' scTy' exp) alts
           pure (Case fc sc' scTy' alts)
