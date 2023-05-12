module TTImp.ProcessDef

import Core.Case.Builder
import Core.Check.Erase
import Core.Context
import Core.Context.Log
import Core.Core
import Core.Coverage
import Core.Env
import Core.Hash
import Core.Check.Linear
import Core.Metadata
import Core.Evaluate
import Core.Termination
import Core.Transform
import Core.Unify.State

import TTImp.BindImplicits
import TTImp.Elab
import TTImp.Elab.Check
import TTImp.Elab.Utils
import TTImp.Impossible
-- import TTImp.PartialEval -- Skipping this for now, needs complete redesign
import TTImp.TTImp
import TTImp.TTImp.Functor
import TTImp.ProcessType
import TTImp.Unelab
import TTImp.WithClause

import Data.Either
import Data.List
import Libraries.Data.NameMap
import Data.Maybe
import Data.SnocList
import Data.String
import Libraries.Text.PrettyPrint.Prettyprinter

%default covering

mismatch : {auto c : Ref Ctxt Defs} ->
           {vars : _} ->
           (Glued vars, Glued vars) -> Core Bool

mismatchNF : {auto c : Ref Ctxt Defs} ->
             {vars : _} ->
             NF vars -> NF vars -> Core Bool
mismatchNF (VTCon _ xn _ xargs) (VTCon _ yn _ yargs)
    = if xn /= yn
         then pure True
         else do xargsNF <- traverseSnocList spineArg xargs
                 yargsNF <- traverseSnocList spineArg yargs
                 anyMSnoc mismatch (zip xargsNF yargsNF)
mismatchNF (VDCon _ _ xt _ xargs) (VDCon _ _ yt _ yargs)
    = if xt /= yt
         then pure True
         else do xargsNF <- traverseSnocList spineArg xargs
                 yargsNF <- traverseSnocList spineArg yargs
                 anyMSnoc mismatch (zip xargsNF yargsNF)
mismatchNF (VPrimVal _ xc) (VPrimVal _ yc) = pure (xc /= yc)
mismatchNF (VDelayed _ _ x) (VDelayed _ _ y)
    = mismatchNF !(expand x) !(expand y)
mismatchNF (VDelay _ _ _ x) (VDelay _ _ _ y)
    = mismatchNF !(expand x) !(expand y)

-- NPrimVal is apart from NDCon, NTCon, NBind, and NType
mismatchNF (VPrimVal _ _) (VDCon _ _ _ _ _) = pure True
mismatchNF (VDCon _ _ _ _ _) (VPrimVal _ _) = pure True
mismatchNF (VPrimVal _ _) (VBind _ _ _ _) = pure True
mismatchNF (VBind _ _ _ _) (VPrimVal _ _) = pure True
mismatchNF (VPrimVal _ _) (VTCon _ _ _ _) = pure True
mismatchNF (VTCon _ _ _ _) (VPrimVal _ _) = pure True
mismatchNF (VPrimVal _ _) (VType _ _) = pure True
mismatchNF (VType _ _) (VPrimVal _ _) = pure True

-- NTCon is apart from NBind, and NType
mismatchNF (VTCon _ _ _ _) (VBind _ _ _ _) = pure True
mismatchNF (VBind _ _ _ _) (VTCon _ _ _ _) = pure True
mismatchNF (VTCon _ _ _ _) (VType _ _) = pure True
mismatchNF (VType _ _) (VTCon _ _ _ _) = pure True

-- NBind is apart from NType
mismatchNF (VBind _ _ _ _) (VType _ _) = pure True
mismatchNF (VType _ _) (VBind _ _ _ _) = pure True

mismatchNF _ _ = pure False

mismatch (x, y) = mismatchNF !(expand x) !(expand y)

-- If the terms have the same type constructor at the head, and one of
-- the argument positions has different constructors at its head, then this
-- is an impossible case, so return True
export
impossibleOK : {auto c : Ref Ctxt Defs} ->
               {vars : _} ->
               NF vars -> NF vars -> Core Bool
impossibleOK (VTCon _ xn xa xargs) (VTCon _ yn ya yargs)
    = if xn /= yn
         then pure True
         else do xargsNF <- traverseSnocList spineArg xargs
                 yargsNF <- traverseSnocList spineArg yargs
                 anyMSnoc mismatch (zip xargsNF yargsNF)
-- If it's a data constructor, any mismatch will do
impossibleOK (VDCon _ _ xt _ xargs) (VDCon _ _ yt _ yargs)
    = if xt /= yt
         then pure True
         else do xargsNF <- traverseSnocList spineArg xargs
                 yargsNF <- traverseSnocList spineArg yargs
                 anyMSnoc mismatch (zip xargsNF yargsNF)
impossibleOK (VPrimVal _ x) (VPrimVal _ y) = pure (x /= y)

-- VPrimVal is apart from VDCon, VTCon, VBind, and VType
impossibleOK (VPrimVal _ _) (VDCon _ _ _ _ _) = pure True
impossibleOK (VDCon _ _ _ _ _) (VPrimVal _ _) = pure True
impossibleOK (VPrimVal _ _) (VBind _ _ _ _) = pure True
impossibleOK (VBind _ _ _ _) (VPrimVal _ _) = pure True
impossibleOK (VPrimVal _ _) (VTCon _ _ _ _) = pure True
impossibleOK (VTCon _ _ _ _) (VPrimVal _ _) = pure True
impossibleOK (VPrimVal _ _) (VType _ _) = pure True
impossibleOK (VType _ _) (VPrimVal _ _) = pure True

-- VTCon is apart from VBind, and VType
impossibleOK (VTCon _ _ _ _) (VBind _ _ _ _) = pure True
impossibleOK (VBind _ _ _ _) (VTCon _ _ _ _) = pure True
impossibleOK (VTCon _ _ _ _) (VType _ _) = pure True
impossibleOK (VType _ _) (VTCon _ _ _ _) = pure True

-- VBind is apart from VType
impossibleOK (VBind _ _ _ _) (VType _ _) = pure True
impossibleOK (VType _ _) (VBind _ _ _ _) = pure True

impossibleOK x y = pure False

export
impossibleErrOK : {auto c : Ref Ctxt Defs} ->
                  Error -> Core Bool
impossibleErrOK (CantConvert fc defs env l r)
    = do defs' <- get Ctxt
         put Ctxt defs
         res <- impossibleOK !(expand !(nf env l))
                             !(expand !(nf env r))
         put Ctxt defs'
         pure res
impossibleErrOK (CantSolveEq fc defs env l r)
    = do defs' <- get Ctxt
         put Ctxt defs
         res <- impossibleOK !(expand !(nf env l))
                             !(expand !(nf env r))
         put Ctxt defs'
         pure res
impossibleErrOK (BadDotPattern _ _ ErasedArg _ _) = pure True
impossibleErrOK (CyclicMeta _ _ _ _) = pure True
impossibleErrOK (AllFailed errs)
    = anyM impossibleErrOK (map snd errs)
impossibleErrOK (WhenUnifying _ _ _ _ _ err)
    = impossibleErrOK err
impossibleErrOK _ = pure False

-- If it's a clause we've generated, see if the error is recoverable. That
-- is, if we have a concrete thing, and we're expecting the same concrete
-- thing, or a function of something, then we might have a match.
export
recoverable : {auto c : Ref Ctxt Defs} ->
              {vars : _} ->
              NF vars -> NF vars -> Core Bool
-- Unlike the above, any mismatch will do

-- TYPE CONSTRUCTORS
recoverable (VTCon _ xn xa xargs) (VTCon _ yn ya yargs)
    = if xn /= yn
         then pure False
         else do xargsNF <- traverseSnocList spineArg xargs
                 yargsNF <- traverseSnocList spineArg yargs
                 pure $ not !(anyMSnoc mismatch (zip xargsNF yargsNF))
-- Type constructor vs. primitive type
recoverable (VTCon _ _ _ _) (VPrimVal _ _) = pure False
recoverable (VPrimVal _ _) (VTCon _ _ _ _) = pure False
-- Type constructor vs. type
recoverable (VTCon _ _ _ _) (VType _ _) = pure False
recoverable (VType _ _) (VTCon _ _ _ _) = pure False
-- Type constructor vs. binder
recoverable (VTCon _ _ _ _) (VBind _ _ _ _) = pure False
recoverable (VBind _ _ _ _) (VTCon _ _ _ _) = pure False

recoverable (VTCon _ _ _ _) _ = pure True
recoverable _ (VTCon _ _ _ _) = pure True

-- DATA CONSTRUCTORS
recoverable (VDCon _ _ xt _ xargs) (VDCon _ _ yt _ yargs)
    = if xt /= yt
         then pure False
         else do xargsNF <- traverseSnocList spineArg xargs
                 yargsNF <- traverseSnocList spineArg yargs
                 pure $ not !(anyMSnoc mismatch (zip xargsNF yargsNF))
-- Data constructor vs. primitive constant
recoverable (VDCon _ _ _ _ _) (VPrimVal _ _) = pure False
recoverable (VPrimVal _ _) (VDCon _ _ _ _ _) = pure False

recoverable (VDCon _ _ _ _ _) _ = pure True
recoverable _ (VDCon _ _ _ _ _) = pure True

-- FUNCTION CALLS
recoverable (VApp _ _ _ _ _) (VApp _ _ _ _ _)
    = pure True -- both functions; recoverable

-- PRIMITIVES
recoverable (VPrimVal _ x) (VPrimVal _ y) = pure (x == y)
-- primitive vs. binder
recoverable (VPrimVal _ _) (VBind _ _ _ _) = pure False
recoverable (VBind _ _ _ _) (VPrimVal _ _) = pure False

-- OTHERWISE: no
recoverable x y = pure False

export
recoverableErr : {auto c : Ref Ctxt Defs} ->
                 Error -> Core Bool
recoverableErr (CantConvert fc defs env l r)
  = do defs' <- get Ctxt
       put Ctxt defs
       ok <- recoverable !(expand !(nf env l))
                         !(expand !(nf env r))
       put Ctxt defs'
       pure ok

recoverableErr (CantSolveEq fc defs env l r)
  = do defs' <- get Ctxt
       put Ctxt defs
       ok <- recoverable !(expand !(nf env l))
                         !(expand !(nf env r))
       put Ctxt defs'
       pure ok
recoverableErr (BadDotPattern _ _ ErasedArg _ _) = pure True
recoverableErr (CyclicMeta _ _ _ _) = pure True
recoverableErr (AllFailed errs)
    = anyM recoverableErr (map snd errs)
recoverableErr (WhenUnifying _ _ _ _ _ err)
    = recoverableErr err
recoverableErr _ = pure False

-- Given a type checked LHS and its type, return the environment in which we
-- should check the RHS, the LHS and its type in that environment,
-- and a function which turns a checked RHS into a
-- pattern clause
-- The 'SubVars' proof contains a proof that refers to the *inner* environment,
-- so all the outer things are marked as 'DropCons'
extendEnv : {vars : _} ->
            Env Term vars -> SubVars inner vars ->
            NestedNames vars ->
            Term vars -> Term vars ->
            Core (vars' **
                    (SubVars inner vars',
                     Env Term vars', NestedNames vars',
                     Term vars', Term vars'))
extendEnv env p nest (Bind _ n (PVar fc c pi tmty) sc) (Bind _ n' (PVTy _ _ _) tysc) with (nameEq n n')
  extendEnv env p nest (Bind _ n (PVar fc c pi tmty) sc) (Bind _ n' (PVTy _ _ _) tysc) | Nothing
      = throw (InternalError "Can't happen: names don't match in pattern type")
  extendEnv env p nest (Bind _ n (PVar fc c pi tmty) sc) (Bind _ n (PVTy _ _ _) tysc) | (Just Refl)
      = extendEnv (env :< PVar fc c pi tmty) (DropCons p) (weaken nest) sc tysc
extendEnv env p nest (Bind _ n (PLet fc c tmval tmty) sc) (Bind _ n' (PLet _ _ _ _) tysc) with (nameEq n n')
  extendEnv env p nest (Bind _ n (PLet fc c tmval tmty) sc) (Bind _ n' (PLet _ _ _ _) tysc) | Nothing
      = throw (InternalError "Can't happen: names don't match in pattern type")
  -- PLet on the left becomes Let on the right, to give it computational force
  extendEnv env p nest (Bind _ n (PLet fc c tmval tmty) sc) (Bind _ n (PLet _ _ _ _) tysc) | (Just Refl)
      = extendEnv (env :< Let fc c tmval tmty) (DropCons p) (weaken nest) sc tysc
extendEnv env p nest tm ty
      = pure (_ ** (p, env, nest, tm, ty))

-- Find names which are applied to a function in a Rig1/Rig0 position,
-- so that we know how they should be bound on the right hand side of the
-- pattern.
-- 'bound' counts the number of variables locally bound; these are the
-- only ones we're checking linearity of (we may be shadowing names if this
-- is a local definition, so we need to leave the earlier ones alone)
findLinear : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             Bool -> Nat -> RigCount -> Term vars ->
             Core (List (Name, RigCount))
findLinear top bound rig (Bind fc n b sc)
    = findLinear top (S bound) rig sc
findLinear top bound rig (As fc _ _ p)
    = findLinear top bound rig p
findLinear top bound rig tm
    = case getFnArgsSpine tm of
           (Ref _ _ n, [<]) => pure []
           (Ref _ nt n, args)
              => do defs <- get Ctxt
                    Just nty <- lookupTyExact n (gamma defs)
                         | Nothing => pure []
                    logTerm "declare.def.lhs" 5 ("Type of " ++ show !(toFullNames n)) nty
                    findLinArg (accessible nt rig) args
           _ => pure []
    where
      accessible : NameType -> RigCount -> RigCount
      accessible Func r = if top then r else erased
      accessible _ r = r

      findLinArg : {vars : _} ->
                   RigCount -> SnocList (RigCount, Term vars) ->
                   Core (List (Name, RigCount))
      findLinArg rig (as :< (c, As fc UseLeft _ p))
          = findLinArg rig (as :< (c, p))
      findLinArg rig (as :< (c, As fc UseRight p _))
          = findLinArg rig (as :< (c, p))
      findLinArg rig (as :< (c, Local fc idx prf))
          = do let a = nameAt prf
               if idx < bound
                  then pure $ (a, rigMult c rig) :: !(findLinArg rig as)
                  else findLinArg rig as
      findLinArg rig (as :< (c, a))
           = pure $ !(findLinear False bound (rigMult c rig) a) ++
                    !(findLinArg rig as)
      findLinArg rig [<] = pure []

setLinear : List (Name, RigCount) -> Term vars -> Term vars
setLinear vs (Bind fc x b@(PVar _ _ _ _) sc)
    = case lookup x vs of
           Just c' => Bind fc x (setMultiplicity b c') (setLinear vs sc)
           _ => Bind fc x b (setLinear vs sc)
setLinear vs (Bind fc x b@(PVTy _ _ _) sc)
    = case lookup x vs of
           Just c' => Bind fc x (setMultiplicity b c') (setLinear vs sc)
           _ => Bind fc x b (setLinear vs sc)
setLinear vs tm = tm

-- Combining multiplicities on LHS:
-- Rig1 + Rig1/W not valid, since it means we have repeated use of name
-- Rig0 + RigW = RigW
-- Rig0 + Rig1 = Rig1
combineLinear : FC -> List (Name, RigCount) ->
                Core (List (Name, RigCount))
combineLinear loc [] = pure []
combineLinear loc ((n, count) :: cs)
    = case lookupAll n cs of
           [] => pure $ (n, count) :: !(combineLinear loc cs)
           counts => do count' <- combineAll count counts
                        pure $ (n, count') ::
                               !(combineLinear loc (filter notN cs))
  where
    notN : (Name, RigCount) -> Bool
    notN (n', _) = n /= n'

    lookupAll : Name -> List (Name, RigCount) -> List RigCount
    lookupAll n [] = []
    lookupAll n ((n', c) :: cs)
       = if n == n' then c :: lookupAll n cs else lookupAll n cs

    -- Those combine rules are obtuse enough that they are worth investigating
    combine : RigCount -> RigCount -> Core RigCount
    combine l r = if l |+| r == top && not (isErased $ l `glb` r) && (l `glb` r) /= top
                     then throw (LinearUsed loc 2 n)
                     -- if everything is fine, return the linearity that has the
                     -- highest bound
                     else pure (l `lub` r)

    combineAll : RigCount -> List RigCount -> Core RigCount
    combineAll c [] = pure c
    combineAll c (c' :: cs)
        = do newc <- combine c c'
             combineAll newc cs

export -- also used by Transforms
checkLHS : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           {auto m : Ref MD Metadata} ->
           {auto u : Ref UST UState} ->
           Bool -> -- in transform
           (mult : RigCount) ->
           Int -> List ElabOpt -> NestedNames vars -> Env Term vars ->
           FC -> RawImp ->
           Core (RawImp, -- checked LHS with implicits added
                 (vars' ** (SubVars vars vars',
                           Env Term vars', NestedNames vars',
                           Term vars', Term vars')))
checkLHS {vars} trans mult n opts nest env fc lhs_in
    = do defs <- get Ctxt
         logRaw "declare.def.lhs" 30 "Raw LHS: " lhs_in
         lhs_raw <- if trans
                       then pure lhs_in
                       else lhsInCurrentNS nest lhs_in
         logRaw "declare.def.lhs" 30 "Raw LHS in current NS: " lhs_raw

         autoimp <- isUnboundImplicits
         setUnboundImplicits True
         (_, lhs_bound) <- bindNames False lhs_raw
         setUnboundImplicits autoimp
         logRaw "declare.def.lhs" 30 "Raw LHS with implicits bound" lhs_bound

         lhs <- if trans
                   then pure lhs_bound
                   else implicitsAs n defs (cast vars) lhs_bound

         logC "declare.def.lhs" 5 $ do pure $ "Checking LHS of " ++ show !(getFullName (Resolved n))
-- todo: add Pretty RawImp instance
--         logC "declare.def.lhs" 5 $ do pure $ show $ indent {ann = ()} 2 $ pretty lhs
         log "declare.def.lhs" 10 $ show lhs
         logEnv "declare.def.lhs" 5 "In env" env
         let lhsMode = if trans
                          then InTransform
                          else InLHS mult
         (lhstm, lhstyg) <-
             wrapErrorC opts (InLHS fc !(getFullName (Resolved n))) $
                     elabTerm n lhsMode opts nest env
                                (IBindHere fc PATTERN lhs) Nothing
         logTerm "declare.def.lhs" 5 "Checked LHS term" lhstm
         lhsty <- quote env lhstyg

         let lhsenv = letToLam env
         -- we used to fully normalise the LHS, to make sure fromInteger
         -- patterns were allowed, but now they're fully normalised anyway
         -- so we only need to do the holes. If there's a lot of type level
         -- computation, this is a huge saving!
         lhstm <- normaliseLHS lhsenv lhstm
         lhsty <- normaliseHoles env lhsty
         linvars_in <- findLinear True 0 linear lhstm
         logTerm "declare.def.lhs" 10 "Checked LHS term after normalise" lhstm
         log "declare.def.lhs" 5 $ "Linearity of names in " ++ show n ++ ": " ++
                 show linvars_in

         linvars <- combineLinear fc linvars_in
         let lhstm_lin = setLinear linvars lhstm
         let lhsty_lin = setLinear linvars lhsty

         logTerm "declare.def.lhs" 3 "LHS term" lhstm_lin
         logTerm "declare.def.lhs" 5 "LHS type" lhsty_lin
         setHoleLHS (bindEnv fc env lhstm_lin)

         ext <- extendEnv env SubRefl nest lhstm_lin lhsty_lin
         pure (lhs, ext)

-- Return whether any of the pattern variables are in a trivially empty
-- type, where trivally empty means one of:
--  * No constructors
--  * Every constructor of the family has a return type which conflicts with
--    the given constructor's type
hasEmptyPat : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              Defs -> Env Term vars -> Term vars -> Core Bool
hasEmptyPat defs env (Bind fc x b sc)
   = pure $ !(isEmpty defs env !(expand !(nf env (binderType b))))
            || !(hasEmptyPat defs (env :< b) sc)
hasEmptyPat defs env _ = pure False

-- For checking with blocks as nested names
applyEnv : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           Env Term vars -> Name ->
           Core (Name, (Maybe Name, List (Var vars), FC -> NameType -> Term vars))
applyEnv env withname
    = do n' <- resolveName withname
         pure (withname, (Just withname, reverse (allVarsNoLet env),
                  \fc, nt => applyTo fc
                         (Ref fc nt (Resolved n')) env))

-- Check a pattern clause, returning the component of the 'Case' expression it
-- represents, or Nothing if it's an impossible clause
export
checkClause : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto m : Ref MD Metadata} ->
              {auto u : Ref UST UState} ->
              (mult : RigCount) -> (vis : Visibility) ->
              (totreq : TotalReq) -> (hashit : Bool) ->
              Int -> List ElabOpt -> NestedNames vars -> Env Term vars ->
              ImpClause -> Core (Either RawImp Clause)
checkClause mult vis totreq hashit n opts nest env (ImpossibleClause fc lhs)
    = do lhs_raw <- lhsInCurrentNS nest lhs
         handleUnify
           (do autoimp <- isUnboundImplicits
               setUnboundImplicits True
               (_, lhs) <- bindNames False lhs_raw
               setUnboundImplicits autoimp

               log "declare.def.clause.impossible" 5 $ "Checking " ++ show lhs
               logEnv "declare.def.clause.impossible" 5 "In env" env
               (lhstm, lhstyg) <-
                           elabTerm n (InLHS mult) opts nest env
                                      (IBindHere fc PATTERN lhs) Nothing
               defs <- get Ctxt
               lhs <- normaliseHoles env lhstm
               if !(hasEmptyPat defs env lhs)
                  then pure (Left lhs_raw)
                  else throw (ValidCase fc env (Left lhs)))
           (\err =>
              case err of
                   ValidCase _ _ _ => throw err
                   _ => do defs <- get Ctxt
                           if !(impossibleErrOK err)
                              then pure (Left lhs_raw)
                              else throw (ValidCase fc env (Right err)))
checkClause {vars} mult vis totreq hashit n opts nest env (PatClause fc lhs_in rhs)
    = do (_, (vars'  ** (sub', env', nest', lhstm', lhsty'))) <-
             checkLHS False mult n opts nest env fc lhs_in
         let rhsMode = if isErased mult then InType else InExpr
         log "declare.def.clause" 5 $ "Checking RHS " ++ show rhs
         logEnv "declare.def.clause" 5 "In env" env'

         rhstm <- logTime 3 ("Check RHS " ++ show fc) $
                    wrapErrorC opts (InRHS fc !(getFullName (Resolved n))) $
                       checkTermSub n rhsMode opts nest' env' env sub' rhs !(nf env' lhsty')
         clearHoleLHS

         logTerm "declare.def.clause" 3 "RHS term" rhstm
         when hashit $
           do addHashWithNames lhstm'
              addHashWithNames rhstm
              log "module.hash" 15 "Adding hash for def."
         -- If the rhs is a hole, record the lhs in the metadata because we
         -- might want to split it interactively
         case rhstm of
              Meta _ _ _ _ =>
                 addLHS (getFC lhs_in) (length env) env' lhstm'
              _ => pure ()
         pure (Right (MkClause env' lhstm' rhstm))
-- TODO: (to decide) With is complicated. Move this into its own module?
checkClause {vars} mult vis totreq hashit n opts nest env
    (WithClause ifc lhs_in rig wval_raw mprf flags cs)
    = do (lhs, (vars'  ** (sub', env', nest', lhspat, reqty))) <-
             checkLHS False mult n opts nest env ifc lhs_in
         let wmode
               = if isErased mult || isErased rig then InType else InExpr

         (wval, gwvalTy) <- wrapErrorC opts (InRHS ifc !(getFullName (Resolved n))) $
                elabTermSub n wmode opts nest' env' env sub' wval_raw Nothing
         clearHoleLHS

         logTerm "declare.def.clause.with" 5 "With value (at quantity \{show rig})" wval
         logTerm "declare.def.clause.with" 3 "Required type" reqty
         wvalTy <- quote env' gwvalTy
         wval <- normaliseHoles env' wval
         wvalTy <- normaliseHoles env' wvalTy

         let (wevars ** withSub) = keepOldEnv sub' (snd (findSubEnv env' wval))
         logTerm "declare.def.clause.with" 5 "With value type" wvalTy
         log "declare.def.clause.with" 5 $ "Using vars " ++ show wevars

         let Just wval = shrinkTerm wval withSub
             | Nothing => throw (InternalError "Impossible happened: With abstraction failure #1")
         let Just wvalTy = shrinkTerm wvalTy withSub
             | Nothing => throw (InternalError "Impossible happened: With abstraction failure #2")
         -- Should the env be normalised too? If the following 'impossible'
         -- error is ever thrown, that might be the cause!
         let Just wvalEnv = shrinkEnv env' withSub
             | Nothing => throw (InternalError "Impossible happened: With abstraction failure #3")

         -- Abstracting over 'wval' in the scope of bNotReq in order
         -- to get the 'magic with' behaviour
         (wargs ** (scenv, var, binder)) <- bindWithArgs rig wvalTy ((,wval) <$> mprf) wvalEnv

         let bnr = bindNotReq vfc 0 env' withSub [] reqty
         let notreqns = fst bnr
         let notreqty = snd bnr

         let repFn = if Syntactic `elem` flags
                       then replaceSyn
                       else replace
         wtyScope <- repFn scenv !(nf scenv (weakenNs (mkSizeOf wargs) wval))
                            var
                            !(nf scenv
                                 (weakenNs (mkSizeOf wargs) notreqty))
         let bNotReq = binder wtyScope

         -- The environment has some implicit and some explcit args, potentially,
         -- which is inconvenient since we have to know which is which when
         -- elaborating the application of the rhs function. So it's easier
         -- if we just make them all explicit - this type isn't visible to
         -- users anyway!
         let env' = mkExplicit env'

         let Just (reqns, envns, wtype) = bindReq vfc env' withSub [] bNotReq
             | Nothing => throw (InternalError "Impossible happened: With abstraction failure #4")

         -- list of argument names - 'Just' means we need to match the name
         -- in the with clauses to find out what the pattern should be.
         -- 'Nothing' means it's the with pattern (so wargn)
         let wargNames
                 = map Just reqns ++
                   Nothing :: map Just notreqns

         logTerm "declare.def.clause.with" 3 "With function type" wtype
         log "declare.def.clause.with" 5 $ "Argument names " ++ show wargNames

         wname <- genWithName !(prettyName !(toFullNames (Resolved n)))
         widx <- addDef wname ({flags $= (SetTotal totreq ::)}
                                    (newDef vfc wname (if isErased mult then erased else top)
                                      vars wtype vis None))

         let toWarg : Maybe (PiInfo RawImp, Name) -> List (Maybe Name, RawImp)
               := flip maybe (\pn => [(Nothing, IVar vfc (snd pn))]) $
                    (Nothing, wval_raw) ::
                    case mprf of
                      Nothing => []
                      Just _  =>
                       let fc = emptyFC in
                       let refl = IVar fc (NS builtinNS (UN $ Basic "Refl")) in
                       [(mprf, INamedApp fc refl (UN $ Basic "x") wval_raw)]

         let rhs_in = gapply (IVar vfc wname)
                    $ map (\ nm => (Nothing, IVar vfc nm)) envns
                   ++ concatMap toWarg wargNames

         log "declare.def.clause.with" 3 $ "Applying to with argument " ++ show rhs_in
         rhs <- wrapErrorC opts (InRHS ifc !(getFullName (Resolved n))) $
             checkTermSub n wmode opts nest' env' env sub' rhs_in
                          !(nf env' reqty)

         -- Generate new clauses by rewriting the matched arguments
         cs' <- traverse (mkClauseWith 1 wname wargNames lhs) cs
         log "declare.def.clause.with" 3 $ "With clauses: " ++ show cs'

         -- Elaborate the new definition here
         nestname <- applyEnv env wname
         let nest'' = { names $= (nestname ::) } nest

         let wdef = IDef ifc wname cs'
         processDecl [] nest'' env wdef

         pure (Right (MkClause env' lhspat rhs))
  where
    vfc : FC
    vfc = virtualiseFC ifc

    mkExplicit : forall vs . Env Term vs -> Env Term vs
    mkExplicit [<] = [<]
    mkExplicit (env :< Pi fc c _ ty) = mkExplicit env :< Pi fc c Explicit ty
    mkExplicit (env :< b) = mkExplicit env :< b

    bindWithArgs :
       (rig : RigCount) -> (wvalTy : Term xs) -> Maybe (Name, Term xs) ->
       (wvalEnv : Env Term xs) ->
       Core (ext : SnocList Name
         ** ( Env Term (xs ++ ext)
            , Term (xs ++ ext)
            , (Term (xs ++ ext) -> Term xs)
            ))
    bindWithArgs {xs} rig wvalTy Nothing wvalEnv =
      let wargn : Name
          wargn = MN "warg" 0
          wargs : SnocList Name
          wargs = [<wargn]

          scenv : Env Term (xs ++ wargs)
                := wvalEnv :< Pi vfc top Explicit wvalTy

          var : Term (xs ++ wargs)
              := Local vfc Z First

          binder : Term (xs ++ wargs) -> Term xs
                 := Bind vfc wargn (Pi vfc rig Explicit wvalTy)

      in pure (wargs ** (scenv, var, binder))

    bindWithArgs {xs} rig wvalTy (Just (name, wval)) wvalEnv = do
      defs <- get Ctxt

      Just eqName <- getEqualTy
        | _ => throw (GenericMsg (getLoc wval) "No builtin equality defined")
      Just (TCon _ ar) <- lookupDefExact eqName (gamma defs)
        | _ => throw (InternalError "Cannot find builtin equality: \{show eqName}")
      let eqTyCon = Ref vfc (TyCon ar) !(toResolvedNames eqName)

      let wargn : Name
          wargn = MN "warg" 0
          wargs : SnocList Name
          wargs = [<wargn, name]

          wvalTy' := weaken wvalTy
          eqTy : Term (xs :< MN "warg" 0)
               := apply vfc eqTyCon
                           [ (erased, wvalTy')
                           , (erased, wvalTy')
                           , (top, weaken wval)
                           , (top, Local vfc Z First)
                           ]

          scenv : Env Term (xs ++ wargs)
                := wvalEnv
                    :< Pi vfc top Explicit wvalTy
                    :< Pi vfc top Implicit eqTy

          var : Term (xs ++ wargs)
              := Local vfc (S Z) (Later First)

          binder : Term (xs ++ wargs) -> Term xs
                 := \ t => Bind vfc wargn (Pi vfc rig Explicit wvalTy)
                         $ Bind vfc name  (Pi vfc rig Implicit eqTy) t

      pure (wargs ** (scenv, var, binder))

    -- If it's 'KeepCons/SubRefl' in 'outprf', that means it was in the outer
    -- environment so we need to keep it in the same place in the 'with'
    -- function. Hence, turn it to KeepCons whatever
    keepOldEnv : {0 outer : _} -> {vs : _} ->
                 (outprf : SubVars outer vs) -> SubVars vs' vs ->
                 (vs'' : SnocList Name ** SubVars vs'' vs)
    keepOldEnv {vs} SubRefl p = (vs ** SubRefl)
    keepOldEnv {vs} p SubRefl = (vs ** SubRefl)
    keepOldEnv (DropCons p) (DropCons p')
        = let (_ ** rest) = keepOldEnv p p' in
              (_ ** DropCons rest)
    keepOldEnv (DropCons p) (KeepCons p')
        = let (_ ** rest) = keepOldEnv p p' in
              (_ ** KeepCons rest)
    keepOldEnv (KeepCons p) (DropCons p')
        = let (_ ** rest) = keepOldEnv p p' in
              (_ ** KeepCons rest)
    keepOldEnv (KeepCons p) (KeepCons p')
        = let (_ ** rest) = keepOldEnv p p' in
              (_ ** KeepCons rest)

    -- Rewrite the clauses in the block to use an updated LHS.
    -- 'drop' is the number of additional with arguments we expect
    -- (i.e. the things to drop from the end before matching LHSs)
    mkClauseWith : (drop : Nat) -> Name ->
                   List (Maybe (PiInfo RawImp, Name)) ->
                   RawImp -> ImpClause ->
                   Core ImpClause
    mkClauseWith drop wname wargnames lhs (PatClause ploc patlhs rhs)
        = do log "declare.def.clause.with" 20 "PatClause"
             newlhs <- getNewLHS ploc drop nest wname wargnames lhs patlhs
             newrhs <- withRHS ploc drop wname wargnames rhs lhs
             pure (PatClause ploc newlhs newrhs)
    mkClauseWith drop wname wargnames lhs (WithClause ploc patlhs rig wval prf flags ws)
        = do log "declare.def.clause.with" 20 "WithClause"
             newlhs <- getNewLHS ploc drop nest wname wargnames lhs patlhs
             newwval <- withRHS ploc drop wname wargnames wval lhs
             ws' <- traverse (mkClauseWith (S drop) wname wargnames lhs) ws
             pure (WithClause ploc newlhs rig newwval prf flags ws')
    mkClauseWith drop wname wargnames lhs (ImpossibleClause ploc patlhs)
        = do log "declare.def.clause.with" 20 "ImpossibleClause"
             newlhs <- getNewLHS ploc drop nest wname wargnames lhs patlhs
             pure (ImpossibleClause ploc newlhs)


-- Calculate references for the given name, and recursively if they haven't
-- been calculated already
calcRefs : {auto c : Ref Ctxt Defs} ->
           (runtime : Bool) -> (aTotal : Name) -> (fn : Name) -> Core ()
calcRefs rt at fn
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact fn (gamma defs)
              | _ => pure ()
         let Function pi tree_ct tree_rt pats = definition gdef
              | _ => pure () -- not a function definition
         let refs : Maybe (NameMap Bool)
                  = if rt then refersToRuntimeM gdef else refersToM gdef
         let Nothing = refs
              | Just _ => pure () -- already done
         let tree : Term [<] = if rt then tree_rt else tree_ct
         let metas = getMetas tree
         traverse_ addToSave (keys metas)
         let refs_all = addRefs False at metas tree
         refs <- ifThenElse rt
                    (dropErased (keys refs_all) refs_all)
                    (pure refs_all)
         ignore $ ifThenElse rt
            (addDef fn ({ refersToRuntimeM := Just refs } gdef))
            (addDef fn ({ refersToM := Just refs } gdef))
         traverse_ (calcRefs rt at) (keys refs)
  where
    dropErased : List Name -> NameMap Bool -> Core (NameMap Bool)
    dropErased [] refs = pure refs
    dropErased (n :: ns) refs
        = do defs <- get Ctxt
             Just gdef <- lookupCtxtExact n (gamma defs)
                  | Nothing => dropErased ns refs
             if multiplicity gdef /= erased
                then dropErased ns refs
                else dropErased ns (delete n refs)

-- Compile run time case trees for the given name
mkRunTime : {auto c : Ref Ctxt Defs} ->
            {auto m : Ref MD Metadata} ->
            {auto u : Ref UST UState} ->
            FC -> (CaseType, Name) -> Core ()
mkRunTime fc (ct, n)
    = do log "compile.casetree" 5 $ "Making run time definition for " ++ show !(toFullNames n)
         defs <- get Ctxt
         Just gdef <- lookupCtxtExact n (gamma defs)
              | _ => pure ()
         let cov = gdef.totality.isCovering
         -- If it's erased at run time, don't build the tree
         when (not (isErased $ multiplicity gdef)) $ do
           let Function pi tree_ct _ (Just pats) = definition gdef
                | _ => pure () -- not a function definition
           let ty = type gdef
           -- Prepare RHS of definitions, by erasing 0-multiplicities, and
           -- finding any applications to specialise (partially evaluate)
           pats' <- traverse (toErased (location gdef)) pats
           let clauses = case cov of
                              MissingCases _ => addErrorCase pats'
                              _ => pats'
           (tree_rt, _) <- getPMDef (location gdef) ct RunTime n ty clauses

           log "compile.casetree" 10 $ show tree_rt
           ignore $ addDef n $
                       { definition := Function pi tree_ct tree_rt (Just pats)
                       } gdef
  where
    mkCrash : {vars : _} -> String -> Term vars
    mkCrash msg
       = apply fc (Ref fc Func (NS builtinNS (UN $ Basic "idris_crash")))
               [(erased, Erased fc Placeholder),
                (top, PrimVal fc (Str msg))]

    matchAny : Term vars -> Term vars
    matchAny (App fc f c a) = App fc (matchAny f) c (Erased fc Placeholder)
    matchAny tm = tm

    makeErrorClause : {vars : _} -> Env Term vars -> Term vars -> Clause
    makeErrorClause env lhs
        = MkClause env (matchAny lhs)
             (mkCrash ("Unhandled input for " ++ show n ++ " at " ++ show fc))

    addErrorCase : List Clause -> List Clause
    addErrorCase [] = []
    addErrorCase [MkClause env lhs rhs]
        = MkClause env lhs rhs :: makeErrorClause env lhs :: []
    addErrorCase (x :: xs) = x :: addErrorCase xs

    toErased : FC -> Clause -> Core Clause
    toErased fc (MkClause env lhs rhs)
        = do lhs_erased <- erase linear env lhs
             rhs' <- applyTransforms env rhs
             rhs_erased <- erase linear env rhs'
             pure (MkClause env lhs_erased rhs_erased)

compileRunTime : {auto c : Ref Ctxt Defs} ->
                 {auto m : Ref MD Metadata} ->
                 {auto u : Ref UST UState} ->
                 FC -> Name -> Core ()
compileRunTime fc atotal
    = do defs <- get Ctxt
         traverse_ (mkRunTime fc) (toCompileCase defs)
         traverse_ (calcRefs True atotal) (map snd (toCompileCase defs))

         update Ctxt { toCompileCase := [] }

warnUnreachable : {auto c : Ref Ctxt Defs} ->
                  Clause -> Core ()
warnUnreachable (MkClause env lhs rhs)
    = recordWarning (UnreachableClause (getLoc lhs) env lhs)

isAlias : RawImp -> Maybe ((FC, Name)                -- head symbol
                          , List (FC, (FC, String))) -- pattern variables
isAlias lhs
  = do let (hd, apps) = getFnArgs lhs []
       hd <- isIVar hd
       args <- traverse (isExplicit >=> bitraverse pure isIBindVar) apps
       pure (hd, args)

lookupOrAddAlias : {vars : _} ->
                   {auto m : Ref MD Metadata} ->
                   {auto c : Ref Ctxt Defs} ->
                   {auto u : Ref UST UState} ->
                   List ElabOpt -> NestedNames vars -> Env Term vars -> FC ->
                   Name -> List ImpClause -> Core (Maybe GlobalDef)
lookupOrAddAlias eopts nest env fc n [cl@(PatClause _ lhs _)]
  = do defs <- get Ctxt
       log "declare.def.alias" 20 $ "Looking at \{show cl}"
       Nothing <- lookupCtxtExact n (gamma defs)
         | Just gdef => pure (Just gdef)
       -- No prior declaration:
       --   1) check whether it has the shape of an alias
       let Just (hd, args) = isAlias lhs
         | Nothing => pure Nothing
       --   2) check whether it could be a misspelling
       log "declare.def" 5 $
         "Missing type declaration for the alias "
         ++ show n
         ++ ". Checking first whether it is a misspelling."
       [] <- do -- get the candidates
                Just (str, kept) <- getSimilarNames n
                   | Nothing => pure []
                -- only keep the ones that haven't been defined yet
                decls <- for kept $ \ (cand, weight) => do
                    Just gdef <- lookupCtxtExact cand (gamma defs)
                      | Nothing => pure Nothing -- should be impossible
                    let None = definition gdef
                      | _ => pure Nothing
                    pure (Just (cand, weight))
                pure $ showSimilarNames (currentNS defs) n str $ catMaybes decls
          | (x :: xs) => throw (MaybeMisspelling (NoDeclaration fc n) (x ::: xs))
       --   3) declare an alias
       log "declare.def" 5 "Not a misspelling: go ahead and declare it!"
       processType eopts nest env fc top Public []
          $ MkImpTy fc fc n $ holeyType (map snd args)
       defs <- get Ctxt
       lookupCtxtExact n (gamma defs)

  where
    holeyType : List (FC, String) -> RawImp
    holeyType [] = Implicit fc False
    holeyType ((xfc, x) :: xs)
      = let xfc = virtualiseFC xfc in
        IPi xfc top Explicit (Just (UN $ Basic x)) (Implicit xfc False)
      $ holeyType xs

lookupOrAddAlias _ _ _ fc n _
  = do defs <- get Ctxt
       lookupCtxtExact n (gamma defs)

export
processDef : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto m : Ref MD Metadata} ->
             {auto u : Ref UST UState} ->
             List ElabOpt -> NestedNames vars -> Env Term vars -> FC ->
             Name -> List ImpClause -> Core ()
processDef opts nest env fc n_in cs_in
    = do n <- inCurrentNS n_in
         defs <- get Ctxt
         Just gdef <- lookupOrAddAlias opts nest env fc n cs_in
           | Nothing => noDeclaration fc n
         let None = definition gdef
              | _ => throw (AlreadyDefined fc n)
         let ty = type gdef
         -- a module's interface hash (what determines when the module has changed)
         -- should include the definition (RHS) of anything that is public (available
         -- at compile time for elaboration) _or_ inlined (dropped into destination definitions
         -- during compilation).
         let hashit = visibility gdef == Public || (Inline `elem` gdef.flags)
         let mult = if isErased (multiplicity gdef)
                       then erased
                       else linear
         nidx <- resolveName n

         -- Dynamically rebind default totality requirement to this function's totality requirement
         -- and use this requirement when processing `with` blocks
         log "declare.def" 5 $ "Traversing clauses of " ++ show n ++ " with mult " ++ show mult
         let treq = fromMaybe !getDefaultTotalityOption (findSetTotal (flags gdef))
         cs <- withTotality treq $
               traverse (checkClause mult (visibility gdef) treq
                                     hashit nidx opts nest env) cs_in
         let pats = rights cs

         let ct = if elem InCase opts then CaseBlock n else PatMatch
         (tree_ct, unreachable) <-
             logTime 3 ("Building compile time case tree for " ++ show n) $
                getPMDef fc ct (CompileTime mult) n ty pats
         traverse_ warnUnreachable unreachable

         logC "declare.def" 2 $
                 do ctnf <- normaliseHoles [<] tree_ct
                    t <- toFullNames ctnf
                    ct <- toFullNames tree_ct
                    pure ("Case tree for " ++ show n ++ ": " ++ show ct
                          ++ "\n" ++ "Normalised to " ++ show t)
         log "declare.def" 10 $ "Patterns: " ++ show !(toFullNames pats)

         -- check whether the name was declared in a different source file
         defs <- get Ctxt
         let pi = case lookup n (userHoles defs) of
                        Nothing => defaultFI
                        Just e => { externalDecl := e } defaultFI
         -- Add compile time tree as a placeholder for the runtime tree,
         -- but we'll rebuild that in a later pass once all the case
         -- blocks etc are resolved
         ignore $ addDef (Resolved nidx)
                  ({ definition := Function pi tree_ct tree_ct (Just pats)
                   } gdef)

         when (visibility gdef == Public) $
             do let rmetas = getMetas tree_ct
                log "declare.def" 10 $ "Saving from " ++ show n ++ ": " ++ show (keys rmetas)
                traverse_ addToSave (keys rmetas)
         when (isUserName n && visibility gdef /= Private) $
             do let tymetas = getMetas (type gdef)
                traverse_ addToSave (keys tymetas)
         addToSave n

         -- Flag this name as one which needs compiling
         update Ctxt { toCompileCase $= ((ct, n) ::) }

         atotal <- toResolvedNames (NS builtinNS (UN $ Basic "assert_total"))
         logTime 3 ("Building size change graphs " ++ show n) $
           when (not (InCase `elem` opts)) $
             do calcRefs False atotal (Resolved nidx)
                sc <- calculateSizeChange fc n
                log "totality.termination.sizechange" 5 $ "Graph: " ++ show sc
                setSizeChange fc n sc
                checkIfGuarded fc n

         md <- get MD -- don't need the metadata collected on the coverage check
         cov <- logTime 3 ("Checking Coverage " ++ show n) $ checkCoverage nidx ty mult cs
         setCovering fc n cov
         put MD md

         -- If we're not in a case tree, compile all the outstanding case
         -- trees.
         when (not (elem InCase opts)) $
              compileRunTime fc atotal
  where
    -- Move `withTotality` to Core.Context if we need it elsewhere
    ||| Temporarily rebind the default totality requirement (%default total/partial/covering).
    withTotality : TotalReq -> Lazy (Core a) -> Core a
    withTotality tot c = do
         defaultTotality <- getDefaultTotalityOption
         setDefaultTotalityOption tot
         x <- catch c (\error => do setDefaultTotalityOption defaultTotality
                                    throw error)
         setDefaultTotalityOption defaultTotality
         pure x


    simplePat : forall vars . Term vars -> Bool
    simplePat (Local _ _ _) = True
    simplePat (Erased _ _) = True
    simplePat (As _ _ _ p) = simplePat p
    simplePat _ = False

    -- Is the clause returned from 'checkClause' a catch all clause, i.e.
    -- one where all the arguments are variables? If so, no need to do the
    -- (potentially expensive) coverage check
    catchAll : Clause -> Bool
    catchAll (MkClause env lhs _)
       = all simplePat (getArgs lhs)

    -- Return 'Nothing' if the clause is impossible, otherwise return the
    -- checked clause (with implicits filled in, so that we can see if they
    -- match any of the given clauses)
    checkImpossible : Int -> RigCount -> ClosedTerm ->
                      Core (Maybe ClosedTerm)
    checkImpossible n mult tm
        = do itm <- unelabNoPatvars [<] tm
             let itm = map rawName itm
             handleUnify
               (do ctxt <- get Ctxt
                   log "declare.def.impossible" 3 $ "Checking for impossibility: " ++ show itm
                   autoimp <- isUnboundImplicits
                   setUnboundImplicits True
                   (_, lhstm) <- bindNames False itm
                   setUnboundImplicits autoimp
                   (lhstm, _) <- elabTerm n (InLHS mult) [] (MkNested []) [<]
                                    (IBindHere fc COVERAGE lhstm) Nothing
                   logTerm "declare.def.impossible" 5 "LHS term" lhstm
                   lhs <- normaliseHoles [<] lhstm
                   defs <- get Ctxt
                   if !(hasEmptyPat defs [<] lhs)
                      then do log "declare.def.impossible" 5 "Some empty pat"
                              put Ctxt ctxt
                              pure Nothing
                      else do log "declare.def.impossible" 5 "No empty pat"
                              rtm <- closeEnv !(nf [<] lhs)
                              put Ctxt ctxt
                              pure (Just rtm))
               (\err => do defs <- get Ctxt
                           if not !(recoverableErr err)
                              then pure Nothing
                              else pure (Just tm))
      where
        -- They'll be 'Bind' at the top level already, and we really don't
        -- want to expand when we get to the clause, so 'Glued' is what we
        -- want here.
        closeEnv : Glued [<] -> Core ClosedTerm
        closeEnv (VBind _ x (PVar _ _ _ _) sc)
            = closeEnv !(sc (pure (vRef fc Bound x)))
        closeEnv nf = quote [<] nf

    getClause : Either RawImp Clause -> Core (Maybe Clause)
    getClause (Left rawlhs)
        = catch (do lhsp <- getImpossibleTerm env nest rawlhs
                    log "declare.def.impossible" 3 $ "Generated impossible LHS: " ++ show lhsp
                    pure $ Just $ MkClause [<] lhsp (Erased (getFC rawlhs) Impossible))
                (\e => do log "declare.def" 5 $ "Error in getClause " ++ show e
                          pure Nothing)
    getClause (Right c) = pure (Just c)

    checkCoverage : Int -> ClosedTerm -> RigCount ->
                    List (Either RawImp Clause) ->
                    Core Covering
    checkCoverage n ty mult cs
        = do covcs' <- traverse getClause cs -- Make stand in LHS for impossible clauses
             log "declare.def.impossible" 5 $ unlines
               $ "Using clauses :"
               :: map (("  " ++) . show) !(traverse toFullNames covcs')
             let covcs = mapMaybe id covcs'
             (ctree, _) <-
                 getPMDef fc PatMatch (CompileTime mult) (Resolved n) ty covcs
             log "declare.def.impossible" 3 $ "Working from " ++ show !(toFullNames ctree)
             missCase <- if any catchAll covcs
                            then do log "declare.def" 3 $ "Catch all case in " ++ show n
                                    pure []
                            else getMissing fc (Resolved n) ctree
             logC "declare.def.impossible" 3 $
                     do mc <- traverse toFullNames missCase
                        pure ("Initially missing in " ++
                                 show !(getFullName (Resolved n)) ++ ":\n" ++
                                showSep "\n" (map show mc))
             -- Filter out the ones which are impossible
             missImp <- traverse (checkImpossible n mult) missCase
             -- Filter out the ones which are actually matched (perhaps having
             -- come up due to some overlapping patterns)
             logC "declare.def.impossible" 5 $
                 do mc <- traverse toFullNames missImp
                    pure ("Missing after checkImpossible:\n" ++
                              showSep "\n" (map show mc))
             missMatch <- traverse (checkMatched covcs) (mapMaybe id missImp)
             logC "declare.def.impossible" 5 $
                 do mc <- traverse toFullNames missMatch
                    pure ("Missing after checkMatched:\n" ++
                              showSep "\n" (map show mc))
             let miss = catMaybes missMatch
             if isNil miss
                then do [] <- getNonCoveringRefs fc (Resolved n)
                           | ns => toFullNames (NonCoveringCall ns)
                        pure IsCovering
                else pure (MissingCases miss)
