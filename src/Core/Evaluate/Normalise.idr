module Core.Evaluate.Normalise

import Core.Context
import Core.Core
import Core.Env
import Core.Error
import Core.Evaluate.Value
import Core.Primitives
import Core.TT

import Data.List
import Data.SnocList
import Data.Vect

apply : FC -> Value vars -> Value vars -> Core (Value vars)
apply fc (VLam _ _ _ _ _ sc) arg = sc arg
apply fc (VApp afc nt n spine go) arg
    = pure $ VApp afc nt n (spine :< (fc, arg)) $
           do Just go' <- go
                   | Nothing => pure Nothing
              Just <$> apply fc go' arg
apply fc (VLocal lfc l idx p spine) arg
    = pure $ VLocal lfc l idx p (spine :< (fc, arg))
apply fc (VMeta mfc n i sc spine go) arg
    = pure $ VMeta mfc n i sc (spine :< (fc, arg)) $
           do Just go' <- go
                   | Nothing => pure Nothing
              Just <$> apply fc go' arg
apply fc (VDCon dfc n t a spine) arg
    = pure $ VDCon dfc n t a (spine :< (fc, arg))
apply fc (VTCon tfc n a spine) arg
    = pure $ VTCon tfc n a (spine :< (fc, arg))
apply fc (VAs _ _ _ pat) arg
    = apply fc pat arg -- doesn't really make sense to keep the name
apply fc (VForce ffc r v spine) arg
    = pure $ VForce ffc r v (spine :< (fc, arg))
apply fc (VCase cfc sc ty alts) arg
    = pure $ VCase cfc sc ty !(traverse (applyAlt arg) alts)
  where
    applyConCase : Value vars ->
                   Name -> Int ->
                   (args : List Name) ->
                   VCaseScope args vars ->
                   VCaseScope args vars
    applyConCase arg n t [] rhs
        = do rhs' <- rhs
             apply fc rhs' arg
    applyConCase arg n t (a :: args) sc
        = \a' => applyConCase arg n t args (sc a')

    -- Need to apply the argument to the rhs of every case branch
    applyAlt : Value vars -> VCaseAlt vars -> Core (VCaseAlt vars)
    applyAlt arg (VConCase n t args rhs)
        = pure $ VConCase n t args (applyConCase arg n t args rhs)
    applyAlt arg (VDelayCase t a rhs)
        = pure $ VDelayCase t a
                  (\t', a' =>
                      do rhs' <- rhs t' a'
                         apply fc rhs' arg)
    applyAlt arg (VConstCase c rhs) = VConstCase c <$> apply fc rhs arg
    applyAlt arg (VDefaultCase rhs) = VDefaultCase <$> apply fc rhs arg
-- Remaining cases would be ill-typed
apply _ arg _ = pure arg

applyAll : FC -> Value vars -> List (Value vars) -> Core (Value vars)
applyAll fc f [] = pure f
applyAll fc f (x :: xs)
    = do f' <- apply fc f x
         applyAll fc f' xs

data LocalEnv : List Name -> List Name -> Type where
     Nil : LocalEnv [] vars
     (::) : Value vars -> LocalEnv free vars -> LocalEnv (x :: free) vars

extend : LocalEnv ns vars -> LocalEnv ms vars -> LocalEnv (ns ++ ms) vars
extend [] env = env
extend (x :: vars) env = x :: extend vars env

data ExtendLocs : List Name -> List Name -> Type where
     Lin : ExtendLocs vars []
     (:<) : ExtendLocs vars xs -> Value vars -> ExtendLocs vars (xs ++ [x])

mkEnv : ExtendLocs vars ns -> LocalEnv ns vars
mkEnv {vars} ext = rewrite sym (appendNilRightNeutral ns) in go ext []
  where
    go : ExtendLocs vars ns' -> LocalEnv rest vars ->
         LocalEnv (ns' ++ rest) vars
    go [<] locs = locs
    go {ns' = xs ++ [x]} {rest} (ext :< val) locs
        = rewrite sym (appendAssociative xs [x] rest) in
                  go ext (val :: locs)

runOp : {vars : _} ->
        FC -> PrimFn ar -> Vect ar (Value vars) -> Value vars
runOp fc op args
    = case getOp op args of
           Just res => res
           Nothing => VPrimOp fc op args

parameters {auto c : Ref Ctxt Defs}

  -- Forward declared since these are all mutual
  export
  eval : {vars : _} ->
         LocalEnv free vars ->
         Env Term vars ->
         Term (free ++ vars) -> Core (Value vars)

  evalCaseAlt : {vars : _} ->
                LocalEnv free vars -> Env Term vars ->
                CaseAlt (free ++ vars) ->
                Core (VCaseAlt vars)
  evalCaseAlt {vars} {free} locs env (ConCase n tag scope)
      = pure $ VConCase n tag _ (getScope locs scope)
    where
      CaseArgs : CaseScope vs -> List Name
      CaseArgs (RHS tm) = []
      CaseArgs (Arg x sc) = x :: CaseArgs sc

      getScope : forall free .
                 LocalEnv free vars ->
                 (sc : CaseScope (free ++ vars)) ->
                 VCaseScope (CaseArgs sc) vars
      getScope locs (RHS tm) = eval locs env tm
      getScope locs (Arg x sc) = \v => getScope (v :: locs) sc

  evalCaseAlt locs env (DelayCase t a tm)
      = pure $ VDelayCase t a (\t', a' => eval (t' :: a' :: locs) env tm)
  evalCaseAlt locs env (ConstCase c tm)
      = pure $ VConstCase c !(eval locs env tm)
  evalCaseAlt locs env (DefaultCase tm)
      = pure $ VDefaultCase !(eval locs env tm)

  blockedCase : {vars : _} ->
                FC -> LocalEnv free vars -> Env Term vars ->
                (sc : Value vars) -> (scTy : Term (free ++ vars)) ->
                List (CaseAlt (free ++ vars)) ->
                Core (Value vars)
  blockedCase fc locs env sc scTy alts
      = do scTy' <- eval locs env scTy
           alts' <- traverse (evalCaseAlt locs env) alts
           pure (VCase fc sc scTy' alts')

  tryAlts : {vars : _} ->
            LocalEnv free vars -> Env Term vars ->
            (sc : Value vars) -> -- scrutinee, which we assume to be in
                  -- canonical form since we've checked (so not blocked)
            List (CaseAlt (free ++ vars)) ->
            Core (Value vars) -> -- what to do if stuck
            Core (Value vars)
  tryAlts {vars} locs env sc@(VDCon _ _ t a sp) (ConCase _ t' cscope :: as) stuck
      = if t == t' then evalCaseScope locs sp cscope
           else tryAlts locs env sc as stuck
    where
      evalCaseScope : forall free . LocalEnv free vars ->
                      Spine vars -> CaseScope (free ++ vars) ->
                      Core (Value vars)
      evalCaseScope locs [<] (RHS tm) = eval locs env tm
      evalCaseScope locs (sp :< v) (Arg x sc)
          = evalCaseScope (snd v :: locs) sp sc
      evalCaseScope _ _ _ = stuck

  tryAlts locs env sc@(VDelay _ _ ty arg) (DelayCase ty' arg' rhs :: as) stuck
      = eval (ty :: arg :: locs) env rhs
  tryAlts locs env sc@(VPrimVal _ c) (ConstCase c' rhs :: as) stuck
      = if c == c'
           then eval locs env rhs
           else tryAlts locs env sc as stuck
  tryAlts locs env sc (DefaultCase rhs :: as) stuck = eval locs env rhs
  tryAlts locs env sc (a :: as) stuck = tryAlts locs env sc as stuck
  tryAlts locs env sc [] stuck = stuck

  evalCase : {vars : _} ->
             FC -> LocalEnv free vars -> Env Term vars ->
             (sc : Value vars) -> (scTy : Term (free ++ vars)) ->
             List (CaseAlt (free ++ vars)) ->
             Core (Value vars)
  evalCase fc locs env sc ty alts
      = if isCanonical sc
           then tryAlts locs env sc alts (blockedCase fc locs env sc ty alts)
           else blockedCase fc locs env sc ty alts
    where
      isCanonical : Value vars -> Bool
      isCanonical (VLam{}) = True
      isCanonical (VBind{}) = True
      isCanonical (VDCon{}) = True
      isCanonical (VTCon{}) = True
      isCanonical (VDelay{}) = True
      isCanonical (VPrimVal{}) = True
      isCanonical (VType{}) = True
      isCanonical _ = False

  evalLocal : {vars, idx : _} ->
              Env Term vars ->
              FC -> Maybe Bool ->
              (0 p : IsVar name idx (free ++ vars)) ->
              LocalEnv free vars ->
              Core (Value vars)
  evalLocal env fc mloc p []
      = case getBinder p env of
             Let _ _ val _ => eval [] env val
             _ => pure $ VLocal fc mloc _ p [<]
  evalLocal env fc mloc First (x :: locs) = pure x
  evalLocal env fc mloc (Later p) (x :: locs) = evalLocal env fc mloc p locs

  evalPiInfo : {vars : _} ->
               LocalEnv free vars ->
               Env Term vars ->
               PiInfo (Term (free ++ vars)) ->
               Core (PiInfo (Value vars))
  evalPiInfo locs env Implicit = pure Implicit
  evalPiInfo locs env Explicit = pure Explicit
  evalPiInfo locs env AutoImplicit = pure AutoImplicit
  evalPiInfo locs env (DefImplicit x)
      = do x' <- eval locs env x
           pure (DefImplicit x')

  evalBinder : {vars : _} ->
               LocalEnv free vars ->
               Env Term vars ->
               Binder (Term (free ++ vars)) ->
               Core (Binder (Value vars))
  evalBinder locs env (Lam fc c p ty)
     = pure $ Lam fc c !(evalPiInfo locs env p) !(eval locs env ty)
  evalBinder locs env (Let fc c val ty)
     = pure $ Let fc c !(eval locs env val) !(eval locs env ty)
  evalBinder locs env (Pi fc c p ty)
     = pure $ Pi fc c !(evalPiInfo locs env p) !(eval locs env ty)
  evalBinder locs env (PVar fc c p ty)
     = pure $ PVar fc c !(evalPiInfo locs env p) !(eval locs env ty)
  evalBinder locs env (PLet fc c val ty)
     = pure $ PLet fc c !(eval locs env val) !(eval locs env ty)
  evalBinder locs env (PVTy fc c ty)
     = pure $ PVTy fc c !(eval locs env ty)

--   Declared above with this type:
--   eval : {vars : _} ->
--          LocalEnv free vars ->
--          Env Term vars ->
--          Term (free ++ vars) -> Core (Value vars)
  eval locs env (Local fc l idx p) = evalLocal env fc l p locs
  eval locs env (Ref fc (DataCon t a) n)
      = pure $ VDCon fc n t a [<]
  eval locs env (Ref fc (TyCon a) n)
      = pure $ VTCon fc n a [<]
  eval locs env tm@(Ref fc nt n)
      = pure $ VApp fc nt n [<] $
             do defs <- get Ctxt
                Just def <- lookupCtxtExact n (gamma defs)
                    | Nothing => pure Nothing
                let Function _ fn = definition def
                    | _ => pure Nothing
                Just <$> eval locs env (embed fn)
  eval locs env (Meta fc n i scope)
       = do scope' <- traverse (eval locs env) scope
            pure $ VMeta fc n i scope' [<] $
                 do defs <- get Ctxt
                    Just def <- lookupCtxtExact n (gamma defs)
                        | Nothing => pure Nothing
                    let Function _ fn = definition def
                        | _ => pure Nothing
                    Just <$> applyAll fc !(eval locs env (embed fn)) scope'
  eval locs env (Bind fc x (Lam bfc r p ty) sc)
      = pure $ VLam fc x r !(evalPiInfo locs env p) !(eval locs env ty)
                    (\arg => eval (arg :: locs) env sc)
  eval locs env (Bind fc x (Let bfc c val ty) sc)
      = do val' <- eval locs env val
           eval (val' :: locs) env sc
  eval locs env (Bind fc x b sc)
      = pure $ VBind fc x !(evalBinder locs env b)
                     (\arg => eval (arg :: locs) env sc)
  eval locs env (App fc fn arg)
      = apply fc !(eval locs env fn) !(eval locs env arg)
  eval locs env (As fc use (AsLoc afc idx p) pat)
      = pure $ VAs fc use !(evalLocal env afc Nothing p locs)
                          !(eval locs env pat)
  eval locs env (As fc use _ pat)
      = eval locs env pat
  eval locs env (Case fc sc ty alts)
      = evalCase fc locs env !(eval locs env sc) ty alts
  eval locs env (TDelayed fc r tm)
      = pure $ VDelayed fc r !(eval locs env tm)
  eval locs env (TDelay fc r ty arg)
      = pure $ VDelay fc r !(eval locs env ty) !(eval locs env arg)
  eval locs env (TForce fc r tm)
      = do VDelay _ _ _ arg <- eval locs env tm
               | tm' => pure $ VForce fc r tm' [<]
           pure arg
  eval locs env (PrimVal fc c) = pure $ VPrimVal fc c
  eval {free} {vars} locs env (PrimOp fc op args)
      = pure $ runOp fc op !(evalArgs args)
    where
      -- No traverse for Vect in Core...
      evalArgs : Vect n (Term (free ++ vars)) -> Core (Vect n (Value vars))
      evalArgs [] = pure []
      evalArgs (a :: as) = pure $ !(eval locs env a) :: !(evalArgs as)

  eval locs env (Erased fc i) = pure $ VErased fc i
  eval locs env (Unmatched fc str) = pure $ VUnmatched fc str
  eval locs env (Impossible fc) = pure $ VImpossible fc
  eval locs env (TType fc n) = pure $ VType fc n

  export
  nf : {vars : _} ->
       Env Term vars -> Term vars -> Core (Value vars)
  nf = eval []
