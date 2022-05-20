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

export
apply : FC -> Value vars -> RigCount -> Value vars -> Core (Value vars)
apply fc (VLam _ _ _ _ _ sc) _ arg = sc arg
apply fc (VApp afc nt n spine go) q arg
    = pure $ VApp afc nt n (spine :< (fc, q, arg)) $
           do Just go' <- go
                   | Nothing => pure Nothing
              res <- apply fc go' q arg
              pure (Just res)
apply fc (VLocal lfc l idx p spine) q arg
    = pure $ VLocal lfc l idx p (spine :< (fc, q, arg))
apply fc (VMeta mfc n i sc spine go) q arg
    = pure $ VMeta mfc n i sc (spine :< (fc, q, arg)) $
           do Just go' <- go
                   | Nothing => pure Nothing
              res <- apply fc go' q arg
              pure (Just res)
apply fc (VDCon dfc n t a spine) q arg
    = pure $ VDCon dfc n t a (spine :< (fc, q, arg))
apply fc (VTCon tfc n a spine) q arg
    = pure $ VTCon tfc n a (spine :< (fc, q, arg))
apply fc (VAs _ _ _ pat) q arg
    = apply fc pat q arg -- doesn't really make sense to keep the name
apply fc (VForce ffc r v spine) q arg
    = pure $ VForce ffc r v (spine :< (fc, q, arg))
apply fc (VCase cfc sc ty alts) q arg
    = pure $ VCase cfc sc ty !(traverse (applyAlt arg) alts)
  where
    applyConCase : Value vars ->
                   Name -> Int ->
                   (args : SnocList Name) ->
                   VCaseScope args vars ->
                   VCaseScope args vars
    applyConCase arg n t [<] rhs
        = do rhs' <- rhs
             apply fc rhs' q arg
    applyConCase arg n t (args :< a) sc
        = \a' => applyConCase arg n t args (sc a')

    -- Need to apply the argument to the rhs of every case branch
    applyAlt : Value vars -> VCaseAlt vars -> Core (VCaseAlt vars)
    applyAlt arg (VConCase n t args rhs)
        = pure $ VConCase n t args (applyConCase arg n t args rhs)
    applyAlt arg (VDelayCase t a rhs)
        = pure $ VDelayCase t a
                  (\t', a' =>
                      do rhs' <- rhs t' a'
                         apply fc rhs' q arg)
    applyAlt arg (VConstCase c rhs) = VConstCase c <$> apply fc rhs q arg
    applyAlt arg (VDefaultCase rhs) = VDefaultCase <$> apply fc rhs q arg
-- Remaining cases would be ill-typed
apply _ arg _ _ = pure arg

applyAll : FC -> Value vars -> List (RigCount, Value vars) -> Core (Value vars)
applyAll fc f [] = pure f
applyAll fc f ((q, x) :: xs)
    = do f' <- apply fc f q x
         applyAll fc f' xs

data LocalEnv : SnocList Name -> SnocList Name -> Type where
     Lin : LocalEnv [<] vars
     (:<) : LocalEnv free vars -> Value vars -> LocalEnv (free :< x) vars

extend : LocalEnv ns vars -> LocalEnv ms vars -> LocalEnv (ms ++ ns) vars
extend [<] env = env
extend (vars :< x) env = extend vars env :< x

updateEnv : {idx : _} ->
            LocalEnv free vars ->
            (0 _ : IsVar name idx (vars ++ free)) -> Value vars ->
            LocalEnv free vars
updateEnv (env :< b) First new = env :< new
updateEnv (env :< b) (Later p) new = updateEnv env p new :< b
updateEnv env _ _ = env

namespace ExtendLocs
  public export
  data ExtendLocs : SnocList Name -> SnocList Name -> Type where
       Lin : ExtendLocs vars [<]
       (:<) : ExtendLocs vars xs -> Value vars -> ExtendLocs vars (cons x xs)

mkEnv : ExtendLocs vars ns -> LocalEnv ns vars
mkEnv {vars} ext = rewrite sym (appendLinLeftNeutral ns) in go ext [<]
  where
    go : ExtendLocs vars ns' -> LocalEnv rest vars ->
         LocalEnv (rest ++ ns') vars
    go [<] locs = locs
    go {ns' = cons x xs} {rest} (ext :< val) locs
        = rewrite appendAssociative rest [<x] xs in
                  go ext (locs :< val)

runOp : {vars : _} ->
        FC -> PrimFn ar -> Vect ar (Value vars) -> Core (Value vars)
runOp fc op args
    = do args' <- traverseVect getVal args
         -- If it gets stuck, return the glued args, not the values
         case getOp op args' of
           Just res => pure res
           Nothing => pure $ VPrimOp fc op args

parameters {auto c : Ref Ctxt Defs}

  -- Forward declared since these are all mutual
  export
  eval : {vars : _} ->
         LocalEnv free vars ->
         Env Term vars ->
         Term (vars ++ free) -> Core (Value vars)

  evalCaseAlt : {vars : _} ->
                LocalEnv free vars -> Env Term vars ->
                CaseAlt (vars ++ free) ->
                Core (VCaseAlt vars)
  evalCaseAlt {vars} {free} locs env (ConCase n tag scope)
      = pure $ VConCase n tag _ (getScope locs scope)
    where
      CaseArgs : CaseScope vs -> SnocList Name
      CaseArgs (RHS tm) = [<]
      CaseArgs (Arg x sc) = CaseArgs sc :< x

      getScope : forall free .
                 LocalEnv free vars ->
                 (sc : CaseScope (vars ++ free)) ->
                 VCaseScope (CaseArgs sc) vars
      getScope locs (RHS tm) = eval locs env tm
      getScope locs (Arg x sc) = \v => getScope (locs :< v) sc

  evalCaseAlt locs env (DelayCase t a tm)
      = pure $ VDelayCase t a (\t', a' => eval (locs :< a' :< t') env tm)
  evalCaseAlt locs env (ConstCase c tm)
      = pure $ VConstCase c !(eval locs env tm)
  evalCaseAlt locs env (DefaultCase tm)
      = pure $ VDefaultCase !(eval locs env tm)

  blockedCase : {vars : _} ->
                FC -> LocalEnv free vars -> Env Term vars ->
                (sc : Value vars) -> (scTy : Term (vars ++ free)) ->
                List (CaseAlt (vars ++ free)) ->
                Core (Value vars)
  blockedCase fc locs env sc scTy alts
      = do scTy' <- eval locs env scTy
           alts' <- traverse (evalCaseAlt locs env) alts
           pure (VCase fc sc scTy' alts')

  tryAlts : {vars : _} ->
            LocalEnv free vars -> Env Term vars ->
            (sc : Value vars) -> -- scrutinee, which we assume to be in
                  -- canonical form since we've checked (so not blocked)
            List (CaseAlt (vars ++ free)) ->
            Core (Value vars) -> -- what to do if stuck
            Core (Value vars)
  tryAlts {vars} locs env sc@(VDCon _ _ t a sp) (ConCase _ t' cscope :: as) stuck
      = if t == t' then evalCaseScope locs (cast sp) cscope
           else tryAlts locs env sc as stuck
    where
      -- We've turned the spine into a list so that the argument positions
      -- correspond when going through the CaseScope
      evalCaseScope : forall free . LocalEnv free vars ->
                      List (FC, RigCount, Value vars) -> CaseScope (vars ++ free) ->
                      Core (Value vars)
      evalCaseScope locs [] (RHS tm) = eval locs env tm
      evalCaseScope locs ((_, _, v) :: sp) (Arg x sc)
          = evalCaseScope (locs :< v) sp sc
      evalCaseScope _ _ _ = stuck

  tryAlts locs env sc@(VDelay _ _ ty arg) (DelayCase ty' arg' rhs :: as) stuck
      = eval (locs :< ty :< arg) env rhs
  tryAlts locs env sc@(VPrimVal _ c) (ConstCase c' rhs :: as) stuck
      = if c == c'
           then eval locs env rhs
           else tryAlts locs env sc as stuck
  tryAlts locs env sc (DefaultCase rhs :: as) stuck = eval locs env rhs
  tryAlts locs env sc (a :: as) stuck = tryAlts locs env sc as stuck
  tryAlts locs env sc [] stuck = stuck

  evalCase : {vars : _} ->
             FC -> LocalEnv free vars -> Env Term vars ->
             (sc : Value vars) -> (scTy : Term (vars ++ free)) ->
             List (CaseAlt (vars ++ free)) ->
             Core (Value vars)
  evalCase fc locs env sc_in ty alts
      = do sc <- getVal sc_in
           if isCanonical sc
              then tryAlts locs env sc alts (blockedCase fc locs env sc ty alts)
              else blockedCase fc locs env sc_in ty alts
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
              (0 p : IsVar name idx (vars ++ free)) ->
              LocalEnv free vars ->
              Core (Value vars)
  evalLocal env fc mloc p [<]
      = case getBinder p env of
             MkBinder _ _ (LetVal val) _ => eval [<] env val
             _ => pure $ VLocal fc mloc _ p [<]
  evalLocal env fc mloc First (locs :< x) = pure x
  evalLocal env fc mloc (Later p) (locs :< x) = evalLocal env fc mloc p locs

  evalPiInfo : {vars : _} ->
               LocalEnv free vars ->
               Env Term vars ->
               PiInfo (Term (vars ++ free)) ->
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
               Binder (Term (vars ++ free)) ->
               Core (Binder (Value vars))
  evalBinder locs env (MkBinder fc c p ty)
     = pure $ MkBinder fc c !(mapBinderM (evalPiInfo locs env) (eval locs env) p)
                            !(eval locs env ty)

--   Declared above with this type:
--   eval : {vars : _} ->
--          LocalEnv free vars ->
--          Env Term vars ->
--          Term (vars ++ free) -> Core (Value vars)
  eval locs env (Local fc l idx p) = evalLocal env fc l p locs
  eval locs env (Ref fc (DataCon t a) n)
      = pure $ VDCon fc n t a [<]
  eval locs env (Ref fc (TyCon a) n)
      = pure $ VTCon fc n a [<]
  eval locs env tm@(Ref fc nt n)
      = do defs <- get Ctxt
           Just def <- lookupCtxtExact n (gamma defs)
                | Nothing => pure (VApp fc nt n [<] (pure Nothing))
           let Function _ fn = definition def
                | _ => pure (VApp fc nt n [<] (pure Nothing))
           pure $ VApp fc nt n [<] $
                    do res <- eval locs env (embed fn)
                       pure (Just res)
  eval locs env (Meta fc n i scope)
       = do scope' <- traverse (\ (q, val) =>
                                     do val' <- eval locs env val
                                        pure (q, val')) scope
            defs <- get Ctxt
            Just def <- lookupCtxtExact n (gamma defs)
                 | Nothing => pure (VMeta fc n i scope' [<] (pure Nothing))
            let Function _ fn = definition def
                 | _ => pure (VMeta fc n i scope' [<] (pure Nothing))
            pure $ VMeta fc n i scope' [<] $
                     do evalfn <- eval locs env (embed fn)
                        res <- applyAll fc evalfn scope'
                        pure (Just res)
  eval locs env (Bind fc x (MkBinder bfc r (LamVal p) ty) sc)
      = pure $ VLam fc x r !(evalPiInfo locs env p) !(eval locs env ty)
                    (\arg => eval (locs :< arg) env sc)
  eval locs env (Bind fc x (MkBinder bfc c (LetVal val) ty) sc)
      = do val' <- eval locs env val
           eval (locs :< val') env sc
  eval locs env (Bind fc x b sc)
      = pure $ VBind fc x !(evalBinder locs env b)
                     (\arg => eval (locs :< arg) env sc)
  eval locs env (App fc fn q arg)
      = apply fc !(eval locs env fn) q !(eval locs env arg)
  eval locs env (As fc use (AsLoc afc idx p) pat)
      = pure $ VAs fc use !(evalLocal env afc Nothing p locs)
                          !(eval locs env pat)
  eval locs env (As fc use _ pat)
      = eval locs env pat
  eval locs env (Case fc sc ty alts)
      = do sc' <- eval locs env sc
           locs' <- case sc of
                         Local _ _ _ p => pure $ updateEnv locs p !(getVal sc')
                         _ => pure locs
           evalCase fc locs' env sc' ty alts
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
      = runOp fc op !(evalArgs args)
    where
      -- No traverse for Vect in Core...
      evalArgs : Vect n (Term (vars ++ free)) -> Core (Vect n (Value vars))
      evalArgs [] = pure []
      evalArgs (a :: as) = pure $ !(eval locs env a) :: !(evalArgs as)

  eval locs env (Erased fc i) = pure $ VErased fc i
  eval locs env (Unmatched fc str) = pure $ VUnmatched fc str
  eval locs env (Impossible fc) = pure $ VImpossible fc
  eval locs env (TType fc n) = pure $ VType fc n

  export
  nf : {vars : _} ->
       Env Term vars -> Term vars -> Core (Value vars)
  nf = eval [<]
