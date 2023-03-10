module Core.Termination

import Core.Context
import Core.Context.Log
import Core.Env
import Core.TT
import Core.Evaluate

import Core.Termination.CallGraph
import Core.Termination.Positivity
import Core.Termination.SizeChange

import Libraries.Data.NameMap
import Libraries.Data.SortedMap
import Data.List
import Data.String

%default covering

-- Termination checking follows (more or less)
-- "The size-change principle for program termination" by Lee, Jones and
-- Ben-Amram. https://doi.org/10.1145/360204.360210

-- Check if all branches end up as constructor arguments, with no other
-- function application, and set 'AllGuarded' if so.
-- This is to check whether a function can be considered a constructor form
-- for the sake of termination checking (and might have other uses...)
export
checkIfGuarded : {auto c : Ref Ctxt Defs} ->
                 FC -> Name -> Core ()
checkIfGuarded fc n
    = do logC "totality.termination.guarded" 6 $ do pure "Check if Guarded: \{show !(toFullNames n)}"
         defs <- get Ctxt
         Just (Function _ tm _ _) <- lookupDefExact n (gamma defs)
              | _ => pure ()
         tmnf <- nf [<] tm
         -- Just work from 'Glued', don't do any actual normalisation
         t <- guardedDef tmnf
         log "totality.termination.guarded" 6 (show t)
         if t then do Just gdef <- lookupCtxtExact n (gamma defs)
                           | Nothing => pure ()
                      g <- allM (checkNotFn defs) (keys (refersTo gdef))
                      log "totality.termination.guarded" 6
                            $ "Refers to " ++ show !(toFullNames (keys (refersTo gdef)))
                      when g $ setFlag fc n AllGuarded
              else pure ()
  where
    guardedNF : {vars : _} -> Glued vars -> Core Bool
    guardedNF (VDCon{}) = pure True
    guardedNF (VApp _ _ n _ _)
        = do defs <- get Ctxt
             Just gdef <- lookupCtxtExact n (gamma defs)
                  | Nothing => pure False
             pure (AllGuarded `elem` flags gdef)
    guardedNF _ = pure False

    guardedScope : {vars : _} -> (args : _) -> VCaseScope args vars -> Core Bool
    guardedScope [<] sc = guardedNF (snd !sc)
    guardedScope (sx :< y) sc = guardedScope sx (sc (pure (VErased fc Placeholder)))

    guardedAlt : {vars : _} -> VCaseAlt vars -> Core Bool
    guardedAlt (VConCase _ _ _ args sc) = guardedScope _ sc
    guardedAlt (VDelayCase fc ty arg sc)
        = guardedScope [< (top, arg), (top, ty) ] sc
    guardedAlt (VConstCase _ _ sc) = guardedNF sc
    guardedAlt (VDefaultCase _ sc) = guardedNF sc

    guardedAlts : {vars : _} -> List (VCaseAlt vars) -> Core Bool
    guardedAlts [] = pure True
    guardedAlts (x :: xs)
        = if !(guardedAlt x) then guardedAlts xs else pure False

    guardedDef : {vars : _} ->  Glued vars -> Core Bool
    guardedDef (VLam fc _ _ _ _ sc)
        = guardedDef !(sc (VErased fc Placeholder))
    guardedDef (VCase fc ct c _ _ alts)
        = guardedAlts alts
    guardedDef nf = guardedNF nf

    checkNotFn : Defs -> Name -> Core Bool
    checkNotFn defs n
        = do Just gdef <- lookupCtxtExact n (gamma defs)
                  | Nothing => pure False
             case definition gdef of
                  DCon _ _ _ => pure True
                  _ => pure (multiplicity gdef == erased
                              || (AllGuarded `elem` flags gdef))

-- Check whether a function is terminating, and record in the context
export
checkTerminating : {auto c : Ref Ctxt Defs} ->
                   FC -> Name -> Core Terminating
checkTerminating loc n
    = do tot <- getTotality loc n
         logC "totality.termination" 6 $ do pure "Checking termination: \{show !(toFullNames n)}"
         case isTerminating tot of
              Unchecked =>
                 do tot' <- calcTerminating loc n
                    setTerminating loc n tot'
                    pure tot'
              t => pure t

-- Check whether a data type satisfies the strict positivity condition, and
-- record in the context
export
checkPositive : {auto c : Ref Ctxt Defs} ->
                FC -> Name -> Core Terminating
checkPositive loc n_in
    = do n <- toResolvedNames n_in
         tot <- getTotality loc n
         logC "totality.positivity" 6 $ do pure "Checking positivity: \{show !(toFullNames n)}"
         case isTerminating tot of
              Unchecked =>
                  do (tot', cons) <- calcPositive loc n
                     setTerminating loc n tot'
                     traverse_ (\c => setTerminating loc c tot') cons
                     pure tot'
              t => pure t

-- Check and record totality of the given name; positivity if it's a data
-- type, termination if it's a function
export
checkTotal : {auto c : Ref Ctxt Defs} ->
             FC -> Name -> Core Terminating
checkTotal loc n_in
    = do defs <- get Ctxt
         let Just nidx = getNameID n_in (gamma defs)
             | Nothing => undefinedName loc n_in
         let n = Resolved nidx
         tot <- getTotality loc n
         logC "totality" 5 $ do pure "Checking totality: \{show !(toFullNames n)}"
         defs <- get Ctxt
         case isTerminating tot of
              Unchecked => do
                  mgdef <- lookupCtxtExact n (gamma defs)
                  case definition <$> mgdef of
                       Just (TCon{})
                           => checkPositive loc n
                       _ => do whenJust (refersToM =<< mgdef) $ \ refs =>
                                 logC "totality" 5 $ do pure $ "  Mutually defined with:"
                                                            ++ show !(traverse toFullNames (keys refs))
                               checkTerminating loc n
              t => pure t
