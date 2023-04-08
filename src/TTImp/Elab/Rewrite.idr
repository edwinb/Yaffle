module TTImp.Elab.Rewrite

import Core.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Core.Metadata
import Core.Evaluate
import Core.Unify
import Core.TT

import TTImp.Elab.Check
import TTImp.Elab.Delayed
import TTImp.TTImp

import Data.SnocList

%default covering

-- TODO: Later, we'll get the name of the lemma from the type, if it's one
-- that's generated for a dependent type. For now, always return the default
findRewriteLemma : {auto c : Ref Ctxt Defs} ->
                   FC -> (rulety : Term vars) ->
                   Core Name
findRewriteLemma loc rulety
   = case !getRewrite of
          Nothing => throw (GenericMsg loc "No rewrite lemma defined")
          Just n => pure n

getRewriteTerms : {vars : _} ->
                  {auto c : Ref Ctxt Defs} ->
                  FC -> Defs -> NF vars -> Error ->
                  Core (Glued vars, Glued vars, Glued vars)
getRewriteTerms loc defs (VTCon nfc eq a args) err
    = if !(isEqualTy eq)
         then case map spineArg args of
                   (_ :< lhsty :< rhsty :< lhs :< rhs) =>
                        pure (!lhs, !rhs, !lhsty)
                   _ => throw err
         else throw err
getRewriteTerms loc defs ty err
    = throw err

rewriteErr : Error -> Bool
rewriteErr (NotRewriteRule _ _ _) = True
rewriteErr (RewriteNoChange _ _ _ _ _) = True
rewriteErr (InType _ _ err) = rewriteErr err
rewriteErr (InCon _ _ err) = rewriteErr err
rewriteErr (InLHS _ _ err) = rewriteErr err
rewriteErr (InRHS _ _ err) = rewriteErr err
rewriteErr (WhenUnifying _ _ _ _ _ err) = rewriteErr err
rewriteErr _ = False

record Lemma vars where
  constructor MkLemma
  ||| The name of the rewriting lemma
  name : Name
  ||| The predicate (\ v => lhs === rhs) to pass to it
  pred : Term vars
  ||| The type ((v : ?) -> Type) of the predicate
  predTy : Term vars

elabRewrite : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              FC -> Env Term vars ->
              (expected : Term vars) ->
              (rulety : Term vars) ->
              Core (Lemma vars)
elabRewrite loc env expected rulety
    = do defs <- get Ctxt
         parg <- genVarName "rwarg"
         tynf <- expand !(nf env rulety)
         (lt, rt, lty) <- getRewriteTerms loc defs tynf (NotRewriteRule loc env rulety)
         lemn <- findRewriteLemma loc rulety

         -- Need to normalise again, since we might have been delayed and
         -- the metavariables might have been updated
         expnf <- nf env expected

         logTerm "elab.rewrite" 5 "Rewriting" !(quoteNF env lt)
         logTerm "elab.rewrite" 5 "Rewriting in" !(quoteNF env expnf)
         rwexp_sc <- replace env lt (Ref loc Bound parg) expnf
         logTerm "elab.rewrite" 5 "Rewritten to" rwexp_sc

         ltyTm <- quote env lty
         let pred = Bind loc parg (Lam loc top Explicit ltyTm)
                          (refsToLocals (Add parg parg None) rwexp_sc)
         let predty = Bind loc parg (Pi loc top Explicit ltyTm)
                          (TType loc (MN "top" 0))

         -- if the rewritten expected type converts with the original,
         -- then the rewrite did nothing, which is an error
         defs <- get Ctxt
         when !(convert env rwexp_sc expected) $
             throw (RewriteNoChange loc defs env rulety expected)
         pure (MkLemma lemn pred predty)

export
checkRewrite : {vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               {auto m : Ref MD Metadata} ->
               {auto u : Ref UST UState} ->
               {auto e : Ref EST (EState vars)} ->
               RigCount -> ElabInfo ->
               NestedNames vars -> Env Term vars ->
               FC -> RawImp -> RawImp -> Maybe (Glued vars) ->
               Core (Term vars, Glued vars)
checkRewrite rigc elabinfo nest env fc rule tm Nothing
    = throw (GenericMsg fc "Can't infer a type for rewrite")
checkRewrite {vars} rigc elabinfo nest env ifc rule tm (Just expected)
    = delayOnFailure ifc rigc elabinfo env (Just expected) rewriteErr Rewrite $ \delayed =>
        do let vfc = virtualiseFC ifc

           constart <- getNextEntry
           (rulev, grulet) <- check erased elabinfo nest env rule Nothing
           solveConstraintsAfter constart inTerm Normal

           rulet <- quote env grulet
           expTy <- quote env expected
           when delayed $ log "elab.rewrite" 5 "Retrying rewrite"
           lemma <- elabRewrite vfc env expTy rulet

           rname <- genVarName "_"
           pname <- genVarName "_"

           let pbind = Let vfc erased lemma.pred lemma.predTy
           let rbind = Let vfc erased (weaken rulev) (weaken rulet)

           let env' = env :< pbind :< rbind

           -- Nothing we do in this last part will affect the EState,
           -- we're only doing the application this way to make sure the
           -- implicits for the rewriting lemma are in the right place. But,
           -- we still need the right type for the EState, so weaken it once
           -- for each of the let bindings above.
           (rwtm, grwty) <-
              inScope vfc (env :< pbind) $ \e' =>
                inScope {e=e'} vfc env' $ \e'' =>
                  let offset = mkSizeOf [< pname, rname] in
                  check {e = e''} rigc elabinfo (weakenNs offset nest) env'
                    (apply (IVar vfc lemma.name)
                      [ IVar vfc pname
                      , IVar vfc rname
                      , tm ])
                    (Just !(nf env' (weakenNs offset expTy)))
           rwty <- quote env' grwty
           let binding = Bind vfc pname pbind . Bind vfc rname rbind
           pure (binding rwtm, !(nf env (binding rwty)))
