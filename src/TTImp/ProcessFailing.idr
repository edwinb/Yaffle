module TTImp.ProcessFailing

import Core.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Core.Metadata
import Core.Evaluate
import Core.Unify.State

import TTImp.Elab
import TTImp.Elab.Check
import TTImp.TTImp

import TTImp.ProcessDecls.Totality

import Data.List1

%default covering

export
processFailing :
  {vars : _} ->
  {auto c : Ref Ctxt Defs} ->
  {auto m : Ref MD Metadata} ->
  {auto u : Ref UST UState} ->
  List ElabOpt ->
  NestedNames vars -> Env Term vars ->
  FC -> Maybe String ->  List ImpDecl -> Core ()
processFailing eopts nest env fc mmsg decls
    = do -- save the state: the content of a failing block should be discarded
         ust <- get UST
         md <- get MD
         defs <- branch
         -- We're going to run the elaboration, and then return:
         -- * Nothing     if the block correctly failed
         -- * Just err    if it either did not fail or failed with an invalid error message
         result <- catch
               (do -- Run the elaborator
                   before <- getTotalityErrors
                   traverse_ (processDecl eopts nest env) decls
                   after <- getTotalityErrors
                   let errs = after \\ before
                   let (e :: es) = errs
                     | [] => -- We have (unfortunately) succeeded
                             pure (Just $ FailingDidNotFail fc)
                   let Just msg = mmsg
                     | _ => pure Nothing
                   log "elab.failing" 10 $ "Failing block based on \{show msg} failed with \{show errs}"
                   test <- anyM (checkError msg) errs
                   pure $ do -- Unless the error is the expected one
                             guard (not test)
                             -- We should complain we had the wrong one
                             pure (FailingWrongError fc msg (e ::: es)))
               (\err => do let Just msg = mmsg
                                 | _ => pure Nothing
                           log "elab.failing" 10 $ "Failing block based on \{show msg} failed with \{show err}"
                           test <- checkError msg err
                           pure $ do -- Unless the error is the expected one
                                     guard (not test)
                                     -- We should complain we had the wrong one
                                     pure (FailingWrongError fc msg (err ::: [])))
         md' <- get MD
         -- Reset the state
         put UST ust
         -- For metadata, we preserve the syntax highlithing information (but none
         -- of the things that may include code that's dropped like types, LHSs, etc.)
         put MD ({ semanticHighlighting := semanticHighlighting md'
                 , semanticAliases := semanticAliases md'
                 , semanticDefaults := semanticDefaults md'
                 } md)
         put Ctxt defs
         -- And fail if the block was successfully accepted
         whenJust result throw
