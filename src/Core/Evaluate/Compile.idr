module Core.Evaluate.Compile

import Core.Directory
import Core.Error
import Core.Evaluate.ToScheme
import Core.TT
import Core.Context

import Libraries.Utils.Scheme
import System.Info

-- Compilation for the Scheme-based evaluator. We compile top level definitions
-- to Scheme definitions. This is Just-In-Time, rather than compiled and
-- exported, largely because the majority of definitions are either not
-- needed for compile-time evaluation, needed only once, or small enough that
-- saving doesn't help.

public export
data EvalMode = EvalAll | EvalTC

schString : String -> String
schString s = concatMap okchar (unpack s)
  where
    okchar : Char -> String
    okchar c = if isAlphaNum c || c =='_'
                  then cast c
                  else "C-" ++ show (cast {to=Int} c)

schVarUN : UserName -> String
schVarUN (Basic n) = schString n
schVarUN (Field n) = "rf--" ++ schString n
schVarUN Underscore = "_US_"

schVarName : Name -> String
schVarName (NS ns (UN n))
   = schString (showNSWithSep "-" ns) ++ "-" ++ schVarUN n
schVarName (NS ns n) = schString (showNSWithSep "-" ns) ++ "-" ++ schVarName n
schVarName (UN n) = "u--" ++ schVarUN n
schVarName (MN n i) = schString n ++ "-" ++ show i
schVarName (PV n d) = "pat--" ++ schVarName n
schVarName (DN _ n) = schVarName n
schVarName (Nested (i, x) n) = "n--" ++ show i ++ "-" ++ show x ++ "-" ++ schVarName n
schVarName (CaseBlock x y) = "case--" ++ schString x ++ "-" ++ show y
schVarName (WithBlock x y) = "with--" ++ schString x ++ "-" ++ show y
schVarName (Resolved i) = "fn--" ++ show i

schName : EvalMode -> Name -> String
schName EvalAll n = "ct-ALL-" ++ schVarName n
schName EvalTC  n = "ct-TC-" ++ schVarName n

parameters {auto c : Ref Ctxt Defs}
  -- forward declare, so that we can compile names in a body when we
  -- encounter them
  compileDef : Name -> Core ()

  compileBody : EvalMode -> Name -> Def -> Core (SchemeObj Write)

  compileDef n_in
    = do n <- toFullNames n_in -- this is handy for readability of generated names
                     -- we used resolved names for blocked names, though, as
                     -- that's a bit better for performance
         defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
              | Nothing => throw (UndefinedName emptyFC n)
         -- If it's already been done, don't do it again
         -- (Assumption: if a definition is ever updated, its evaldef is
         -- cleared)
         let Nothing = evaldef def
               | _ => pure () -- already done
         -- Check whether the name is available for reduction in evalTC mode
         let redok = reducibleInAny (currentNS defs :: nestedNS defs)
                                    (fullname def)
                                    (visibility def)

         -- 'n' is used in compileBody for generating names for readback,
         -- and reading back resolved names is quicker because it's just
         -- an integer
         n_res <- toResolvedNames n
         def_full <- toFullNames (definition def)

         b_all <- compileBody EvalAll n_res def_full
         b_tc <- compileBody EvalTC n_res def_full
         let schdef_all = Define (schName EvalAll n) b_all
         let schdef_tc = Define (schName EvalTC n) b_tc

         -- Add the new definition to the current scheme runtime
         Just obj_all <- coreLift $ evalSchemeObj schdef_all
              | Nothing => throw (InternalError ("Compiling " ++ show n ++ " failed"))
         Just obj_tc <- coreLift $ evalSchemeObj schdef_tc
              | Nothing => throw (InternalError ("Compiling " ++ show n ++ " failed"))
         -- Record that this one is done
         ignore $ addDef n
              ({ evaldef := Just (MkCompiledTerm schdef_tc schdef_all) } def)

  initEvalWith : String -> CoreFile Bool
  initEvalWith "chez"
      = do defs <- get Ctxt
           if defs.schemeEvalLoaded
              then pure True
              else
               catch (do f <- readDataFile "chez/ct-support.ss"
                         Just _ <- coreLift $ evalSchemeStr $ "(begin " ++ f ++ ")"
                              | Nothing => pure False
                         put Ctxt ({ schemeEvalLoaded := True } defs)
                         pure True)
                  (\err => pure False)
  initEvalWith "racket"
      = do defs <- get Ctxt
           if defs.schemeEvalLoaded
              then pure True
              else
               catch (do f <- readDataFile "racket/ct-support.rkt"
                         Just _ <- coreLift $ evalSchemeStr $ "(begin " ++ f ++ ")"
                              | Nothing => pure False
                         put Ctxt ({ schemeEvalLoaded := True } defs)
                         pure True)
                  (\err => do coreLift $ printLn err
                              pure False)
  initEvalWith _ = pure False -- only works on Chez for now

-- Initialise the internal functions we need to build/extend blocked
-- applications
-- These are in a support file, chez/support.ss. Returns True if loading
-- and processing succeeds. If it fails, which it probably will during a
-- bootstrap build at least, we can fall back to the default evaluator.
export
initialiseSchemeEval : Ref Ctxt Defs => CoreFile Bool
initialiseSchemeEval = initEvalWith codegen
