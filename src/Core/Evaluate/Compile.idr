module Core.Evaluate.Compile

import Core.Directory
import Core.Error
import Core.Evaluate.ToScheme
import Core.TT
import Core.Context

import Libraries.Utils.Scheme
import System.Info

initEvalWith : Ref Ctxt Defs => String -> CoreFile Bool
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
