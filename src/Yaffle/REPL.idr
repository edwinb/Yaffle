module Yaffle.REPL

import Core.AutoSearch
import Core.Context
import Core.Context.Log
import Core.Core
import Core.Directory
import Core.Env
import Core.Error
import Core.FC
import Core.InitPrimitives
import Core.Metadata
import Core.Evaluate
import Core.Syntax.Parser
import Core.Termination
import Core.TT
import Core.Unify

import TTImp.Elab
import TTImp.Elab.Check
-- import TTImp.Interactive.ExprSearch
-- import TTImp.Interactive.GenerateDef
import TTImp.Parser
import TTImp.ProcessFile
import TTImp.TTImp
import TTImp.Unelab

import TTMain.ProcessTT

import Parser.Source

import System
import System.File

%default covering

showInfo : {auto c : Ref Ctxt Defs} ->
           (Name, Int, GlobalDef) -> Core ()
showInfo (n, _, d)
    = coreLift_ $ putStrLn (show n ++ " ==>\n" ++
                   "\t" ++ show !(toFullNames (definition d)) ++ "\n" ++
                   "\t" ++ show (sizeChange d) ++ "\n")

-- Returns 'True' if the REPL should continue
process : {auto c : Ref Ctxt Defs} ->
          {auto m : Ref MD Metadata} ->
          {auto u : Ref UST UState} ->
          ImpREPL -> Core Bool
process (Eval ttimp)
    = do (tm, _) <- elabTerm 0 InExpr [] (MkNested []) [<] ttimp Nothing
         defs <- get Ctxt
         tmnf <- toFullNames !(normalise [<] tm)
         coreLift_ (printLn !(unelabNoImp [<] tmnf))
         pure True
process (Check (IVar _ n))
    = do defs <- get Ctxt
         ns <- lookupTyName n (gamma defs)
         traverse_ printName ns
         pure True
  where
    printName : (Name, Int, ClosedTerm) -> Core ()
    printName (n, _, tyh)
        = do defs <- get Ctxt
             ty <- toFullNames !(normaliseHoles [<] tyh)
             coreLift_ $ putStrLn $ show n ++ " : " ++
                                    show !(unelabNoImp [<] ty)
process (Check ttimp)
    = do (tm, gty) <- elabTerm 0 InExpr [] (MkNested []) [<] ttimp Nothing
         defs <- get Ctxt
         tyh <- quote [<] gty
         ty <- toFullNames !(normaliseHoles [<] tyh)
         coreLift_ (printLn !(unelab [<] ty))
         pure True
process (DebugInfo n)
    = do defs <- get Ctxt
         traverse_ showInfo !(lookupCtxtName n (gamma defs))
         pure True

{-
process (ProofSearch n_in)
    = do defs <- get Ctxt
         [(n, i, ty)] <- lookupTyName n_in (gamma defs)
              | ns => ambiguousName (justFC defaultFC) n_in (map fst ns)
         def <- search (justFC defaultFC) top False 1000 n ty []
         defs <- get Ctxt
         defnf <- normaliseHoles defs [] def
         coreLift_ (printLn !(toFullNames defnf))
         pure True
process (ExprSearch n_in)
    = do defs <- get Ctxt
         [(n, i, ty)] <- lookupTyName n_in (gamma defs)
              | ns => ambiguousName (justFC defaultFC) n_in (map fst ns)
         results <- exprSearchN (justFC defaultFC) 1 n []
         traverse_ (coreLift . printLn) results
         pure True
process (GenerateDef line name)
    = do defs <- get Ctxt
         Just (_, n', _, _) <- findTyDeclAt (\p, n => onLine line p)
              | Nothing => do coreLift_ (putStrLn ("Can't find declaration for " ++ show name))
                              pure True
         case !(lookupDefExact n' (gamma defs)) of
              Just None =>
                  catch
                    (do ((fc, cs) :: _) <- logTime 0 "Generation" $
                                makeDefN (\p, n => onLine line p) 1 n'
                           | _ => coreLift_ (putStrLn "Failed")
                        coreLift_ $ putStrLn (show cs))
                    (\err => coreLift_ $ putStrLn $ "Can't find a definition for " ++ show n')
              Just _ => coreLift_ $ putStrLn "Already defined"
              Nothing => coreLift_ $ putStrLn $ "Can't find declaration for " ++ show name
         pure True
process (Missing n_in)
    = do defs <- get Ctxt
         case !(lookupCtxtName n_in (gamma defs)) of
              [] => undefinedName emptyFC n_in
              ts => do traverse_ (\fn =>
                          do tot <- getTotality emptyFC fn
                             case isCovering tot of
                                  MissingCases cs =>
                                     coreLift_ (putStrLn (show fn ++ ":\n" ++
                                                 showSep "\n" (map show cs)))
                                  NonCoveringCall ns =>
                                     coreLift_ (putStrLn
                                         (show fn ++ ": Calls non covering function"
                                           ++ case ns of
                                                   [fn] => " " ++ show fn
                                                   _ => "s: " ++ showSep ", " (map show ns)))
                                  _ => coreLift_ $ putStrLn (show fn ++ ": All cases covered"))
                        (map fst ts)
                       pure True
process (CheckTotal n)
    = do defs <- get Ctxt
         case !(lookupCtxtName n (gamma defs)) of
              [] => undefinedName emptyFC n
              ts => do traverse_ (\fn =>
                          do ignore $ checkTotal emptyFC fn
                             tot <- getTotality emptyFC fn
                             coreLift_ (putStrLn (show fn ++ " is " ++ show tot)))
                               (map fst ts)
                       pure True
-}
process Quit
    = do coreLift_ $ putStrLn "Bye for now!"
         pure False
process _ = throw (InternalError "Not implemented")

processCatch : {auto c : Ref Ctxt Defs} ->
               {auto m : Ref MD Metadata} ->
               {auto u : Ref UST UState} ->
               ImpREPL -> Core Bool
processCatch cmd
    = catch (process cmd)
            (\err => do coreLift_ (putStrLn (show err))
                        pure True)


export
repl : {auto c : Ref Ctxt Defs} ->
       {auto m : Ref MD Metadata} ->
       {auto u : Ref UST UState} ->
       Core ()
repl
    = do coreLift_ (putStr "Yaffle> ")
         inp <- coreLift getLine
         case runParser (Virtual Interactive) Nothing inp command of
              Left err => do coreLift_ (printLn err)
                             repl
              Right (_, _, cmd) => when !(processCatch cmd) repl

export
processTTImpFile : {auto c : Ref Ctxt Defs} ->
                   String -> Core Bool
processTTImpFile fname
    = do modIdent <- ctxtPathToNS fname
         Right (ws, decor, tti) <-
              coreLift $ parseFile fname (PhysicalIdrSrc modIdent)
                            (do decls <- prog (PhysicalIdrSrc modIdent)
                                eoi
                                pure decls)
               | Left err => do coreLift (putStrLn (show err))
                                pure False
         traverse_ recordWarning ws
         m <- newRef MD (initMetadata (PhysicalIdrSrc modIdent))
         u <- newRef UST initUState

         catch (do ignore $ processTTImpDecls (MkNested []) [<] tti
                   Nothing <- checkDelayedHoles
                       | Just err => throw err
                   repl
                   pure True)
               (\err => do coreLift_ (printLn err)
                           pure False)

export
ttImpMain : String -> Core ()
ttImpMain fname
    = do defs <- initDefs
         c <- newRef Ctxt defs
         addPrimitives
         ok <- processTTImpFile fname
         -- TODO: when ok, write out TTC
         pure ()
