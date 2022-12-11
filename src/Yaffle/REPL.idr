module Yaffle.REPL

import Core.AutoSearch
import Core.Binary
import Core.CompileExpr
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
import Core.TTCFile
import Core.Unify

import Compiler.CompileExpr

import TTImp.Elab
import TTImp.Elab.Check
import TTImp.Interactive.ExprSearch
import TTImp.Interactive.GenerateDef
import TTImp.Parser
import TTImp.ProcessFile
import TTImp.TTImp
import TTImp.TTImp.TTC
import TTImp.Unelab

import TTMain.ProcessTT

import Parser.Source

import Libraries.Utils.Path
import System
import System.File

%default covering

showInfo : {auto c : Ref Ctxt Defs} ->
           (Name, Int, GlobalDef) -> Core ()
showInfo (n, _, d)
    = do ignore $ checkTotal replFC n
         tot <- getTotality replFC n >>= toFullNames
         coreLift_ $ putStrLn (show n ++ " ==>\n" ++
                   "\t" ++ show !(toFullNames (definition d)) ++ "\n" ++
                   "\t" ++ show (sizeChange d) ++ "\n" ++
                   "\t" ++ show tot ++ "\n")

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
         ns <- lookupCtxtName n (gamma defs)
         traverse_ printName ns
         pure True
  where
    isHole : Def -> Maybe Nat
    isHole (Hole locs _) = Just locs
    isHole _ = Nothing

    showCount : RigCount -> String
    showCount Rig0 = " 0 "
    showCount Rig1 = " 1 "
    showCount RigW = "   "

    printHole : {vars : _} ->
                Name -> Nat -> Env Term vars -> Term vars -> Core ()
    printHole n Z env tm
        = do coreLift $ putStrLn "-------------------------------------"
             coreLift $ putStrLn $ show n ++ " : " ++ show !(unelabNoImp env tm)
    printHole n (S k) env (Bind _ x b@(Pi _ c _ ty) sc)
        = do coreLift $ putStr $ showCount c ++ show x ++ " : " ++
                        show !(unelabNoImp env ty) ++ "\n"
             printHole n k (env :< b) sc
    printHole n (S k) env tm
        = do coreLift $ putStrLn "-------------------------------------"
             coreLift $ putStrLn $ show n ++ " : " ++ show !(unelabNoImp env tm)

    printName : (Name, Int, GlobalDef) -> Core ()
    printName (n, i, gdef)
        = do let tyh = type gdef
             maybe (do ty <- toFullNames !(normaliseHoles [<] tyh)
                       coreLift_ $ putStrLn $ show n ++ " : " ++
                                    show !(unelabNoImp [<] ty))
                   (\locs => do tyb <- normaliseBinders [<] tyh
                                ty <- toFullNames !(normaliseHoles [<] tyb)
                                printHole n locs [<] ty)
                   (isHole (definition gdef))
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

process (ProofSearch n_in)
    = do defs <- get Ctxt
         [(n, i, ty)] <- lookupTyName n_in (gamma defs)
              | ns => ambiguousName (justFC defaultFC) n_in (map fst ns)
         def <- search (justFC defaultFC) top False 1000 n ty [<]
         defs <- get Ctxt
         defnf <- normaliseHoles [<] def
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
                                                 showSep "\n" (map show !(toFullNames cs))))
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
process (ShowCompiled n)
    = do compileDef n
         defs <- get Ctxt
         ns <- lookupCtxtName n (gamma defs)
         traverse_ showCompiled ns
         pure True
  where
    showCompiled : (Name, Int, GlobalDef) -> Core ()
    showCompiled (n, i, def)
        = case compexpr def of
               Nothing => pure ()
               Just cd => coreLift $ putStrLn (show n ++ " = " ++ show cd)
process Quit
    = do coreLift_ $ putStrLn "Bye for now!"
         pure False

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
                   {auto m : Ref MD Metadata} ->
                   {auto u : Ref UST UState} ->
                   String -> ModuleIdent -> Core Bool
processTTImpFile fname modIdent
    = do
         Right (ws, decor, tti) <-
              coreLift $ parseFile fname (PhysicalIdrSrc modIdent)
                            (do decls <- prog (PhysicalIdrSrc modIdent)
                                eoi
                                pure decls)
               | Left err => do coreLift (putStrLn (show err))
                                pure False
         traverse_ recordWarning ws

         catch (do ignore $ processTTImpDecls (MkNested []) [<] tti
                   Nothing <- checkDelayedHoles
                       | Just err => throw err
                   pure True)
               (\err => do coreLift_ (printLn err)
                           pure False)

HasNames () where
  full _ _ = pure ()
  resolved _ _ = pure ()

export
ttImpMain : String -> Core ()
ttImpMain fname
    = do defs <- initDefs
         c <- newRef Ctxt defs
         addPrimitives
         modIdent <- ctxtPathToNS fname
         m <- newRef MD (initMetadata (PhysicalIdrSrc modIdent))
         u <- newRef UST initUState
         case extension fname of
              Just "ttc" => do coreLift_ $ putStrLn "Processing as TTC"
                               ignore $
                                  readFromTTC {extra = ()} True emptyFC
                                      True fname (nsAsModuleIdent emptyNS) emptyNS
                               coreLift_ $ putStrLn "Read TTC"
              _ => do coreLift_ $ putStrLn "Processing as TTImp"
                      -- TODO: add a command line flag for timing
                      ok <- logTimeWhen False 1 "Processing" $
                               processTTImpFile fname modIdent
                      when ok $
                         do file $ makeBuildDirectory modIdent
                            ttcFileName <- getTTCFileName fname "ttc"
                            writeToTTC () fname ttcFileName
                            coreLift_ $ putStrLn $ "Written " ++ show ttcFileName
         repl
