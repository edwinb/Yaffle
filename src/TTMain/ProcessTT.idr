module TTMain.ProcessTT

import Core.Context
import Core.Env
import Core.Error
import Core.Evaluate
import Core.Syntax.Decls
import Core.Syntax.Raw
import Core.Check.Typecheck
import Core.Unify.State
import Core.Unify

parameters {auto c : Ref Ctxt Defs} {auto u : Ref UST UState}
  processEval : RawI -> Core ()
  processEval rawtm
      = do (tm, ty) <- infer linear [<] rawtm
           tmnf <- normalise [<] tm
           coreLift $ putStrLn $ show !(toFullNames tmnf) ++ " : "
                                     ++ show !(toFullNames ty)

  processHNF : RawI -> Core ()
  processHNF rawtm
      = do (tm, ty) <- infer linear [<] rawtm
           tmnf <- normaliseHNF [<] tm
           coreLift $ putStrLn $ show !(toFullNames tmnf) ++ " : "
                                     ++ show !(toFullNames ty)

  processUnify : RawI -> RawI -> Core ()
  processUnify rawx rawy
      = do (tmx, tyx) <- infer linear [<] rawx
           (tmy, tyy) <- infer linear [<] rawy
           chkConvert replFC [<] tyx tyy
           ures <- unify inTerm replFC [<] tmx tmy
           case constraints ures of
                [] => coreLift $ putStrLn "Success"
                _ => coreLift $ putStrLn "Constraints" -- TODO, print them

  processLogging : LogLevel -> Core ()
  processLogging lvl
      = addLogLevel (Just lvl)

  export
  processCommand : Command -> Core ()
  processCommand (Decl d) = processDecl d
  processCommand (Eval tm) = processEval tm
  processCommand (HNF tm) = processHNF tm
  processCommand (Unify x y) = processUnify x y
  processCommand (Logging x) = processLogging x
  processCommand Quit = pure ()
