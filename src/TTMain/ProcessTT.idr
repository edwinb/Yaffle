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
-- At this stage, it's handy to do these at erased mulitiplicity,
-- then we don't need to faff about with options to set evaluation multiplicity
-- in order to test unification etc properly.
  processEval : RawI -> Core ()
  processEval rawtm
      = do (tm, ty) <- infer erased [<] rawtm
           tmnf <- normalise [<] tm
           coreLift $ putStrLn $ show !(toFullNames tmnf) ++ " : "
                                     ++ show !(toFullNames ty)

  processHNF : RawI -> Core ()
  processHNF rawtm
      = do (tm, ty) <- infer erased [<] rawtm
           tmnf <- normaliseHNF [<] tm
           coreLift $ putStrLn $ show !(toFullNames tmnf) ++ " : "
                                     ++ show !(toFullNames ty)

  processCheck : RawI -> Core ()
  processCheck rawtm
      = do (tm, ty) <- infer erased [<] rawtm
           tynf <- normalise [<] ty
           coreLift $ putStrLn $ show !(toFullNames tm) ++ " : "
                                     ++ show !(toFullNames tynf)

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
  processCommand (Check tm) = processCheck tm
  processCommand (Unify x y) = processUnify x y
  processCommand (Logging x) = processLogging x
  processCommand Quit = pure ()
