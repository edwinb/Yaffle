module TTMain.ProcessTT

import Core.Context
import Core.Env
import Core.Error
import Core.Evaluate
import Core.Syntax.Raw
import Core.Typecheck.Check

parameters {auto c : Ref Ctxt Defs}
  processDecl : RawDecl -> Core ()
  processDecl d = throw (InternalError "processDecl not implemented")

  processEval : RawI -> Core ()
  processEval rawtm
      = do (tm, ty) <- infer [] rawtm
           tmnf <- normalise [] tm
           tynf <- normalise [] ty

           coreLift $ putStrLn $ show tmnf ++ " : " ++ show tynf

  export
  processCommand : Command -> Core ()
  processCommand (Decl d) = processDecl d
  processCommand (Eval tm) = processEval tm
