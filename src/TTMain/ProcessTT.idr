module TTMain.ProcessTT

import Core.Context
import Core.Env
import Core.Error
import Core.Evaluate
import Core.Syntax.Decls
import Core.Syntax.Raw
import Core.Typecheck.Check

parameters {auto c : Ref Ctxt Defs}
  processEval : RawI -> Core ()
  processEval rawtm
      = do (tm, ty) <- infer top [] rawtm
           tmnf <- normalise [] tm
           coreLift $ putStrLn $ show tmnf ++ " : " ++ show ty

  processHNF : RawI -> Core ()
  processHNF rawtm
      = do (tm, ty) <- infer top [] rawtm
           tmnf <- normaliseHNF [] tm
           coreLift $ putStrLn $ show tmnf ++ " : " ++ show ty

  export
  processCommand : Command -> Core ()
  processCommand (Decl d) = processDecl d
  processCommand (Eval tm) = processEval tm
  processCommand (HNF tm) = processHNF tm
  processCommand Quit = pure ()
