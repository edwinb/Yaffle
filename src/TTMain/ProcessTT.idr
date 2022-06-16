module TTMain.ProcessTT

import Core.Context
import Core.Env
import Core.Error
import Core.Evaluate
import Core.Syntax.Decls
import Core.Syntax.Raw
import Core.Check.Typecheck
import Core.Unify.State

parameters {auto c : Ref Ctxt Defs} {auto u : Ref UST UState}
  processEval : RawI -> Core ()
  processEval rawtm
      = do (tm, ty) <- infer top [<] rawtm
           tmnf <- normalise [<] tm
           coreLift $ putStrLn $ show !(toFullNames tmnf) ++ " : "
                                     ++ show !(toFullNames ty)

  processHNF : RawI -> Core ()
  processHNF rawtm
      = do (tm, ty) <- infer top [<] rawtm
           tmnf <- normaliseHNF [<] tm
           coreLift $ putStrLn $ show !(toFullNames tmnf) ++ " : "
                                     ++ show !(toFullNames ty)

  export
  processCommand : Command -> Core ()
  processCommand (Decl d) = processDecl d
  processCommand (Eval tm) = processEval tm
  processCommand (HNF tm) = processHNF tm
  processCommand Quit = pure ()
