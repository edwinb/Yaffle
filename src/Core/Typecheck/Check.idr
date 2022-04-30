module Core.Typecheck.Check

-- Typechecker for raw TT terms

import Core.Context
import Core.Env
import Core.Error
import Core.Evaluate.Convert
import Core.Syntax.Raw
import Core.TT

parameters {auto c : Ref Ctxt Defs}
  export
  infer : {vars : _} ->
          Env Term vars -> RawI -> Core (Term vars, Term vars)

  export
  check : {vars : _} ->
          Env Term vars -> RawC -> Term vars -> Core (Term vars)
  check env (RInf fc tm) exp
      = do (tm', ty') <- infer env tm
           True <- convert env ty' exp
                | False => throw (CantConvert fc !(get Ctxt) env ty' exp)
           pure tm'
  check env (RLam fc n scope) exp = ?todoLam
  check env (RCase fc sc alts) exp = ?todoCase
