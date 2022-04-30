module Core.Typecheck.Check

-- Typechecker for raw TT terms

import Core.Context
import Core.Env
import Core.Error
import Core.Syntax.Raw
import Core.TT

parameters {auto c : Ref Ctxt Defs}
  export
  infer : {vars : _} ->
          Env Term vars -> RawI -> Core (Term vars, Term vars)

  export
  check : {vars : _} ->
          Env Term vars -> RawC -> Term vars -> Core (Term vars)
