module Core.Evaluate

import Core.Context
import Core.Env
import Core.Error
import public Core.Evaluate.Normalise
import public Core.Evaluate.Quote
import public Core.Evaluate.Value
import Core.TT

parameters {auto c : Ref Ctxt Defs}
  export
  normalise : {vars : _} ->
              Env Term vars -> Term vars -> Core (Term vars)
  normalise env tm
      = do val <- nf env tm
           quoteNF env val
