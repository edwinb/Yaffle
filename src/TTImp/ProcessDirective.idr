module TTImp.ProcessDirective

import Core.Context
import Core.Metadata
import Core.Unify.State

import TTImp.TTImp

export
processDirective :
           {auto c : Ref Ctxt Defs} ->
           {auto m : Ref MD Metadata} ->
           {auto u : Ref UST UState} ->
           FC -> Directive -> Core ()
processDirective fc (PairNames p f s) = setPair fc p f s
processDirective fc (RewriteName rw eq) = setRewrite fc rw eq
