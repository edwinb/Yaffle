module Test.TryEval

import Core.Context
import Core.Core
import Core.Env
import Core.Error
import Core.Evaluate.Normalise
import Core.Evaluate.Quote
import Core.Evaluate.Value
import Core.InitPrimitives
import Core.Primitives
import Core.TT

var : String -> Name
var = UN . Basic

nat : Term vs
nat = Ref EmptyFC (TyCon 0) (var "Nat")

zCon : Term vs
zCon = Ref EmptyFC (DataCon 0 0) (var "Z")

sCon : Term vs
sCon = Ref EmptyFC (DataCon 1 1) (var "S")

plusC : Term []
plusC = Bind EmptyFC (var "x") (Lam EmptyFC RigW Explicit nat) $
        Bind EmptyFC (var "y") (Lam EmptyFC RigW Explicit nat) $
        Case EmptyFC (Local EmptyFC Nothing _ (Later First)) nat $
        [ConCase (var "Z") 0 (RHS (Local EmptyFC Nothing _ First)),
         ConCase (var "S") 1 (Arg (var "k")
             (RHS (apply EmptyFC sCon
                     [apply EmptyFC (Ref EmptyFC Func (var "plus"))
                            [Local EmptyFC Nothing _ First,
                             Local EmptyFC Nothing _ (Later First)]])))]

doTryEval : Core ()
doTryEval
    = do defs <- initDefs
         c <- newRef Ctxt defs
         addPrimitives
         let plusdef = newDef EmptyFC (var "plus") RigW (Erased EmptyFC False)
                              Public
                              (Function (MkFnInfo False) plusC)
         ignore $ addDef (var "plus") plusdef
         let exp = apply EmptyFC (Ref EmptyFC Func (var "plus"))
                         [apply EmptyFC sCon [apply EmptyFC sCon [zCon]],
                          apply EmptyFC sCon [apply EmptyFC sCon [zCon]]]
         coreLift $ putStrLn "Ready"
         val <- nf [] exp
         tm <- quoteNF [] val
         coreLift $ printLn tm

         val <- nf [] (apply EmptyFC (Ref EmptyFC Func (opName (Add IntegerType)))
                             [PrimVal EmptyFC (BI 40),
                              PrimVal EmptyFC (BI 54)])
         tm <- quoteNF [] val
         coreLift $ printLn tm

tryEval : IO ()
tryEval = coreRun doTryEval
               (\err : Error => putStrLn "Uncaught error")
               (\res => pure ())

