module Core.TTCFile

import Core.Binary
import Core.Context
import Core.Core

record TTCFile extra (mode : BinaryMode) where
  constructor MkTTCFile
  version : Int
  totalReq : TotalReq
  sourceHash : Maybe String
  ifaceHash : Int
  importHashes : List (Namespace, Int)
  incData : List (CG, String, List String)
  context : List (Name, Binary mode)
  userHoles : List Name
  autoHints : List (Name, Bool)
  typeHints : List (Name, Name, Bool)
  imported : List (ModuleIdent, Bool, Namespace)
  nextVar : Int
  currentNS : Namespace
  nestedNS : List Namespace
  pairnames : Maybe PairNames
  rewritenames : Maybe RewriteNames
  primnames : PrimNames
  namedirectives : List (Name, List String)
  cgdirectives : List (CG, String)
  transforms : List (Name, Transform)
  foreignExports : List (Name, (List (String, String)))
  extraData : extra
