module Core.Binary

import public Core.Binary.Prims
import Core.Core

import System.File

||| Get a file's modified time. If it doesn't exist, return 0 (UNIX Epoch)
export
modTime : String -> CoreE err Int
modTime fname
  = do Right f <- coreLift $ openFile fname Read
         | Left err => pure 0 -- Beginning of Time :)
       Right t <- coreLift $ fileModifiedTime f
         | Left err => do coreLift $ closeFile f
                          pure 0
       coreLift $ closeFile f
       pure t
