module Main

import System
import System.Directory
import System.File

import Test.Golden

%default covering

------------------------------------------------------------------------
-- Test cases

ttTests : TestPool
ttTests = MkTestPool "TT" [] Nothing
     [ "basic001", "basic002", "basic003", "basic004",
       "linear001", "linear002", "linear003", "linear004",
       "relevance001",
       "unify001", "unify002", "unify003" ]

main : IO ()
main
    = runner $ [ testPaths "tt" ttTests ]
  where
    testPaths : String -> TestPool -> TestPool
    testPaths dir = { testCases $= map ((dir ++ "/") ++) }
