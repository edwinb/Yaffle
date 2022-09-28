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
     [ "basic001", "basic002", "basic003", "basic004", "basic005",
       "linear001", "linear002", "linear003", "linear004", "linear005",
       "presence001",
       "unify001", "unify002", "unify003"]

failingTests : TestPool
failingTests = MkTestPool "Failing tests (PRs welcome)" [] Nothing
  [ "unify004"
  ]

main : IO ()
main
    = runner $ [ testPaths "tt" ttTests
               , testPaths "tt" failingTests]
  where
    testPaths : String -> TestPool -> TestPool
    testPaths dir = { testCases $= map ((dir ++ "/") ++) }
