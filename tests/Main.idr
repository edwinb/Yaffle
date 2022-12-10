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
       "linear001", "linear002", "linear003", "linear004", "linear005", "linear006",
       "presence001", "presence002",
       "unify001", "unify002", "unify003",
       "patterns001", "patterns002",
       "sizechange001",
       "search001", "search002"]

yaffleTests = MkTestPool "Yaffle" [] Nothing
    [ "basic001", "basic002", "basic003",
      "case001",
      "qtt001", "qtt002",
      "record001", "record002",
      "rewrite001",
      "with001",
      -- Below are things that don't test anything specific, but are useful exercises
      "example001",
      "papers001" ]

failingTests : TestPool
failingTests = MkTestPool "Failing tests (PRs welcome)" [] Nothing
  [ "unify004"
  ]

main : IO ()
main
    = runner $ [ testPaths "tt"     ttTests
               , testPaths "yaffle" yaffleTests
               , testPaths "tt"     failingTests]
  where
    testPaths : String -> TestPool -> TestPool
    testPaths dir = { testCases $= map ((dir ++ "/") ++) }
