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
      "compile001", "compile002",
      "coverage001",
      "qtt001", "qtt002", "qtt003", "qtt004",
      "record001", "record002",
      "rewrite001",
      "with001",
      -- Below are things that don't test anything specific, but are useful exercises
      "example001"
      -- "papers001"  -- disabled since it doesn't work in Idris 2 either, and will
                      -- be tested when building libraries
    ]

idrisTestsRegression : TestPool
idrisTestsRegression = MkTestPool "Various regressions" [] Nothing
       -- Miscellaneous regressions
      ["reg001", "reg002", "reg003", "reg004", "reg005", "reg006", "reg007"
--        "reg008", "reg009", "reg010", "reg011", "reg012", "reg013", "reg014",
--        "reg015", "reg016", "reg017", "reg018", "reg019", "reg020", "reg021",
--        "reg022", "reg023", "reg024", "reg025", "reg026", "reg027", "reg028",
--        "reg029", "reg030", "reg031", "reg032", "reg033", "reg034", "reg035",
--        "reg036", "reg037", "reg038", "reg039", "reg040", "reg041", "reg042",
--        "reg043", "reg044", "reg045", "reg046", "reg047", "reg048", "reg049",
--        "reg050"
      ]

failingTests : TestPool
failingTests = MkTestPool "Failing tests (PRs welcome)" [] Nothing
  [ "unify004"
  ]

main : IO ()
main
    = runner $ [ testPaths "tt"     ttTests
               , testPaths "yaffle" yaffleTests
               , testPaths "idris2" idrisTestsRegression
               , testPaths "tt"     failingTests]
  where
    testPaths : String -> TestPool -> TestPool
    testPaths dir = { testCases $= map ((dir ++ "/") ++) }
