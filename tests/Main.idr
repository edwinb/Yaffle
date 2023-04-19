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
      "record001", "record002", "record003",
      "rewrite001",
      "with001",
      -- Below are things that don't test anything specific, but are useful exercises
      "example001"
      -- "papers001"  -- disabled since it doesn't work in Idris 2 either, and will
                      -- be tested when building libraries
    ]

idrisTestsBasic : TestPool
idrisTestsBasic = MkTestPool "Fundamental language features" [] Nothing
      -- Fundamental language features
      ["basic001", "basic002", "basic003", "basic004", "basic005",
       "basic006", "basic007", "basic008", "basic009", "basic010",
       "basic011", "basic012", "basic013", "basic014", "basic015",
       "basic016", "basic017", "basic018", "basic019", "basic020",
--        "basic021", "basic022", "basic023", "basic024", "basic025",
--        "basic026", "basic027", "basic028", "basic029", "basic030",
--        "basic031", "basic032", "basic033", "basic034", "basic035",
--        "basic036", "basic037", "basic038", "basic039", "basic040",
--        "basic041", "basic042", "basic043", "basic044", "basic045",
--        "basic046", "basic047",             "basic049", "basic050",
--        "basic051", "basic052", "basic053", "basic054", "basic055",
--        "basic056", "basic057", "basic058", "basic059", "basic060",
--        "basic061", "basic062", "basic063", "basic064", "basic065",
--        "basic066", "basic067", "basic068", "basic069"]
--        "idiom001",
       "dotted001",
       "rewrite001",
       "interpolation001", "interpolation002", "interpolation003",
       "interpolation004"]

idrisTestsRegression : TestPool
idrisTestsRegression = MkTestPool "Various regressions" [] Nothing
       -- Miscellaneous regressions
      ["reg001", "reg002", "reg003", "reg004", "reg005", "reg006", "reg007",
       "reg008", "reg009", "reg010", "reg011", "reg012", "reg013", "reg014",
       "reg015", "reg016", "reg017", "reg018", "reg019", "reg020", "reg021",
       "reg022", "reg023", "reg024", "reg025", "reg026", "reg027", "reg028",
       "reg029", "reg030", "reg031", "reg032", "reg033", "reg034", "reg035",
       "reg036", "reg037", "reg038", "reg039", "reg040", "reg041", "reg042",
       "reg043", "reg044", "reg045", "reg046", "reg047", "reg048", "reg049",
       "reg050", "reg051"
      ]

chezTests : TestPool
chezTests = MkTestPool "Chez backend" [] (Just Chez)
    [ "chez001", "chez002", "chez003", "chez004", "chez005", "chez006"
    , "chez007", "chez008", "chez009", "chez010", "chez011", "chez012"
    , "chez013", "chez014", "chez015", "chez016", "chez017", "chez018"
    , "chez019", "chez020", "chez021", "chez022", "chez023", "chez024"
    , "chez025", "chez026", "chez027", "chez028", "chez029", "chez030"
    , "chez031", "chez032", "chez033", "chez034", "chez035"
    , "futures001"
    , "bitops"
    , "casts"
    , "constfold" --, "constfold2", "constfold3"
    , "memo"
    , "newints"
    , "integers"
    , "nat2fin"
    , "inlineiobind"
    , "semaphores001"
    , "semaphores002"
    , "perf001"
    , "reg001"
    , "buffer001"
    ]

failingTests : TestPool
failingTests = MkTestPool "Failing tests (PRs welcome)" [] Nothing
  [ "unify004"
  ]

main : IO ()
main
    = runner $ [ testPaths "tt"     ttTests
               , testPaths "yaffle" yaffleTests
               , testPaths "idris2" idrisTestsBasic
               , testPaths "idris2" idrisTestsRegression
               , testPaths "chez"   chezTests
               , testPaths "tt"     failingTests]
  where
    testPaths : String -> TestPool -> TestPool
    testPaths dir = { testCases $= map ((dir ++ "/") ++) }
