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
     [ "basic001" ]

main : IO ()
main
    = runner $ [ testPaths "tt" ttTests ]
  where
    testPaths : String -> TestPool -> TestPool
    testPaths dir = { testCases $= map ((dir ++ "/") ++) }
