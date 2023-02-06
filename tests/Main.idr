module Main

import Test.Golden


------------------------------------------------------------------------
-- CSP instance `TestPool`s

nqueensTests : TestPool
nqueensTests = MkTestPool "NQueens" [] Nothing
  [  "4Queens"
  --,  "6Queens"
  --,  "8Queens"
  --, "10Queens"
  ]

langfordsTests : TestPool
langfordsTests = MkTestPool "Langford's" [] Nothing
  [ --"langfords2_3"
  --, "langfords2_3"
  -- only comment in the thing below if you need a coffee break; they take TIME
  --- , "langfords3_9"
  --- , "langfords3_10"
  ]


------------------------------------------------------------------------
-- Test runner

-- blatently copied from idris-lang/Idris2/tests/Main.idr
main : IO ()
main = runner $
  [ testPaths "nqueens" nqueensTests
  , testPaths "langfords" langfordsTests
  ]
  where
    testPaths : String -> TestPool -> TestPool
    testPaths dir = { testCases $= map ((dir ++ "/") ++) }

