module Util where

import           Test.CoCo

printOutput :: [Observation] -> IO ()
printOutput obs = do
  putStrLn "-- compact"
  prettyPrint (defaultPPROpts { pprDejaFu = Nothing }) obs
  putStrLn "\n-- plain"
  prettyPrint (defaultPPROpts { pprDejaFu = Just Plain }) obs
  putStrLn "\n-- hunit/tasty"
  prettyPrint (defaultPPROpts { pprDejaFu = Just HUnit }) obs
