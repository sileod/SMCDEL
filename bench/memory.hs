module Main where

import Data.List
import Weigh

import SMCDEL.Language
import SMCDEL.Examples.MuddyChildren
import qualified SMCDEL.Symbolic.S5
import qualified SMCDEL.Symbolic.S5_DD

main :: IO ()
main =
  print $ findNumberCheckPAL 5 5
  {-
  mainWith $ do
  mapM_
    ( \ (n, (label,method)) -> func (label ++ show n) (uncurry method) (n,n))
    [ (n,lm) | lm <- [("DD", findNumberDD), ("checkPAL", findNumberCheckPAL)], n <- [3..6] ]
  -}


-- | The formula to be checked.
checkForm :: Int -> Int -> Form
checkForm n 0 = nobodyknows n
checkForm n k = PubAnnounce (nobodyknows n) (checkForm n (k-1))

-- | Generic function to solve the puzzle.
-- This will be instantiated with different `evalViaBdd` functions for different BDD packages.
findNumberWith :: (Int -> Int -> a, a -> Form -> Bool) -> Int -> Int -> Int
findNumberWith (start,evalfunction) n m = k where
  k | loop 0 == (m-1) = m-1
    | otherwise       = error $ "wrong Muddy Children result: " ++ show (loop 0)
  loop count = if evalfunction (start n m) (PubAnnounce (father n) (checkForm n count))
    then loop (count+1)
    else count

mudPs :: Int -> [Prp]
mudPs n = [P 1 .. P n]

findNumberDD :: Int -> Int -> Int
findNumberDD = findNumberWith (ddMudScnInit,SMCDEL.Symbolic.S5_DD.evalViaBdd) where
  ddMudScnInit n m = ( SMCDEL.Symbolic.S5_DD.KnS (mudPs n) (SMCDEL.Symbolic.S5_DD.boolBddOf Top) [ (show i,delete (P i) (mudPs n)) | i <- [1..n] ], mudPs m )

findNumberCheckPAL :: Int -> Int -> Int
findNumberCheckPAL = findNumberWith (cacMudScnInit,SMCDEL.Symbolic.S5.evalViaCheckPAL) where
  cacMudScnInit n m = ( SMCDEL.Symbolic.S5.KnS (mudPs n) (SMCDEL.Symbolic.S5.boolBddOf Top) [ (show i,delete (P i) (mudPs n)) | i <- [1..n] ], mudPs m )
