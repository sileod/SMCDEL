{- | Solving Cheryl's Sudoku using DEMO-S5

A puzzle made by /Elytron/:
<https://logic-masters.de/Raetselportal/Raetsel/zeigen.php?chlang=en&id=000NMV>
-}

module SMCDEL.Examples.CherylSudoku where

import Data.List

import SMCDEL.Explicit.DEMO_S5 as DEMO_S5

-- | General Type for any Sudokus
type Sudoku = [[Int]]

type Coord = (Int,Int)

(?) :: [[Int]] -> Coord -> Int
(?) rs (y,x) = (rs !! y) !! x

allCoords :: [Coord]
allCoords = [ (y,x) | y <- [0,1,2,3], x <- [0,1,2,3] ]

check :: [Int] -> Bool
check = (==) [1..4] . sort

-- | All 4×4 Sudokus.
-- There are 288 possibilities, see <https://oeis.org/A107739>.
fourByFours :: [ Sudoku ]
fourByFours = [ [w,x,y,z]
              | w <- rows , x <- rows , y <- rows , z <- rows
              , correctCols [w,x,y,z], correctSubsquares [w,x,y,z] ] where
  rows = permutations [1..4]
  correctCols rs = and [ check (map (!! k) rs) | k <- [0..3] ]
  correctSubsquares rs = all (check . map (rs ?))
    [ [ (0,0), (0,1), (1,0), (1,1) ]
    , [ (0,2), (0,3), (1,2), (1,3) ]
    , [ (2,0), (2,1), (3,0), (3,1) ]
    , [ (2,2), (2,3), (3,2), (3,3) ] ]

-- | Digits in cages sum up to the value in the top left and may repeat if allowed by other rules.
subPart :: Char -> [Coord]
subPart 'A' = [ (1,1), (2,0), (2,1) ]
subPart 'B' = [ (3,2), (3,3) ]
subPart 'C' = [ (1,2), (2,2), (2,3) ]
subPart 'D' = [ (0,3), (1,3) ]
subPart _ = undefined

sumPart :: Char -> Sudoku -> Int
sumPart c rs = sum [ rs ? co | co <- subPart c ]

albert, bertrand, carl, david :: DEMO_S5.Agent
albert = DEMO_S5.Ag 1
bertrand = DEMO_S5.Ag 2
carl = DEMO_S5.Ag 3
david = DEMO_S5.Ag 4

-- | Albert, Bertrand, Carl and David are perfectly logical Sudoku solvers.
allAgs :: [DEMO_S5.Agent]
allAgs = [albert, bertrand, carl, david]

start,step1,step2,step3,step4,step5 :: DEMO_S5.EpistM Sudoku

-- | Initial model.
-- Each solver is privately told the value of one variable:
-- Albert is told A, Bertrand is told B, Carl is told C, and David is told D.
start = DEMO_S5.Mo worlds agents [] rels points where
  worlds = fourByFours -- each 4x4 Sudoku is a possible world
  agents = [albert, bertrand, carl, david] -- four agents
  rels = [ (albert  , groupOn (sumPart 'A') $ sortOn (sumPart 'A') worlds)
         , (bertrand, groupOn (sumPart 'B') $ sortOn (sumPart 'B') worlds)
         , (carl    , groupOn (sumPart 'C') $ sortOn (sumPart 'C') worlds)
         , (david   , groupOn (sumPart 'D') $ sortOn (sumPart 'D') worlds) ]
  points = worlds
  -- copied from Data.List.Extra in the "extra" library:
  groupOn :: Eq k => (a -> k) -> [a] -> [[a]]
  groupOn g = groupBy ((==) `on2` g)
    where (.*.) `on2` f = \x -> let fx = f x in \y -> fx .*. f y

canPlace :: Agent -> Coord -> DemoForm Sudoku
canPlace i co = Disj [ Kl i (Fun ((== k) . (? co))) | k <- [1..4] ]

canPlaceSomeDigit :: Agent -> DemoForm Sudoku
canPlaceSomeDigit i = Disj [ canPlace i co | co <- allCoords ]

canPlaceSet :: Agent -> [Coord] -> DemoForm Sudoku
canPlaceSet i coos = Conj (map (canPlace i) coos)

canPlaceAtLeast :: Agent -> Int -> DemoForm Sudoku
canPlaceAtLeast i n =
  Disj [ canPlaceSet i coos
       | coos <- subsequences allCoords
       , length coos == n ]

knowsMore :: Agent -> Agent -> DemoForm Sudoku
knowsMore a b = Disj [ Conj [ canPlaceAtLeast a n
                            , Ng (canPlaceAtLeast b n) ]
                     | n <- [1..16] ]

-- | Albert: "Nobody here can place any digits yet."
step1 = start `updPa` Kn albert (Conj (map (Ng . canPlaceSomeDigit) allAgs))

-- | Bertrand: "Well, now I do."
step2 = step1 `updPa` canPlaceSomeDigit bertrand

-- | Carl: "No one else was told the same number as I was."
step3 = step2 `updPa` Kl carl (Fun fn) where
  fn rs = sumPart 'C' rs `notElem` map (`sumPart` rs) "ABD"

-- | David: "Someone here knows more digits than I do."
step4 = step3 `updPa` Kn david (Disj [ knowsMore i david | i <- allAgs \\ [david] ])

-- | After this exchange, one of the four solvers completes the Sudoku.
step5 = step4 `updPa` Disj [ canPlaceAtLeast i 16 | i <- allAgs ]

whoKnows :: [DEMO_S5.Agent]
whoKnows = filter (\i -> isTrue newM (canPlaceAtLeast i 16)) allAgs where
  (Mo worlds ags val accs _) = step4
  newM = Mo worlds ags val accs (worldsOf step5)

{- $

>>> length $ worldsOf $ start
288

>>> length $ worldsOf $ step1
120

>>> length $ worldsOf $ step2
24

>>> length $ worldsOf $ step3
12

>>> length $ worldsOf $ step4
6

Now run `worldsOf step5` and `whoKnows` to solve the puzzle.
Note that it can take up to two minutes, depending on your CPU.

-}
