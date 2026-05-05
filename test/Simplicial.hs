module Main (main) where

import Data.List
import qualified Data.Map.Strict as M
import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck

import SMCDEL.Language
import SMCDEL.Simplicial.S5
import SMCDEL.Translations.S5
import SMCDEL.Internal.Help
import SMCDEL.Explicit.S5

main :: IO ()
main = hspec $ do
  describe "predefined simplicial examples" $ do
    it "C, X: a knows p_a" $ pointedExampleSM |= K "a" (PrpF (P 1))
    it "C, X: b doesn't know p_a" $ not $ pointedExampleSM |= K "b" (PrpF (P 1))
    it "C, X: b and c don't distributedly know that p_a AND p_b" $
      not $ pointedExampleSM |= Dk ["b", "c"] (conj (PrpF (P 1)) (PrpF (P 2)))
    it "C, X: b and c distributedly know that p_b AND NOT p_c" $
      pointedExampleSM |= Dk ["b", "c"] (conj (PrpF (P 2)) (Neg (PrpF (P 3))))
    it "C, X: all ag distributedly know that p_a" $
      pointedExampleSM |= Dk ["a", "b", "c"] (PrpF (P 1))
    it "C, X: p_a is not common knowledge" $
      not $ pointedExampleSM |= Ck ["a", "b", "c"] (PrpF (P 1))
    it "C, X: after pub annnouncement of p_a, p_a is common knowledge" $ 
      pointedExampleSM |= PubAnnounce (PrpF (P 1)) (Ck ["a", "b", "c"] (PrpF (P 1)))
    it "C', X: p_c is not common knowledge among all ag" $
      not $ (exampleSM2, [1, 2, 3] :: Facet) |= Ck ["a", "b", "c"] (PrpF (P 3))
  describe "sanity and property checks for randomly generated simplicial models" $ do
    prop "generating models works without hanging forever" $
      \m -> withMaxSuccess 10000 $ within 5000 $ (m :: SimplicialModelS5) |= Top
    prop "uses defaultAgents and defaultVocabulary" $ 
      \m -> agentsOf (m :: SimplicialModelS5) `seteq` defaultAgents &&
            vocabOf m `seteq` defaultVocabulary    
    prop "underlying simplicial complex is pure and dim == number of ags" $
      \m -> all (\x -> length x == length (agentsOf m)) (facetsOf (m :: SimplicialModelS5))
    prop "all facets contain all ags" $ 
      \m -> all (\x -> all (\ag -> ag `elem` map (agAt m) x) (agentsOf m)) (facetsOf (m :: SimplicialModelS5))
    prop "simplicial complex is connected" $ 
      \m -> 
        length (facetsOf m) == 1 ||
        all (\f1 -> any (\f2 -> f1 `intersect` f2 /= []) (delete f1 (facetsOf m))) (facetsOf (m :: SimplicialModelS5))
    prop "simplicial complex contains no duplicate facets" $
      \m -> not $ any (\f1 -> any (\f2 -> f1 `seteq` f2) (delete f1 (facetsOf m))) (facetsOf (m :: SimplicialModelS5))
    prop "pointed simplicial model points towards an existing facet" $
      \pm -> snd pm `elem` facetsOf (fst (pm :: PointedSimplicialModelS5))
    prop "multipointed simplicial model points towards existing facets" $
      \pm -> all (\x -> x `elem` facetsOf (fst pm)) (snd (pm :: MultipointedSimplicialModelS5))
    prop "distribution of # of facets and # of intersecting vertices" $
      \m -> 
        let nIntByPair _ [] = []
            nIntByPair x (y : ys) = map (\y -> length (x `intersect` y)) (y : ys) : nIntByPair y ys
            nIntersects [] = []
            nIntersects (x : xs) = concat $ nIntByPair x xs
        in 
          tabulate "# intersects between two facets" (map show (nIntersects (facetsOf m))) $
          tabulate "# facets" [show (length (facetsOf m))] $
          (m :: SimplicialModelS5) |= Top
  describe "validities in S5" $ do
    -- discard test after 200ms if no formula that is Ck/Dk/(Neg) K is found
    prop "Ck ags f --> f" $
      \m (Group ags) f -> discardAfter 200 ((m :: PointedSimplicialModelS5) |= Ck ags f ==> m |= f)
    prop "Dk ags f --> f" $
      \m (Group ags) f -> discardAfter 200 ((m :: PointedSimplicialModelS5) |= Dk ags f ==> m |= f)
    prop "K ag f --> f" $
      \m (Ag ag) f -> discardAfter 200 ((m :: PointedSimplicialModelS5) |= K ag f ==> m |= f)
    prop "K ag f --> K ag (K ag f)" $
      \m (Ag ag) f -> discardAfter 200 ((m :: PointedSimplicialModelS5) |= K ag f ==> m |= K ag (K ag f))
    prop "Neg (K ag f) --> K ag (Neg (K ag f))" $
      \m (Ag ag) f -> discardAfter 200 ((m :: PointedSimplicialModelS5) |= Neg (K ag f) ==> m |= K ag (Neg (K ag f)))
  describe "Ck and Dk properties" $ do
    prop "Ck ag <-> Dk ag" $
      \m (Ag ag) f -> (m :: PointedSimplicialModelS5) |= (Ck [ag] f `Equi` Dk [ag] f)
    prop "Dk Top" $ 
      \m (Group ags) -> (m :: PointedSimplicialModelS5) |= Dk ags Top
    prop "Dk Bottom" $ 
      \m (Group ags) -> not $ (m :: PointedSimplicialModelS5) |= Dk ags Bot
    prop "Ck Top" $ 
      \m (Group ags) -> (m :: PointedSimplicialModelS5) |= Ck ags Top
    prop "Ck Bottom" $ 
      \m (Group ags) -> not $ (m :: PointedSimplicialModelS5) |= Ck ags Bot
    prop "Ck ags f --> K ag f for all ag in ags" $
      \m (Group ags) f ->
        discardAfter 200 $
        (m :: PointedSimplicialModelS5) |= Ck ags f ==> 
        all (\ag -> m |= K ag f) ags
    prop "Ck ags f --> K a (K b f) for all a,b in ags" $
      \m (Group ags) f ->
        discardAfter 200 $
        (m :: PointedSimplicialModelS5) |= Ck ags f ==>
        all (\(a,b) -> m |= K a (K b f)) [(a, b) | a <- ags, b <- ags]
  describe "conversions SM to KrM" $ do
    describe "simpToKripke" $ do
      let x sm = head (facetsOf sm)
          w sm = facetToWorld sm (x sm)
      prop "SM and KrM have same vocabulary" $
        \sm -> vocabOf sm `seteq` vocabOf (simpToKripke sm)
      prop "SM, x |= f <-> KrM, w |= f" $
        \sm f -> ((sm, x sm) |= f) == ((simpToKripke sm, w sm) |= f)
      prop "preserves validity (SM |= f <-> KrM |= f)" $
        \sm f -> sm |= f == simpToKripke sm |= f
      prop "resulting KrM is proper and local" $
        \sm -> isProper (simpToKripke sm) && isLocal (simpToKripke sm)
    describe "simpToKripkePointed" $ do
      prop "SM and KrM have same vocabulary" $
        \pm -> vocabOf pm `seteq` vocabOf (simpToKripkePointed pm)
      prop "(sm, x) |= f <-> (simpToKripkePointed (sm, x))" $ 
        \pm f -> (pm |= f) == (simpToKripkePointed pm |= f)
    describe "simpToKripkeMultipointed" $ do
      prop "SM and KrM have same vocabulary" $
        \pm -> vocabOf pm `seteq` vocabOf (simpToKripkeMultipointed pm)
      prop "(sm, x) |= f <-> (simpToKripkePointed (sm, x))" $ 
        \pm f -> (pm |= f) == (simpToKripkeMultipointed pm |= f)
  describe "conversions KrM to SM" $ do
    describe "kripkeToSimp" $ do
      prop "KrM and SM have same vocabulary" $
        \krm -> vocabOf krm `seteq` vocabOf (kripkeToSimp krm)
      prop "preserves validity (KrM |= f <-> SM |= f)" $
        \krm f -> krm |= f == kripkeToSimp krm |= f
    describe "kripkeToSimpPointed" $ do
      prop "KrM and SM have same vocabulary" $
        \krm -> vocabOf krm `seteq` vocabOf (kripkeToSimpPointed krm)
      prop "KrM, w |= f <-> SM, X |= f" $
        \krm f -> (krm |= f) == (kripkeToSimpPointed krm |= f)
    describe "kripkeToSimpMultipointed" $ do
      prop "KrM and SM have same vocabulary" $
        \krm -> vocabOf krm `seteq` vocabOf (kripkeToSimpMultipointed krm)
      prop "KrM, ws |= f <-> SM, Xs |= f" $
        \krm f -> (krm |= f) == (kripkeToSimpMultipointed krm |= f)
    describe "kripkeToSimpWithMap" $ do
      prop "internalToActual maps all worlds correctly" $
        \krm f -> 
          let
            internalToActual = snd $ kripkeToSimpWithMap krm
            ws = worldsOf krm
            sm = fst $ kripkeToSimpWithMap krm
            equivX = worldToFacet krm internalToActual
          in
            all (\w -> (krm, w) |= f == (sm, equivX w) |= f) ws

-- * Predefined Examples

-- Fig. 4 from proposal (in tests above called C)
exampleSM :: SimplicialModelS5
exampleSM = SMS5
    [[1, 2, 3], [2, 3, 4]]
    (M.fromList [(1, ("a", M.fromList [(P 1, True)])), 
                 (2, ("b", M.fromList [(P 2, True)])), 
                 (3, ("c", M.fromList [(P 3, False)])), 
                 (4, ("a", M.fromList [(P 1, False)]))])

-- Fig. 4 from proposal, pointing towards facet X (C, X)
pointedExampleSM :: PointedSimplicialModelS5
pointedExampleSM = (exampleSM, [1, 2, 3] :: Facet)

-- C' from Example 22 in [Dit+22] (p. 32)
exampleSM2 :: SimplicialModelS5
exampleSM2 = SMS5
    [[1, 2, 3], [2, 3, 4], [3, 4, 5], [5, 6, 7], [6, 7, 8], [7, 8, 9]]
    (M.fromList [(1, ("a", M.fromList [(P 1, False)])), 
                 (2, ("b", M.fromList [(P 2, True)])), 
                 (3, ("c", M.fromList [(P 3, True)])), 
                 (4, ("a", M.fromList [(P 1, True)])), 
                 (5, ("b", M.fromList [(P 2, False)])), 
                 (6, ("a", M.fromList [(P 1, True)])), 
                 (7, ("c", M.fromList [(P 3, False)])), 
                 (8, ("b", M.fromList [(P 2, True)])), 
                 (9, ("a", M.fromList [(P 1, False)]))])
