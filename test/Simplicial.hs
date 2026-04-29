-- {-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, FlexibleContexts #-}

module Main (main) where

import Data.List
import qualified Data.Map.Strict as M
import Test.Hspec
import Test.Hspec.QuickCheck

import SMCDEL.Language
import SMCDEL.Simplicial.S5
import SMCDEL.Translations.S5
import SMCDEL.Internal.Help
import SMCDEL.Explicit.S5

main :: IO ()
main = hspec $ do
  describe "predefined simplicial examples" $ do
    it "C, X: a knows p_a" $ pointedExampleSM |= (K "a" (PrpF (P 1)))
    it "C, X: b doesn't know p_a" $ not $ pointedExampleSM |= (K "b" (PrpF (P 1)))
    it "C, X: b and c don't distributedly know that p_a AND p_b" $
      not $ pointedExampleSM |= (Dk ["b", "c"] (conj (PrpF (P 1)) (PrpF (P 2))))
    it "C, X: b and c distributedly know that p_b AND NOT p_c" $
      pointedExampleSM |= (Dk ["b", "c"] (conj (PrpF (P 2)) (Neg (PrpF (P 3)))))
    it "C, X: all ag distributedly know that p_a" $
      pointedExampleSM |= (Dk ["a", "b", "c"] (PrpF (P 1)))
    it "C, X: p_a is not common knowledge" $
      not $ pointedExampleSM |= (Ck ["a", "b", "c"] (PrpF (P 1)))
    it "C, X: after pub annnouncement of p_a, p_a is common knowledge" $ 
      pointedExampleSM |= (PubAnnounce (PrpF (P 1)) (Ck ["a", "b", "c"] (PrpF (P 1))))
    it "C', X: p_c is not common knowledge among all ag" $
      not $ (exampleSM2, [1, 2, 3] :: Facet) |= (Ck ["a", "b", "c"] (PrpF (P 3)))
  describe "sanity checks for random simplicial models" $ do
    prop "sc is pure and dim == number of ags" $
      \m -> all (\x -> length x == length (agentsOf m)) (facetsOf (m :: SimplicialModelS5))
    prop "all facets contain all ags" $ 
      \m -> all (\x -> (all (\ag -> ag `elem` map (agAt m) x) (agentsOf m))) (facetsOf (m :: SimplicialModelS5))
    prop "simplicial complex is connected" $ 
      \m -> (length (facetsOf m)) == 1 ||
        all (\f1 -> any (\f2 -> f1 `intersect` f2 /= []) (delete f1 (facetsOf m))) (facetsOf (m :: SimplicialModelS5))
    prop "uses defaultAgents and defaultVocabulary" $ 
      \m -> (agentsOf (m :: SimplicialModelS5)) `seteq` defaultAgents && (vocabOf m) `seteq` defaultVocabulary
    prop "simplicial complex contains no facet twice" $
      \m -> not $ any (\f1 -> any (\f2 -> f1 `seteq` f2) (delete f1 (facetsOf m))) (facetsOf (m :: SimplicialModelS5))
    prop "pointed simplicial model points towards an existing facet" $
      \pm -> (snd pm) `elem` (facetsOf (fst (pm :: PointedSimplicialModelS5)))
    prop "multipointed simplicial model points towards existing facets" $
      \pm -> all (\x -> x `elem` (facetsOf (fst pm))) (snd (pm :: MultipointedSimplicialModelS5))
  describe "validities in S5" $ do
    let x m = head (facetsOf m)
    prop "Ck ags f --> f" $
      \m (Group ags) f -> (m :: SimplicialModelS5, x m) |= (Ck ags f `Impl` f)
    prop "Dk ags f --> f" $
      \m (Group ags) f -> (m :: SimplicialModelS5, x m) |= (Dk ags f `Impl` f)
    prop "K ag f --> f" $
      \m (Ag ag) f -> (m :: SimplicialModelS5, x m) |= (K ag f `Impl` f)
    prop "K ag f --> K ag (K ag f)" $
      \m (Ag ag) f -> (m :: SimplicialModelS5, x m) |= (K ag f `Impl` K ag (K ag f))
    prop "Neg (K ag f) --> K ag (Neg (K ag f))" $
      \m (Ag ag) f -> (m :: SimplicialModelS5, x m) |= (Neg (K ag f) `Impl` K ag (Neg (K ag f)))
  describe "Ck and Dk properties" $ do
    let x m = head (facetsOf m)
    prop "Ck ag <-> Dk ag" $
      \m (Ag ag) f -> (m :: SimplicialModelS5, x m) |= (Ck [ag] f `Equi` Dk [ag] f)
    prop "Dk Top" $ 
      \m (Group g) -> (m :: SimplicialModelS5, x m) |= (Dk g Top)
    prop "Dk Bottom" $ 
      \m (Group g) -> not $ (m :: SimplicialModelS5, x m) |= (Dk g Bot)
    prop "Ck Top" $ 
      \m (Group g) -> (m :: SimplicialModelS5, x m) |= (Ck g Top)
    prop "Ck Bottom" $ 
      \m (Group g) -> not $ (m :: SimplicialModelS5, x m) |= (Ck g Bot)
  describe "conversions SM tos KrM" $ do
    describe "simpToKripke" $ do
      let x sm = head (facetsOf sm)
          w sm = facetToWorld sm (x sm)
      prop "SM and KrM have same vocabulary" $
        \sm -> (vocabOf sm `seteq` vocabOf (simpToKripke sm))
      prop "SM, x |= f <-> KrM, w |= f" $
        \sm f -> ((sm, x sm) |= f) == ((simpToKripke sm, w sm) |= f)
      prop "resulting KrM is proper and local" $
        \sm -> isProper (simpToKripke sm) && isLocal (simpToKripke sm)
    describe "simpToKripkePointed" $ do
      prop "SM and KrM have same vocabulary" $
        \pm -> (vocabOf pm `seteq` vocabOf (simpToKripkePointed pm))
      prop "(sm, x) |= f <-> (simpToKripkePointed (sm, x))" $ 
        \pm f -> (pm |= f) == ((simpToKripkePointed pm) |= f)
    describe "simpToKripkeMultipointed" $ do
      prop "SM and KrM have same vocabulary" $
        \pm -> (vocabOf pm `seteq` vocabOf (simpToKripkeMultipointed pm))
      prop "(sm, x) |= f <-> (simpToKripkePointed (sm, x))" $ 
        \pm f -> (pm |= f) == ((simpToKripkeMultipointed pm) |= f)
  describe "conversions KrM to SM" $ do
    describe "kripkeToSimp" $ do
      prop "KrM and SM have same vocabulary" $
        \krm -> (vocabOf krm `seteq` vocabOf (kripkeToSimp krm))
    describe "kripkeToSimpPointed" $ do
      prop "KrM and SM have same vocabulary" $
        \krm -> (vocabOf krm `seteq` vocabOf (kripkeToSimpPointed krm))
      prop "KrM, w |= f <-> SM, X |= f" $
        \krm f -> (krm |= f) == ((kripkeToSimpPointed krm) |= f)
    describe "kripkeToSimpMultipointed" $ do
      prop "KrM and SM have same vocabulary" $
        \krm -> (vocabOf krm `seteq` vocabOf (kripkeToSimpMultipointed krm))
      prop "KrM, ws |= f <-> SM, Xs |= f" $
        \krm f -> (krm |= f) == ((kripkeToSimpMultipointed krm) |= f)
