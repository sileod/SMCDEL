{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, FlexibleContexts #-}

{-
Based on definitions from:

- [Dit+22]
  Hans van Ditmarsch, Éric Goubault, Jérémy Ledent, and Sergio Rajsbaum.
  “Knowledge and Simplicial Complexes”. In: Philosophy of Computing. Edited
  by Björn Lundgren and Nancy Abigail Nuñez Hernández. Cham: Springer In-
  ternational Publishing, 2022, pages 1–50. ISBN: 978-3-030-75267-5

-}

module SMCDEL.Simplicial.S5 where

import Data.List (intersect, nub)
import qualified Data.Map.Strict as M

import SMCDEL.Language

-- | A vertex is represented by an integer
type Vert = Int

-- | A facet is a list of vertices
type Facet = [Vert] -- TODO: implement as sets

-- | A simplicial complex is represented by a list of facets
type SimplicialComplex = [Facet] -- TODO: implement as sets

-- | The colouring function Chi is represented by a map from vertices to agents
type Colours = M.Map Vert Agent

-- | A valuation is a map from vertices to explicit assignments (maps from propositions to Booleans)
type Valuation = M.Map Vert (M.Map Prp Bool)

data SimplicialModelS5 = SMS5 SimplicialComplex Colours Valuation deriving (Eq, Show)

class HasFacets a where
    facetsOf :: a -> [Facet]

instance HasFacets SimplicialComplex where
    facetsOf sc = sc

instance HasFacets SimplicialModelS5 where
    facetsOf (SMS5 sc _ _) = sc

instance HasVocab SimplicialModelS5 where
   vocabOf (SMS5 _ _ val) = nub ((concatMap M.keys . M.elems) val)

instance HasAgents SimplicialModelS5 where
    agentsOf (SMS5 _ col _) = nub (M.elems col)

instance Semantics SimplicialModelS5 where
    isTrue sm form = all (\x -> eval (sm, x) form) (facetsOf sm)

instance Pointed SimplicialModelS5 Facet where
type PointedSimplicialModelS5 = (SimplicialModelS5, Facet)

instance Semantics PointedSimplicialModelS5 where
    isTrue = eval

-- | Get a list of variables that are true in a given vertex
getLocalVar :: SimplicialModelS5 -> Vert -> [Prp]
getLocalVar (SMS5 _ _ val) vert = case M.lookup vert val of
    Nothing -> error "vertex not in SC"
    Just assigns -> (M.keys . M.filter id) assigns

-- | Get a list of variables that are true in a given facet
getGlobalVar :: SimplicialModelS5 -> Facet -> [Prp]
getGlobalVar sm = concatMap (getLocalVar sm)

-- | Get a list of all neighbouring facets where all given agents sit at an intersection  
getRelFacets :: SimplicialModelS5 -> Facet -> [Agent] -> [Facet]
getRelFacets (SMS5 sc col _) facet ags = filter (\x -> (ags `intersect` map (col M.!) (facet `intersect` x)) == ags) sc

-- | Get a list of all facets in which a formula has to be true to be considered common knowledge
-- See 1.6.1 in [Dit+22] for detailed definition of starB 
getStarB :: SimplicialModelS5 -> [Facet] -> [Agent] -> [Facet]
getStarB sm starBs ags
    | singleStarB sm starBs ags == starBs = starBs -- no new facet added to starB, done
    | otherwise = getStarB sm (singleStarB sm starBs ags) ags -- new facet(s) added to starB, check once again

-- | Get a list of all facets where some agent from the given list sits at an intersection of any facet in the given list, including the given facets
singleStarB :: SimplicialModelS5 -> [Facet] -> [Agent] -> [Facet]
singleStarB (SMS5 sc col _) cur ags = filter (\x -> any (\y -> not (null (ags `intersect` map (col M.!) (y `intersect` x)))) cur) sc

eval :: PointedSimplicialModelS5 -> Form -> Bool
eval _ Top = True
eval _ Bot = False
eval (sm, facet) (PrpF p) = p `elem` getGlobalVar sm facet
eval pm (Neg form) = not $ eval pm form
eval pm (Conj forms)  = all (eval pm) forms
eval pm (Disj forms)  = any (eval pm) forms
eval pm (Xor  forms)  = odd $ length (filter id $ map (eval pm) forms)
eval pm (Impl f g)    = not (eval pm f) || eval pm g
eval pm (Equi f g)    = eval pm f == eval pm g
eval (sm, facet) (K ag form) = all (\x -> eval (sm, x) form) facets where
    facets = getRelFacets sm facet [ag]
eval pm (Forall ps f) = eval pm (foldl singleForall f ps) where
  singleForall g p = Conj [ substit p Top g, substit p Bot g ]
eval pm (Exists ps f) = eval pm (foldl singleExists f ps) where
  singleExists g p = Disj [ substit p Top g, substit p Bot g ]
eval (sm, cur) (Ck ags form) = all (\x -> eval (sm, x) form) facets where
    facets = getStarB sm [cur] ags
eval (sm, facet) (Dk ags form) = all (\x -> eval (sm, x) form) facets where
    facets = getRelFacets sm facet ags
eval pm (Kw ag form) = eval pm (K ag form) || eval pm (K ag (Neg form))
eval pm (Ckw ag form) = eval pm (Ck ag form) || eval pm (Ck ag (Neg form))
eval pm (Dkw ags form) = eval pm (Dk ags form) || eval pm (Dk ags (Neg form))
eval (sm, _) (G form) = isTrue sm form
eval _ (PubAnnounce _ _) = undefined -- TODO
eval _ (Dia _ _) = undefined -- TODO


-- Examples

-- TODO: instance Arbitrary SimplicialModelS5

-- Fig. 4 from proposal
exampleSM :: SimplicialModelS5
exampleSM = SMS5
    [[1, 2, 3], [2, 3, 4]]
    (M.fromList [(1, "a"), (2, "b"), (3, "c"), (4, "a")])
    (M.fromList [(1, M.fromList [(P 1, True)]), (2, M.fromList [(P 2, True)]), (3, M.fromList [(P 3, False)]), (4, M.fromList [(P 1, False)])])

-- Fig. 4 from proposal, pointing towards facet X
pointedExampleSM :: PointedSimplicialModelS5
pointedExampleSM = (exampleSM, [1, 2, 3])

-- C' from Example 22 in [Dit+22] (p. 32)
exampleSM2 :: SimplicialModelS5
exampleSM2 = SMS5
    [[1, 2, 3], [2, 3, 4], [3, 4, 5], [5, 6, 7], [6, 7, 8], [7, 8, 9]]
    (M.fromList [(1, "a"), (2, "b"), (3, "c"), (4, "a"), (5, "b"), (6, "a"), (7, "c"), (8, "b"), (9, "a")])
    (M.fromList [(1, M.fromList [(P 1, False)]), (2, M.fromList [(P 2, True)]), (3, M.fromList [(P 3, True)]), (4, M.fromList [(P 1, True)]), (5, M.fromList [(P 2, False)]), (6, M.fromList [(P 1, True)]), (7, M.fromList [(P 3, False)]), (8, M.fromList [(P 2, True)]), (9, M.fromList [(P 1, False)])])

{-
>>> pointedExampleSM |= (K "a" (PrpF (P 1)))
True

>>> pointedExampleSM |= (K "b" (PrpF (P 1)))
False

>>> pointedExampleSM |= (Dk ["b", "c"] (conj (PrpF (P 1)) (PrpF (P 2))))
False

>>> pointedExampleSM |= (Dk ["b", "c"] (conj (PrpF (P 2)) (PrpF (P 3))))
False

>>> pointedExampleSM |= (Dk ["b", "c"] (conj (PrpF (P 2)) (Neg (PrpF (P 3)))))
True

>>> eval (exampleSM2, [1, 2, 3]) (Ck ["a", "b", "c"] (PrpF (P 3)))
False
-}
