{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, FlexibleContexts #-}

module SMCDEL.Simplicial.S5 where

import Data.List (intersect, nub)
import qualified Data.Map.Strict as M

import SMCDEL.Language

-- | A vertex is represented by an integer
type Vert = Int

-- | A facet is a list of vertices
type Facet = [Vert]

-- | A simplicial complex is represented by a list of facets
type SimplicialComplex = [Facet]

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
    isTrue (sm, facet) = eval (sm, facet)

-- | Get a list of variables that are true in a given vertex
getLocalVar :: Valuation -> Vert -> [Prp]
getLocalVar val vert = case M.lookup vert val of
    Nothing -> error "vertex not in SC"
    Just assigns -> (M.keys . M.filter id) assigns

-- | Get a list of variables that are true in a given facet
getGlobalVar :: Valuation -> [Vert] -> [Prp]
getGlobalVar val = concatMap (getLocalVar val)

-- | Get a list of all neighbouring facets where all given agents sit at an intersection  
getRelFacets :: SimplicialModelS5 -> [Vert] -> [Agent] -> [[Vert]]
getRelFacets (SMS5 sc col _) facet ags = filter (\x -> (ags `intersect` map (col M.!) (facet `intersect` x)) == ags) sc

eval :: PointedSimplicialModelS5 -> Form -> Bool
eval _ Top = True
eval _ Bot = False
eval (SMS5 _ _ val, facet) (PrpF p) = p `elem` getGlobalVar val facet
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
eval _ (Ck _ _) = undefined
eval (sm, facet) (Dk ags form) = all (\x -> eval (sm, x) form) facets where
    facets = getRelFacets sm facet ags
eval pm (Kw ag form) = eval pm (K ag form) || eval pm (K ag (Neg form))
eval _ (Ckw _ _) = undefined
eval pm (Dkw ags form) = eval pm (Dk ags form) || eval pm (Dk ags (Neg form))
eval (sm, _) (G form) = all (\x -> eval (sm, x) (G form)) (facetsOf sm)
eval _ (PubAnnounce _ _) = undefined
eval _ (Dia _ _) = undefined


-- Examples

-- Fig. 4 from proposal
exampleSM :: SimplicialModelS5
exampleSM = SMS5
    [[1, 2, 3], [2, 3, 4]]
    (M.fromList [(1, "a"), (2, "b"), (3, "c"), (4, "a")])
    (M.fromList [(1, M.fromList [(P 1, True)]), (2, M.fromList [(P 2, True)]), (3, M.fromList [(P 3, False)]), (4, M.fromList [(P 1, False)])])

{-
>>> eval (exampleSM, [1, 2, 3]) (K "a" (PrpF (P 1)))
True

>>> eval (exampleSM, [1, 2, 3]) (K "b" (PrpF (P 1)))
False

>>> eval (exampleSM, [1, 2, 3]) (Dk ["b", "c"] (conj (PrpF (P 1)) (PrpF (P 2))))
False

>>> eval (exampleSM, [1, 2, 3]) (Dk ["b", "c"] (conj (PrpF (P 2)) (PrpF (P 3))))
False

>>> eval (exampleSM, [1, 2, 3]) (Dk ["b", "c"] (conj (PrpF (P 2)) (Neg (PrpF (P 3)))))
True
-}
