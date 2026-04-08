module SMCDEL.Simplicial.S5 where

import Data.List (intersect)
import Data.Maybe
import qualified Data.Map.Strict as M

import SMCDEL.Language

-- | A vertex is represented by an integer
type Vert = Int

-- | A simplicial complex is represented by a list of facets where each facet is a list of vertices
type SimplicialComplex = [[Vert]]

-- | The colouring function Chi is represented by a map from vertices to agents
type Colours = M.Map Vert Agent

-- | A valuation is a map from vertices to explicit assignments (maps from propositions to Booleans)
type Valuation = M.Map Vert (M.Map Prp Bool)

data SimplicialModelS5 = SMS5 SimplicialComplex Colours Valuation deriving (Eq, Show)

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
getRelFacets (SMS5 sc col _) facet ags = filter (\x -> (ags `intersect` mapMaybe (`M.lookup` col) (facet `intersect` x)) == ags) sc

eval :: SimplicialModelS5 -> [Vert] -> Form -> Bool
eval _ _ Top = True
eval _ _ Bot = False
eval (SMS5 _ _ val) facet (PrpF p) = p `elem` getGlobalVar val facet
eval sm facet (Neg form) = not $ eval sm facet form
eval sm facet (Conj forms)  = all (eval sm facet) forms
eval sm facet (Disj forms)  = any (eval sm facet) forms
eval sm facet (Xor  forms)  = odd $ length (filter id $ map (eval sm facet) forms)
eval sm facet (Impl f g)    = not (eval sm facet f) || eval sm facet g
eval sm facet (Equi f g)    = eval sm facet f == eval sm facet g
eval sm facet (K ag form) = all (\x -> eval sm x form) facets where
    facets = getRelFacets sm facet [ag]
eval sm facets (Forall ps f) = eval sm facets (foldl singleForall f ps) where
  singleForall g p = Conj [ substit p Top g, substit p Bot g ]
eval sm facets (Exists ps f) = eval sm facets (foldl singleExists f ps) where
  singleExists g p = Disj [ substit p Top g, substit p Bot g ]
eval _ _ (Ck _ _) = undefined
eval sm facet (Dk ags form) = all (\x -> eval sm x form) facets where
    facets = getRelFacets sm facet ags
eval sm facet (Kw ag form) = eval sm facet (K ag form) || eval sm facet (K ag (Neg form))
eval _ _ (Ckw _ _) = undefined
eval sm facet (Dkw ags form) = eval sm facet (Dk ags form) || eval sm facet (Dk ags (Neg form))
eval (SMS5 facets col val) _ (G form) = all (\x -> eval (SMS5 facets col val) x (G form)) facets
eval _ _ (PubAnnounce _ _) = undefined
eval _ _ (Dia _ _) = undefined


-- Examples

-- Fig. 4 from proposal
exampleSM :: SimplicialModelS5
exampleSM = SMS5 
    [[1, 2, 3], [2, 3, 4]] 
    (M.fromList [(1, "a"), (2, "b"), (3, "c"), (4, "a")]) 
    (M.fromList [(1, M.fromList [(P 1, True)]), (2, M.fromList [(P 2, True)]), (3, M.fromList [(P 3, False)]), (4, M.fromList [(P 1, False)])])

{-
>>> eval exampleSM [1, 2, 3] (K "a" (PrpF (P 1)))
True

>>> eval exampleSM [1, 2, 3] (K "b" (PrpF (P 1)))
False

>>> eval exampleSM [1, 2, 3] (Dk ["b", "c"] (conj (PrpF (P 1)) (PrpF (P 2))))
False

>>> eval exampleSM [1, 2, 3] (Dk ["b", "c"] (conj (PrpF (P 2)) (PrpF (P 3))))
False

>>> eval exampleSM [1, 2, 3] (Dk ["b", "c"] (conj (PrpF (P 2)) (Neg (PrpF (P 3)))))
True
-}
