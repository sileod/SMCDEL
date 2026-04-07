module SMCDEL.Simplicial.S5 where

import Data.List (intersect)
import SMCDEL.Language

-- a vertex is represented by an integer
type Vert = Int

type SimplicialComplex = [[Vert]] -- include only facets

type Colours = [(Vert, Agent)]

type Valuation = [(Vert, [Prp])]

data SimplicialModelS5 = SMS5 SimplicialComplex Colours Valuation deriving (Eq, Show)

-- returns a list of variables that are true in a given vertex
getLocalVar :: Valuation -> Vert -> [Prp]
getLocalVar val vert = case lookup vert val of
    Nothing -> error "vertex not in SC"
    Just props -> props

-- returns a list of variables that are true in a given facet
getGlobalVar :: Valuation -> [Vert] -> [Prp]
getGlobalVar val = concatMap (getLocalVar val)

-- returns a list of all neighbouring facets where ag sits at an intersection  
getRelFacets :: SimplicialModelS5 -> [Vert] -> Agent -> [[Vert]]
getRelFacets (SMS5 sc col _) facet ag = filter (\x -> Just ag `elem` map (`lookup` col) (facet `intersect` x)) sc

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
    facets = getRelFacets sm facet ag
eval sm facets (Forall ps f) = eval sm facets (foldl singleForall f ps) where
  singleForall g p = Conj [ substit p Top g, substit p Bot g ]
eval sm facets (Exists ps f) = eval sm facets (foldl singleExists f ps) where
  singleExists g p = Disj [ substit p Top g, substit p Bot g ]
eval _ _ (Ck _ _) = undefined
eval _ _ (Dk _ _) = undefined
eval sm facet (Kw ag form) = eval sm facet (K ag form) || eval sm facet (K ag (Neg form))
eval _ _ (Ckw _ _) = undefined
eval _ _ (Dkw _ _) = undefined
eval (SMS5 facets col val) _ (G form) = all (\x -> eval (SMS5 facets col val) x (G form)) facets
eval _ _ (PubAnnounce _ _) = undefined
eval _ _ (Dia _ _) = undefined


-- Examples

-- Fig. 4 from proposal
exampleSM :: SimplicialModelS5
exampleSM = SMS5 [[1, 2, 3], [2, 3, 4]] [(1, "a"), (2, "b"), (3, "c"), (4, "a")] [(1, [P 1]), (2, [P 2]), (3, []), (4, [])]

{-
>>> eval exampleSM [1, 2, 3] (K "a" (PrpF (P 1)))
True

>>> eval exampleSM [1, 2, 3] (K "b" (PrpF (P 1)))
False
-}
