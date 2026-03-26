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
eval _ _ (Forall _ _) = undefined
eval _ _ (Exists _ _) = undefined
eval _ _ (Ck _ _) = undefined
eval _ _ (Dk _ _) = undefined
eval _ _ (Kw _ _) = undefined
eval _ _ (Ckw _ _) = undefined
eval _ _ (Dkw _ _) = undefined
eval _ _ (G _) = undefined
eval _ _ (PubAnnounce _ _) = undefined
eval _ _ (Dia _ _) = undefined


-- Examples

-- Fig. 4 from proposal
exampleSM :: SimplicialModelS5
exampleSM = SMS5 [[1, 2, 3], [2, 3, 4]] [(1, "a"), (2, "b"), (3, "c"), (4, "a")] [(1, [P 1]), (2, [P 2]), (3, []), (4, [])]