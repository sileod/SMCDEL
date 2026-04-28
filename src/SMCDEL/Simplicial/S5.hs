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

import Data.List
import qualified Data.Map.Strict as M
import Test.QuickCheck

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

class HasVertices a where
    vertsOf :: a -> [Vert]

instance HasVertices SimplicialComplex where
    vertsOf = foldl' union []

instance HasVertices SimplicialModelS5 where
    vertsOf (SMS5 sc _ _) = vertsOf sc

instance HasVocab SimplicialModelS5 where
   vocabOf (SMS5 _ _ val) = nub ((concatMap M.keys . M.elems) val)

instance HasAgents SimplicialModelS5 where
    agentsOf (SMS5 _ col _) = nub (M.elems col)

instance Pointed SimplicialModelS5 Facet where
type PointedSimplicialModelS5 = (SimplicialModelS5, Facet)

instance Pointed SimplicialModelS5 [Facet] where
type MultipointedSimplicialModelS5 = (SimplicialModelS5, [Facet])

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
eval pm (PubAnnounce form1 form2) = not (eval pm form1) || eval (update pm form1) form2 
eval _ (Dia _ _) = undefined -- TODO

instance Semantics SimplicialModelS5 where
    isTrue sm form = all (\x -> eval (sm, x) form) (facetsOf sm)

instance Semantics PointedSimplicialModelS5 where
    isTrue = eval

instance Semantics MultipointedSimplicialModelS5 where
    isTrue (sm, xs) form = all (\x -> isTrue (sm, x) form) xs

instance Update SimplicialModelS5 Form where
    unsafeUpdate sm@(SMS5 sc col val) form = SMS5 newsc newcol newval where
        newsc = filter (\x -> eval (sm, x) form) sc
        newcol = M.filterWithKey (\k _ -> k `elem` newvert) col
        newval = M.filterWithKey (\k _ -> k `elem` newvert) val 
        newvert = vertsOf newsc

instance Update PointedSimplicialModelS5 Form where
    unsafeUpdate (sm, x) form = (unsafeUpdate sm form, x)

withoutFacet :: SimplicialModelS5 -> Facet -> SimplicialModelS5
withoutFacet (SMS5 sc col val) x = SMS5
    (delete x sc)
    (M.filterWithKey (\k _ -> k `elem` newVs) col)
    (M.filterWithKey (\k _ -> k `elem` newVs) val)
    where
        newVs = vertsOf (delete x sc)

instance Arbitrary SimplicialModelS5 where
    arbitrary = do
        let verts = [1..45 :: Vert]
        -- let col = M.fromList $ zip verts (concat $ replicate 9 defaultAgents)
        col <- M.fromList <$> mapM (\v -> do
            ag <- elements defaultAgents
            return (v, ag)
            ) verts
        let containsAllAg facet = all (\ag -> ag `elem` map (col M.!) facet) defaultAgents
        initFacet <- vectorOf 5 (elements verts) `suchThat` containsAllAg
        -- let initFacet = [1, 2, 3, 4, 5]
        size <- chooseInt (1, 9)
        let fix f = x where x = f x
        sc <- fix (\f sc -> do
            connectTo <- elements sc
            newFacetPart <- sublistOf connectTo `suchThat` (\x -> length x < 5)
            let agIn = map (col M.!)
            newFacet <- fix (\g vs-> do
                newV <- elements verts `suchThat` (\v -> (col M.! v) `notElem` agIn vs)
                let newFace = newV : vs
                if length newFace < 5 then g newFace
                                      else return newFace
                ) newFacetPart
            let newSc = newFacet : sc
            if length newSc < size then f newSc
                                   else if size == 1 then return sc else return newSc
            ) [initFacet]
        let usedVerts = vertsOf sc
            colActual = M.filterWithKey (\k _ -> k `elem` usedVerts) col
        val <- M.fromList <$> mapM (\v -> do
            let prp = P $ read (col M.! v)
            ass <- M.singleton prp <$> choose (True, False)
            return (v,ass)
            ) usedVerts
        return $ SMS5 sc colActual val
    shrink sm@(SMS5 sc _ _) = 
        [ sm `withoutFacet` x | x <- sc, not (null $ delete x sc) ]

-- Examples

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
Some tests:

In the simplicial model depicted in Fig. 4 in the proposal pointing towards 
\(X\), it is true that \(a\) knows \(p_a\), since \(p_a\) is true in \(X\) and 
only \(X\) is accessible for \(a\).
>>> pointedExampleSM |= (K "a" (PrpF (P 1)))
True

It is not true however, that \(b\) knows \(p_a\), since \(p_a\) is not true in 
\(Y\) and the facets \(X\) and \(Y\) are indistinguishable for \(b\).
>>> pointedExampleSM |= (K "b" (PrpF (P 1)))
False

It is not true that the agents \(b\) and \(c\) distributedly know that 
\(p_a \wedge p_b\), since \(p_a\) is true in \(X\) but not in \(Y\) and both
\(X\) and \(Y\) are indistinguishable for both \(b\) and \(c\) (i.e. neither of 
them knows that \(p_a\) is true).
>>> pointedExampleSM |= (Dk ["b", "c"] (conj (PrpF (P 1)) (PrpF (P 2))))
False

However, they distributedly know that \(p_b \wedge \neg p_c\), since this 
formula holds in both \(X\) and \(Y\).
>>> pointedExampleSM |= (Dk ["b", "c"] (conj (PrpF (P 2)) (Neg (PrpF (P 3)))))
True

Furthermore, while \(b\) and \(c\) among each other do not, all agents 
together distributedly know that \(p_a\) is true, since for \(a\), only \(X\) 
(where \(p_a\) is true) is accessible.
Distributed knowledge among all agents is trivial, since a formula is 
distributedly known among all agents iff it is true in the current facet.
>>> pointedExampleSM |= (Dk ["a", "b", "c"] (PrpF (P 1)))
True

Initially, it is not true that \(p_a\) is common knowledge (both \(b\) and \(c\)
are uncertain about \(p_a\) since \(X\) and \(Y\) are related for agents \(b\) 
and \(c\)) and \(p_a\) is true in \(X\) but false in \(Y\)).
>>> eval pointedExampleSM (Ck ["a", "b", "c"] (PrpF (P 1)))
False

After publicly announcing that \(p_a\) is true, \(p_a\) is common knowledge 
among all agents.
>>> eval pointedExampleSM (PubAnnounce (PrpF (P 1)) (Ck ["a", "b", "c"] (PrpF (P 1))))
True

In \( \mathcal{C}'\) from Ex. 22 in [Dit+22], pointing towards \(X\), it is not 
common knowledge among all agents that \(p_c\) is true, since \(b\) cannot 
distinguish between the left part of the simplicial complex, where \(p_c\) is 
true, and the right part of the complex, where \(p_3\) is false (formally: 
\(p_c\) is not true in \(V\), but \(X\) and \(V\) are
connected via \( c\in \chi(X\cap Z)\) and \( b\in \chi(Z\cap V) \)). 
>>> eval (exampleSM2, [1, 2, 3]) (Ck ["a", "b", "c"] (PrpF (P 3)))
False
-}
