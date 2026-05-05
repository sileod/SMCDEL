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
import SMCDEL.Internal.Help

-- | A vertex is represented by an integer
type Vert = Int

-- | A facet is a list of vertices
type Facet = [Vert] -- TODO: implement as sets

-- | A simplicial complex is represented by a list of facets
type SimplicialComplex = [Facet] -- TODO: implement as sets

-- | An assignment is a map from atomic propositions to Booleans
type Assignment = M.Map Prp Bool

-- | A simplicial model is a simplicial complex and a map from vertices to pairs
-- of agents (colour of that vertex) and assignments (valuation of that vertex)  
data SimplicialModelS5 = SMS5 SimplicialComplex (M.Map Vert (Agent, Assignment))
    deriving (Eq, Show)

class HasFacets a where
    facetsOf :: a -> [Facet]

instance HasFacets SimplicialModelS5 where
    facetsOf (SMS5 sc _) = sc

class HasVertices a where
    vertsOf :: a -> [Vert]

instance HasVertices SimplicialComplex where
    vertsOf = foldl' union []

instance HasVertices SimplicialModelS5 where
    vertsOf (SMS5 _ verts) = M.keys verts

instance HasAgents SimplicialModelS5 where
    agentsOf (SMS5 _ verts) = nub (map fst (M.elems verts))

instance HasVocab SimplicialModelS5 where
    vocabOf (SMS5 _ verts) = nub (concatMap (M.keys . snd) (M.elems verts))

instance Pointed SimplicialModelS5 Facet where
type PointedSimplicialModelS5 = (SimplicialModelS5, Facet)

instance Pointed SimplicialModelS5 [Facet] where
type MultipointedSimplicialModelS5 = (SimplicialModelS5, [Facet])

instance (HasFacets a, Pointed a b) => HasFacets (a, b) where
    facetsOf = facetsOf . fst

-- | Get a list of variables that are true in a given facet
trueIn :: SimplicialModelS5 -> Facet -> [Prp]
trueIn (SMS5 _ verts) = concatMap trueAt where
    trueAt v = (M.keys . M.filter id) (snd $ verts M.! v)

-- | Get the agent colouring the given vertex in the given model
agAt :: SimplicialModelS5 -> Vert -> Agent
agAt (SMS5 _ verts) v = fst $ verts M.! v

-- | Get a list of all neighbouring facets where all given agents sit at an intersection
getRelFacets :: SimplicialModelS5 -> Facet -> [Agent] -> [Facet]
getRelFacets sm@(SMS5 sc _) facet ags = filter (\x -> ags `subseteq` sharedAgs x) sc where
    sharedAgs x = map (agAt sm) (facet `intersect` x)

-- | Get a list of all facets in which a formula has to be true to be considered
-- common knowledge (closure of singleStarB)
-- See 1.6.1 in [Dit+22] for detailed definition of starB 
getStarB :: SimplicialModelS5 -> [Agent] -> Facet -> [Facet]
getStarB sm ags cur = lfp (singleStarB sm ags) [cur]

-- | Get a list of all facets where some agent from the given list sits at an 
--  intersection of any facet in the given list, including the given facets
singleStarB :: SimplicialModelS5 -> [Agent] -> [Facet] -> [Facet]
singleStarB sm@(SMS5 sc _) ags facets = filter (\x -> any (connectedByAgs x) facets) sc where
    connectedByAgs f1 f2 = any (`elem` sharedAgs) ags where
        sharedAgs = map (agAt sm) (f1 `intersect` f2)

eval :: PointedSimplicialModelS5 -> Form -> Bool
eval _ Top = True
eval _ Bot = False
eval (sm, facet) (PrpF p) = p `elem` trueIn sm facet
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
    facets = getStarB sm ags cur
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
    unsafeUpdate sm@(SMS5 sc verts) form = SMS5 newsc newverts where
        newsc = filter (\x -> eval (sm, x) form) sc
        newverts = M.filterWithKey (\k _ -> k `elem` newkeys) verts
        newkeys = vertsOf newsc

instance Update PointedSimplicialModelS5 Form where
    unsafeUpdate (sm, x) form = (unsafeUpdate sm form, x)

withoutFacet :: SimplicialModelS5 -> Facet -> SimplicialModelS5
withoutFacet (SMS5 sc verts) x = SMS5
    (delete x sc)
    (M.filterWithKey (\k _ -> k `elem` newKeys) verts)
    where
        newKeys = vertsOf (delete x sc)

instance Arbitrary SimplicialModelS5 where
    arbitrary = do
        let nonActualVerts = [6..30 :: Vert]
            verts = [1..30 :: Vert]
        -- colour verts [6..30] randomly
        randomVertMap <- M.fromList <$> mapM (\v -> do
            ag <- elements defaultAgents
            let prp = P $ read ag - 1
            ass <- M.singleton prp <$> choose (True, False)
            return (v, (ag, ass))
            ) nonActualVerts
        -- colour verts [1..5] with respective agent to ensure feasibility of facets
        semirandomVertMap <- M.fromList <$> mapM (\v -> do
            let prp = P $ v - 1
                ag = show v
            ass <- M.singleton prp <$> choose (True, False)
            return (v :: Vert, (ag :: Agent, ass))
            ) [1..5]
        let vertMapAll = randomVertMap `M.union` semirandomVertMap
            containsAllAg x = all (\ag -> ag `elem` map (fst . (vertMapAll M.!)) x) defaultAgents
            facet = sort <$> vectorOf 5 (elements verts) `suchThat` containsAllAg
            connected sc = 
                length sc == 1 || 
                all (\f1 -> any (\f2 -> f1 `intersect` f2 /= []) (delete f1 sc)) sc
        sc <- (nub <$> resize 9 (listOf1 facet)) `suchThat` connected
        let vertMap = M.filterWithKey (\k _ -> k `elem` vertsOf sc) vertMapAll
        return $ SMS5 sc vertMap
    -- shrink might break connectivity!
    shrink sm@(SMS5 sc _) = 
        [ sm `withoutFacet` x | x <- sc, not (null $ delete x sc) ]

instance {-# OVERLAPPING #-} Arbitrary PointedSimplicialModelS5 where
    arbitrary = do
        sm <- arbitrary :: Gen SimplicialModelS5
        x <- elements (facetsOf sm)
        return (sm, x)

instance {-# OVERLAPPING #-} Arbitrary MultipointedSimplicialModelS5 where
    arbitrary = do
        sm <- arbitrary :: Gen SimplicialModelS5
        xs <- sublistOf (facetsOf sm) `suchThat` (not . null)
        return (sm, xs)
