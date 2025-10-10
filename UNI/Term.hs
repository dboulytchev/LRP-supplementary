-- Supplementary materials for the course of logic and relational programming, 2021
-- (C) Dmitry Boulytchev, dboulytchev@gmail.com
-- Terms.

module Term where

import qualified Data.Map  as Map
import qualified Data.Set  as Set
import qualified Data.Maybe as Maybe
import Data.List
import Test.QuickCheck
import Debug.Trace

-- Type synonyms for constructor and variable names
type Cst = Int
type Var = Int

-- A type for terms: either a constructor applied to subterms
-- or a variable
data T = C Cst [T] | V Var deriving (Show, Eq)

-- Free variables for a term; returns a set of variables' ids
fv :: T -> Set.Set Int
fv = fv' Set.empty where
  fv' acc (V   x  ) = Set.insert x acc
  fv' acc (C _ sub) = foldl fv' acc sub

-- QuickCheck instantiation for formulas
-- Don't know how to restrict the number of variables/constructors yet
numVar = 10
numCst = 10

-- "Arbitrary" instantiation for terms
instance Arbitrary T where
  shrink (V _)        = []
  shrink (C cst subs) = subs ++ [ C cst subs' | subs' <- shrink subs ]
  arbitrary = sized f where
    f :: Int -> Gen T
    f 0 = num numVar >>= return . V
    f 1 = do cst <- num numCst
             return $ C cst []      
    f n = do m   <- pos (n - 1)
             ms  <- split n m
             cst <- num numCst
             sub <- mapM f ms
             return $ C cst sub
    num   n   = (resize n arbitrary :: Gen (NonNegative Int)) >>= return . getNonNegative
    pos   n   = (resize n arbitrary :: Gen (Positive    Int)) >>= return . getPositive
    split = iterate []
    iterate acc rest 1 = return $ rest : acc
    iterate acc rest i = do k <- num rest
                            iterate (k : acc) (rest - k) (i-1) 

-- A type for a substitution: a (partial) map from
-- variable names to terms. Note, this represents not
-- neccessarily idempotent substitution
type Subst = Map.Map Var T

-- Empty substitution
empty :: Subst
empty = Map.empty

-- Lookups a substitution
lookup :: Subst -> Var -> Maybe T
lookup = flip Map.lookup 

-- Adds in a substitution
add :: Subst -> Var -> T -> Subst
add s v t = Map.insert v t s

-- Apply a substitution to a term
apply :: Subst -> T -> T
apply s (C c ts) = C c $ map (apply s) ts
apply s (V v) = case Term.lookup s v of
                  Just t -> t
                  Nothing -> V v

termContains :: Var -> T -> Bool
termContains v (C c ts) = any (termContains v) ts
termContains v (V v') = v == v'

takeOne :: Subst -> Maybe ((Var, T), Subst)
takeOne s = case Map.toList s of
              (v, t) : others -> Just ((v, t), Map.fromList others)
              [] -> Nothing

type Fvs = Map.Map Var (Set.Set Var)

applyFvsOnce :: Fvs -> Var -> Set.Set Var
applyFvsOnce fvs v = Maybe.fromMaybe Set.empty (Map.lookup v fvs)

applyFvs :: Fvs -> Set.Set Var -> Set.Set Var
applyFvs fvs vars = Set.unions $ Set.map (applyFvsOnce fvs) vars

selfSubst :: Fvs -> Fvs
selfSubst s = Map.map (applyFvs s) s 

ranFvs :: Fvs -> Set.Set Var
ranFvs s = Set.unions $ Map.elems s

ranClean :: Fvs -> Bool
ranClean s = not $ Set.null $ Map.keysSet s `Set.intersection` ranFvs s

occursCheck :: Fvs -> Int -> Bool
occursCheck s 0 = ranClean s
occursCheck s n = ranClean s || occursCheck (selfSubst s) (n - 1)

-- Occurs check: checks if a substitution contains a circular
-- binding    
occurs :: Subst -> Bool
occurs s = occursCheck (Map.map fv s) (Map.size s + 1)

-- Well-formedness: checks if a substitution does not contain
-- circular bindings
wf :: Subst -> Bool
wf = not . occurs

-- A composition of substitutions; the substitutions are
-- assumed to be well-formed
infixl 6 <+>

(<+>) :: Subst -> Subst -> Subst
s <+> p = s `Map.union` p

ran :: Subst -> Set.Set Int
ran = Set.unions . Map.map fv

-- A condition for substitution composition s <+> p: dom (s) \cup ran (p) = \emptyset
compWF :: Subst -> Subst -> Bool
compWF s p  = Set.null $ Map.keysSet s `Set.intersection` ran p 
  
-- A property: for all substitutions s, p and for all terms t
--     (t s) p = t (s <+> p)
checkSubst :: (Subst, Subst, T) -> Bool
checkSubst (s, p, t) =
  not (wf s) || not (wf p) || not (compWF s p) || (apply p . apply s $ t) == apply (s <+> p) t

-- This check should pass:
qcEntry = quickCheck $ withMaxSuccess 1000 $ (\ x -> within 100000000 $ checkSubst x)
