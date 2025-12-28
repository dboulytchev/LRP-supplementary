-- Supplementary materials for the course of logic and relational programming, 2021
-- (C) Dmitry Boulytchev, dboulytchev@gmail.com
-- Unification.

module Unify where

import Control.Monad
import Data.List
import Data.Map
import Data.Set
import qualified Term as T
import qualified Test.QuickCheck as QC

-- Walk primitive: given a variable, lookups for the first
-- non-variable binding; given a non-variable term returns
-- this term
walk :: T.Subst -> T.T -> T.T
walk s (T.C x y) = T.C x y
walk s (T.V v) = if elem v $ Data.Map.keys s then walk s $ T.apply s $ T.V v else T.V v

-- Occurs-check for terms: return true, if
-- a variable occurs in the term
occurs :: T.Var -> T.T -> Bool
occurs v t = Data.Set.member v $ T.fv t

msbs :: Maybe T.Subst -> Maybe T.Subst -> Maybe T.Subst
msbs _ Nothing = Nothing
msbs Nothing _ = Nothing
msbs (Just l) (Just r) = let cmp = l T.<+> r in 
  if T.wf cmp then Just cmp else Nothing

solo :: T.Var -> T.T -> Maybe T.Subst 
solo v t = if occurs v t then Nothing else Just $ T.put T.empty v t

-- Unification generic function. Takes an optional
-- substitution and two unifiable structures and
-- returns an MGU if exists
class Unifiable a where
  unify :: Maybe T.Subst -> a -> a -> Maybe T.Subst

instance Unifiable T.T where
  unify Nothing _ _ = Nothing
  unify (Just s) l r = case (walk s l, walk s r) of
                     (T.V vl, T.V vr) -> if vl == vr then Just s else Just $ T.put s vl (T.V vr)
                     (T.V vl, c) -> msbs (solo vl c) $ Just s
                     (c, T.V vr) -> msbs (solo vr c) $ Just s
                     (T.C cl vls, T.C cr vrs) -> 
                        if cl /= cr || length vls /= length vrs 
                        then Nothing 
                        else Data.List.foldl (uncurry . unify) (Just s) $ zip vls vrs

-- An infix version of unification
-- with empty substitution
infix 4 ===

(===) :: T.T -> T.T -> Maybe T.Subst
(===) = unify (Just T.empty)

-- A quickcheck property
checkUnify :: (T.T, T.T) -> Bool
checkUnify (t, t') =
  case t === t' of
    Nothing -> True
    Just s  -> T.apply s t == T.apply s t'

-- This check should pass:
qcEntry = QC.quickCheck $ QC.withMaxSuccess 1000 $ (\ x -> QC.within 100000000 $ checkUnify x)
    
