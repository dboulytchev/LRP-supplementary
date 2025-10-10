-- Supplementary materials for the course of logic and relational programming, 2021
-- (C) Dmitry Boulytchev, dboulytchev@gmail.com
-- Unification.

module Unify where

import Control.Monad
import Data.List
import qualified Term as T
import qualified Test.QuickCheck as QC

-- Walk primitive: given a variable, lookups for the first
-- non-variable binding; given a non-variable term returns
-- this term
walk :: T.Subst -> T.T -> T.T
walk s (T.V v) = maybe (T.V v) (walk s) (T.lookup s v)
walk s t = t

-- Occurs-check for terms: return true, if
-- a variable occurs in the term
occurs :: T.Var -> T.T -> Bool
occurs = T.termContains

-- Unification generic function. Takes an optional
-- substitution and two terms and returns an optional
-- MGU
unify :: Maybe T.Subst -> T.T -> T.T -> Maybe T.Subst
unify Nothing _ _ = Nothing
unify s@(Just s') t1 t2 = case (walk s' t1, walk s' t2) of
                                  (T.V v1, T.V v2) | v1 == v2 -> s
                                  (T.V v1, t2') -> Just $ T.add s' v1 t2'
                                  (t1', T.V v2) -> Just $ T.add s' v2 t1'
                                  (T.C c1 ts1, T.C c2 ts2) | c1 == c2 && length ts1 == length ts2
                                                -> let unifyPair s (t1, t2) = unify s t1 t2 in
                                                      foldl unifyPair s (zip ts1 ts2)
                                  _ -> Nothing

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
    
