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
walk = undefined

-- Occurs-check for terms: return true, if
-- a variable occurs in the term
occurs :: T.Var -> T.T -> Bool
occurs = undefined

-- Unification generic function. Takes an optional
-- substitution and two unifiable structures and
-- returns an MGU if exists
class Unifiable a where
  unify :: Maybe T.Subst -> a -> a -> Maybe T.Subst

instance Unifiable T.T where
  unify s t1 t2 = undefined

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
    
