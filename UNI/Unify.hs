-- Supplementary materials for the course of logic and relational programming, 2021
-- (C) Dmitry Boulytchev, dboulytchev@gmail.com
-- Unification.

module Unify where

import Control.Monad
import Data.List
import qualified Term as T
import qualified Test.QuickCheck as QC
import qualified Data.Set as Set

-- Walk primitive: given a variable, lookups for the first
-- non-variable binding; given a non-variable term returns
-- this term
walk :: T.Subst -> T.T -> T.T
walk s t = case t  of 
            T.V v -> 
              case T.lookup s v of
                Just t -> walk s t
                _      -> t
            _     -> t

-- Occurs-check for terms: return true, if
-- a variable occurs in the term
occurs :: T.Var -> T.T -> Bool
occurs v t = v `Set.member` T.fv t

-- Unification generic function. Takes an optional
-- substitution and two unifiable structures and
-- returns an MGU if exists
class Unifiable a where
  unify :: Maybe T.Subst -> a -> a -> Maybe T.Subst

instance Unifiable T.T where
  unify ms t1 t2 = go ms [(t1, t2)]
    where
      go :: Maybe T.Subst -> [(T.T, T.T)] -> Maybe T.Subst
      go Nothing _                   = Nothing
      go (Just !s) []                = Just s
      go (Just !s) ((a, b) : rest)   =
        let a' = walk s a
            b' = walk s b
        in case (a', b') of
          (T.V x, T.V y)
            | x == y    -> go (Just s) rest
            | otherwise -> go (Just $ T.put s x (T.V y)) rest
          (T.V x, t)
            | occurs x t -> Nothing
            | otherwise  -> go (Just $ T.put s x t) rest
          (t, T.V x)
            | occurs x t -> Nothing
            | otherwise  -> go (Just $ T.put s x t) rest
          (T.C c1 ts1, T.C c2 ts2)
            | c1 /= c2 || length ts1 /= length ts2 -> Nothing
            | otherwise ->
                go (Just s) (zip ts1 ts2 ++ rest)

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
    
