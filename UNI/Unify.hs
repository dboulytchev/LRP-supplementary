-- Supplementary materials for the course of logic and relational programming, 2021
-- (C) Dmitry Boulytchev, dboulytchev@gmail.com
-- Unification.

module Unify where

import Control.Monad
import Data.List
import qualified Term as T
import qualified Test.QuickCheck as QC
import qualified Data.Map

-- Walk primitive: given a variable, lookups for the first
-- non-variable binding; given a non-variable term returns
-- this term
walk :: T.Subst -> T.T -> T.T
walk subst v@(T.V x) = case T.lookup subst x of
                       Just v'@(T.V {}) -> walk subst v'
                       Just c'@(T.C {}) -> c'
                       Nothing -> v
walk subst c@(T.C {}) = c

-- Occurs-check for terms: return true, if
-- a variable occurs in the term
occurs :: T.Var -> T.T -> Bool
occurs = T.occurs'

-- Unification generic function. Takes an optional
-- substitution and two terms and returns an optional
-- MGU
unify :: Maybe T.Subst -> T.T -> T.T -> Maybe T.Subst
unify Nothing t u = Nothing
unify (Just subst) t u = let t' = walk subst t in
                         let u' = walk subst u in
                         case (t', u') of
                           (T.V x, T.V y) | x == y -> Just subst
                           (T.V x, term) | not $ occurs x term ->
                             Just $ T.add subst x term
                           (term, T.V y) | not $ occurs y term ->
                             Just $ T.add subst y term
                           (T.C xCst xs, T.C yCst ys) | xCst == yCst &&
                                                        length xs == length ys ->
                             foldl (\s (x, y) -> unify s x y) (Just subst) (zip xs ys)
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

