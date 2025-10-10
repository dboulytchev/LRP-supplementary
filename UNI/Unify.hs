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
walk s v@(T.V var) = let res = T.apply s v in
                     if res == v then
                       v
                     else
                       walk s res
walk s t           = t

-- Occurs-check for terms: return true, if
-- a variable occurs in the term
occurs :: T.Var -> T.T -> Bool
occurs v t = v `elem` T.fv t

-- Unification generic function. Takes an optional
-- substitution and two terms and returns an optional
-- MGU
unify :: Maybe T.Subst -> T.T -> T.T -> Maybe T.Subst
unify Nothing  t1 t2    = unify (Just T.empty) t1 t2
unify js@(Just s) t1 t2 = let walks = (walk s t1, walk s t2) in
                          case walks of
                            (T.V l'   , T.V r')    -> if l' /= r' then 
                                                        Just $ T.add s l' (T.V r')
                                                      else 
                                                        js
                            (t        , T.V r')    -> if not (occurs r' t) then
                                                        Just $ T.add s r' t
                                                      else
                                                        Nothing
                            (T.V l'   , t)         -> if not (occurs l' t) then
                                                        Just $ T.add s l' t
                                                      else
                                                        Nothing
                            (T.C cl al, T.C cr ar) | cl /= cr               -> Nothing
                                                   | length al /= length ar -> Nothing
                                                   | otherwise              -> foldl fun (Just s) (zip al ar) where
                                                                                 fun :: Maybe T.Subst -> (T.T, T.T) -> Maybe T.Subst
                                                                                 fun Nothing  _         = Nothing
                                                                                 fun js       (l, r)    = unify js l r

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
    
