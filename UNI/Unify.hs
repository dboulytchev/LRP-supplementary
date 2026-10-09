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
walk s t = case t of
  T.C _ _ -> t
  T.V a -> case T.lookup s a of
    Nothing -> t
    Just t -> walk s t

-- Occurs-check for terms: return true, if
-- a variable occurs in the term
occurs :: T.Var -> T.T -> Bool
occurs a (T.V b) = a == b
occurs a (T.C _ vars) = Data.List.any (occurs a) vars

-- Unification generic function. Takes an optional
-- substitution and two unifiable structures and
-- returns an MGU if exists
class Unifiable a where
  unify :: Maybe T.Subst -> a -> a -> Maybe T.Subst

instance Unifiable T.T where
  unify s t1 t2 = case s of
    Nothing -> Nothing
    Just s -> 
      let t1' = walk s t1 in
      let t2' = walk s t2 in
      case (t1', t2') of
        (T.V a, T.V b) -> return $ if a == b then s else T.put (s T.<+> (T.put T.empty a t2')) a t2'
        (T.V a, _) -> if occurs a t2' then Nothing else return $ T.put s a t2'
        (_, T.V b) -> if occurs b t1' then Nothing else return $ T.put s b t1'
        (T.C c1 vars1, T.C c2 vars2) -> if c1 /= c2 then Nothing else
          if Data.List.length vars1 /= Data.List.length vars2 then Nothing else
          Data.List.foldl (\s' (t1'', t2'') -> unify s' t1'' t2'') (Just s) $ Data.List.zip vars1 vars2

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
    
