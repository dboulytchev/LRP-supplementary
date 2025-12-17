-- Supplementary materials for the course of logic and relational programming, 2025
-- (C) Dmitry Boulytchev, dboulytchev@gmail.com
-- SLD-resolution.

module SLD where

import Term 
import Unify
import qualified Data.Map as Map
import qualified Control.Monad as Monad
import qualified Control.Monad.State as St
import Debug.Trace

-- Predicate names
type Pred = Int

-- Atomic formula
type A = (Pred, [T])

-- A class type to convert data structures to/from
-- atomic formulas
class Atomic a where
  toAtomic   :: a -> A
  fromAtomic :: A -> a 

-- Horn clause
data H = A :- [A] deriving Show

-- Program
type P = [H]

-- Unification for atomic formulas
instance Unifiable A where
  unify = undefined
  
-- Substitution application to atomic formulas
instance Substitutable A where
  apply = undefined

-- State
--   1. A triple
--      1. a tail of a program to match against
--	2. current goal
--	3. current substitution
--   2. A stack of triplets as in the previous item
--   3. An index of first fresh variable
type Triplet = (P, [A], Subst)
type State   = (Triplet, [Triplet], Var)

-- Makes an initial state from a program and list of goals
-- 1000 is a hardcoded maximal number of variables in a goal
initState :: P -> [A] -> State
initState p g = ((p, g, empty), [], 1000)

-- Refresh all variables in a term
refresh :: T -> St.State (Var, Map.Map Var Var) T
refresh (V x) = do
  (i, m) <- St.get
  case Map.lookup x m of
    Nothing ->
      do St.put (i+1, Map.insert x i m)
         return (V i)
    Just j -> return (V j)
refresh (C c ts) = Monad.liftM (C c) $ mapM refresh ts

-- Refresh all variables in atomic formula
refreshA :: A -> St.State (Var, Map.Map Var Var) A
refreshA (p, ts) = Monad.liftM (p,) $ mapM refresh ts
  
-- Refresh all variables in a horn clause
refreshH :: H -> St.State (Var, Map.Map Var Var) H
refreshH (a :- as) = Monad.liftM (\ (a:as) -> (a :- as)) $ mapM refreshA (a:as)

-- Rename a clause
rename :: H -> Var -> (H, Var)
rename h v =
  let (h', (v', _)) = St.runState (refreshH h) (v, Map.empty) in
  (h', v')

-- Top-level evaluator: takes
--   1. a program
--   2. a query
--   3. returns a list of substitutions
eval :: P -> [A] -> [Subst]
eval p g = evalRec p $ initState p g

-- Recursive evalutor
evalRec :: P -> State -> [Subst] 
evalRec p ((hs, g, subst), stack, fresh) = undefined

------------------------------------------
--- Some relations for natural numbers ---
------------------------------------------

--- Some predefined variables
x = V 0
y = V 1
z = V 2

--- Terms
o   = C 0 []
s t = C 1 [t]

--- Predicates
add (x, y, z) = (0, [x, y, z])
mul (x, y, z) = (1, [x, y, z])
lt  (x, y)    = (2, [x, y])
le  (x, y)    = (3, [x, y])

--- Specifications
peano = [add (o, x, x) :- [], add (s(x), y, s(z)) :- [add (x, y, z)]]

--- Samples
s0 = case eval peano [add (s(o), s(o), x)] of
       []    -> "error: should find a solution"
       h : _ -> "solution: " ++ (show $ apply h x)

s1 = case eval peano [add (x, s(o), s (s (o)))] of
       []    -> "error: should find a solution"
       h : _ -> "solution: " ++ (show $ apply h x)

s2 = case eval peano [add (x, y, s (s (o)))] of
       []               -> "error: should find a soultion"
       h1 : h2 : h3 : _ -> "solutions: x = " ++ (show $ apply h1 x) ++ ", y = " ++ (show $ apply h1 y) ++ "\n" ++
                           "           x = " ++ (show $ apply h2 x) ++ ", y = " ++ (show $ apply h2 y) ++ "\n" ++
                           "           x = " ++ (show $ apply h3 x) ++ ", y = " ++ (show $ apply h3 y) ++ "\n"