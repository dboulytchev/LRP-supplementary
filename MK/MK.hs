-- Supplementary materials for the course of logic and relational programming, 2025
-- (C) Dmitry Boulytchev, dboulytchev@gmail.com
-- MicroKanren.

module MK where

import Data.Maybe
import Control.Monad
import Control.Applicative
import qualified Term as T
import qualified Unify as U

data Stream a =
  Nil                 |
  Mature a (Stream a) |
  Immature (Stream a) deriving Functor

pick n s =
  case n of
    0 -> []
    _ -> case s of
           Nil           -> []
           Mature   h tl -> h : pick (n-1) tl
           Immature fs   -> pick n fs  

instance Applicative Stream where
  pure     = undefined
  _ <*> _  = undefined

instance Alternative Stream where
  empty   = undefined
  _ <|> _ = undefined
  
instance Monad Stream where
  _ >>= _ = undefined

instance MonadPlus Stream where
  mzero = undefined
  mplus = undefined
  
type State = (T.Subst, Int)
type Goal  = State -> Stream State

infix 4 ===

(===) :: T.T -> T.T -> Goal
t1 === t2 = undefined

infixr 3 &&&

(&&&) :: Goal -> Goal -> Goal
g1 &&& g2 = undefined

infixr 2 |||

(|||) :: Goal -> Goal -> Goal
g1 ||| g2 = undefined

call_fresh :: (T.T -> Goal) -> Goal
call_fresh f = undefined

delay :: Goal -> Goal
delay f s = undefined

--- Initial state & run
initial = (T.empty, 1000)
peep x (s, _) = map (T.apply s) x
run peeper goal = map peeper $ pick (-1) $ goal initial

------------------------------------------
--- Some relations for natural numbers ---
------------------------------------------

--- Some predefined variables
x = T.V 0
y = T.V 1
z = T.V 2

--- Terms
o   = T.C 0 []
s t = T.C 1 [t]

add x y z = delay $
  x === o &&& y === z |||
  call_fresh (\ x' ->
  call_fresh (\ z' ->
    x === s x' &&&
    z === s z' &&&
    add x' y z'
  ))

s0 = run (peep [x])    (add (s o) (s o) x)
s1 = run (peep [x])    (add x (s o) (s (s o)))
s2 = run (peep [x, y]) (add x y (s (s o)))
       

