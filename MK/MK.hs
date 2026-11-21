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
  pure     = \x -> Mature x Nil
  fs <*> xs  = case fs of
                Nil -> Nil
                Mature fh ftl ->
                  case xs of
                    Nil -> Nil
                    Mature xh xtl ->
                      Mature (fh xh) (ftl <*> xtl)
                    Immature ys ->
                      fs <*> ys
                Immature gs -> gs <*> xs

instance Alternative Stream where
  empty   = Nil
  s1 <|> s2 = case s1 of
    Nil -> s2
    Mature a tl -> Mature a (s2 <|> tl)
    Immature fs -> Immature (s2 <|> fs)
  
instance Monad Stream where
  s >>= f = case s of
    Nil -> Nil
    Mature a tl -> (f a) <|> (tl >>= f)
    Immature fs  -> Immature (fs >>= f)

instance MonadPlus Stream where
  mzero = empty
  mplus = (<|>)
  
type State = (T.Subst, Int)
type Goal  = State -> Stream State

infix 4 ===

(===) :: T.T -> T.T -> Goal
t1 === t2 = \(subst, n) -> case U.unify (Just subst) t1 t2 of
      Nothing -> Nil
      Just subst' -> pure (subst', n)

infixr 3 &&&

(&&&) :: Goal -> Goal -> Goal
g1 &&& g2 = \state -> (g1 state) >>= g2

infixr 2 |||

(|||) :: Goal -> Goal -> Goal
g1 ||| g2 = \state -> (g1 state) <|> (g2 state)

call_fresh :: (T.T -> Goal) -> Goal
call_fresh f = \(subst, n) -> f (T.V n) (subst, n + 1)

delay :: Goal -> Goal
delay f s = Immature (f s)

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
       

