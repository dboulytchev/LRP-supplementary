-- Supplementary materials for the course of logic and relational programming, 2025
-- (C) Dmitry Boulytchev, dboulytchev@gmail.com
-- MicroKanren.

module MK where

import qualified Data.Map as Map
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
  pure      = flip Mature $ Nil
  (<*>) = ap

instance Alternative Stream where
  empty              = Nil
  Nil <|> bs         = bs
  Mature a as <|> bs = Mature a $ bs <|> as 
  Immature as <|> bs = Immature $ bs <|> as
  
instance Monad Stream where
  Nil >>= _         = Nil
  Mature a as >>= f = f a <|> (as >>= f)
  Immature as >>= f = Immature $ as >>= f

instance MonadPlus Stream where
  mzero = empty
  mplus = (<|>)
  
type State = (T.Subst, Int)
type Goal  = State -> Stream State

infix 4 ===

dapp :: T.Subst -> T.T -> T.T
dapp s t = case U.walk s t of T.C cst ts -> T.C cst $ fmap (dapp s) ts
                              T.V v      -> T.V v
prep :: T.Subst -> T.Subst 
prep s = foldl (\cs v -> T.put cs v (dapp s $ T.V v)) Map.empty $ Map.keys s

(===) :: T.T -> T.T -> Goal
t1 === t2 = \(s, i) -> fromMaybe Nil $ fmap (\x -> pure (x, i)) $ fmap prep $ U.unify (Just s) t1 t2

infixr 3 &&&

(&&&) :: Goal -> Goal -> Goal
g1 &&& g2 = \s -> g1 s >>= g2

infixr 2 |||

(|||) :: Goal -> Goal -> Goal
g1 ||| g2 = \s -> g1 s <|> g2 s

call_fresh :: (T.T -> Goal) -> Goal
call_fresh f (s, i) = (f $ T.V i) (s, i + 1)

delay :: Goal -> Goal
delay f s = Immature $ f s

--- Initial state & run
initial = (T.empty, 1000)
peep x (s, _) = map (T.apply s) x
run peeper goal = map peeper $ pick (-1) $ goal initial
run_n n peeper goal = map peeper $ pick n $ goal initial

------------------------------------------
--- Some relations for natural numbers ---
------------------------------------------

--- Some predefined variables
x = T.V 0
y = T.V 1
z = T.V 2

--- Terms
o      = T.C 0 []
s t    = T.C 1 [t]
e      = T.C 2 []
c t ts = T.C 3 [t, ts]

le x y = delay $
  call_fresh(\x' -> 
    add x x' y
  )

add x y z = delay $
  x === o &&& y === z |||
  call_fresh (\ x' ->
  call_fresh (\ z' ->
    x === s x' &&&
    z === s z' &&&
    add x' y z'
  ))

mul x y z = delay $
  y === o &&& z === o |||
  call_fresh(\ t ->
  call_fresh(\ y' ->
    y === s y' &&&
    add x t z  &&&
    mul x y' t
  ))

insert x xs ys = delay $
  xs === e &&& ys === c x e |||
  call_fresh(\x' -> 
  call_fresh(\y' ->
  call_fresh(\xs' -> 
  call_fresh(\ys' ->
    xs === c x' xs' &&&
    ys === c y' ys' &&& (
      le x x' &&& x === y' &&& xs === ys' |||
      le x' x &&& x' === y' &&& insert x xs' ys'
    )
  ))))

sort xs ys = delay $
  xs === e &&& ys === e |||
  call_fresh(\x' ->
  call_fresh(\xs' ->
  call_fresh(\ys' ->
    xs === c x' xs' &&&
    sort xs' ys'    &&&
    insert x' ys' ys
  )))

dummy x = delay $
  dummy x ||| x === x

s0 = run (peep [x])    (add (s o) (s o) x)
s1 = run (peep [x])    (add x (s o) (s (s o)))
s2 = run (peep [x, y]) (add x y (s (s o)))

zero = o
one = s zero
two = s one 
three = s two
six = s $ s $ s three

list3102 = c three $ c one $ c zero $ c two e
list0223 = c zero $ c two $ c two $ c three e

check_mul_3 = run_n 4 (peep [x, y]) (mul x y six) --- can find 4 solutions
check_dummy = run_n 1 (peep [x]) (dummy x)        --- can find 1 solution

sort0 = run (peep [x]) (sort e x)
sort1 = run (peep [x]) (sort list3102 x)
sort2 = run (peep [x]) (sort (c three $ c two $ c x $ c zero e) list0223)
