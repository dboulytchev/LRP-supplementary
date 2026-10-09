-- Supplementary materials for the course of logic and relational programming, 2021
-- (C) Dmitry Boulytchev, dboulytchev@gmail.com
-- Terms.

module Term where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List
import Test.QuickCheck
import Debug.Trace

-- Type synonyms for constructor and variable names
type Cst = Int
type Var = Int

-- A type for terms: either a constructor applied to subterms
-- or a variable
data T = C Cst [T] | V Var deriving (Show, Eq)

-- A class type for converting data structures to/from
-- terms
class Term a where
   toTerm   :: a -> T
   fromTerm :: T -> a
  
-- Free variables for a term; returns a sorted list
fv :: T -> Set.Set Int
fv t0 = go [t0] Set.empty
  where
    go :: [T] -> Set.Set Var -> Set.Set Var
    go []        !acc = acc
    go (t : ts)  !acc = case t of
      V v       -> go ts (Set.insert v acc)
      C _ subts -> go (subts ++ ts) acc

-- QuickCheck instantiation for formulas
-- Don't know how to restrict the number of variables/constructors yet
numVar = 10
numCst = 10

-- "Arbitrary" instantiation for terms
instance Arbitrary T where
  shrink (V _)        = []
  shrink (C cst subs) = subs ++ [ C cst subs' | subs' <- shrink subs ]
  arbitrary = sized f where
    f :: Int -> Gen T
    f 0 = num numVar >>= return . V
    f 1 = do cst <- num numCst
             return $ C cst []      
    f n = do m   <- pos (n - 1)
             ms  <- split n m
             cst <- num numCst
             sub <- mapM f ms
             return $ C cst sub
    num   n   = (resize n arbitrary :: Gen (NonNegative Int)) >>= return . getNonNegative
    pos   n   = (resize n arbitrary :: Gen (Positive    Int)) >>= return . getPositive
    split m n = iterate [] m n 
    iterate acc rest 1 = return $ rest : acc
    iterate acc rest i = do k <- num rest
                            iterate (k : acc) (rest - k) (i-1) 

-- A type for a substitution: a (partial) map from
-- variable names to terms. Note, this not neccessarily  
-- represents an idempotent substitution
type Subst = Map.Map Var T

-- Empty substitution
empty :: Subst
empty = Map.empty

-- Lookups a substitution
lookup :: Subst -> Var -> Maybe T
lookup = flip Map.lookup 

-- Adds in a substitution
put :: Subst -> Var -> T -> Subst
put s v t = Map.insert v t s

-- A class of substitutable types
class Substitutable a where
  apply :: Subst -> a -> a

data Work
  = Process T
  | Build Cst Int

-- Apply a substitution to a term
instance Substitutable T where
  apply s t = go [Process t] []
    where
      go :: [Work] -> [T] -> T
      go []        (r : _) = r
      go (w : ws)  !results = case w of
        Process (V v) ->
          case Term.lookup s v of
            Just t' -> go ws (t' : results)
            Nothing -> go ws (V v : results)
        Process (C cst subs) ->
          go (map Process (reverse subs) ++ (Build cst (length subs) : ws))
              results
        Build cst n ->
          let (children, rest) = splitAt n results
          in go ws (C cst children : rest)

-- Occurs check: checks if a substitution contains a circular
-- binding

data Task = Enter Var | Exit Var

occurs :: Subst -> Bool
occurs s = go initialStack Set.empty Set.empty
  where
    initialStack = [Enter v | v <- Map.keys s]
    go :: [Task] -> Set.Set Var -> Set.Set Var -> Bool
    go [] !_ !_ = False
    go (task : rest) !visiting !done = case task of
      Enter v
        | v `Set.member` visiting -> True
        | v `Set.member` done     -> go rest visiting done
        | otherwise ->
            case Term.lookup s v of
              Nothing    -> go rest visiting (Set.insert v done)
              Just (V v) -> go rest visiting (Set.insert v done)
              Just t     ->
                let deps     = Set.toList (fv t)
                    newStack = map Enter deps ++ [Exit v] ++ rest
                in go newStack (Set.insert v visiting) done
      Exit v ->
        go rest (Set.delete v visiting) (Set.insert v done)

-- Well-formedness: checks if a substitution does not contain
-- circular bindings
wf :: Subst -> Bool
wf = not . occurs

-- A composition of substitutions; the substitutions are
-- assumed to be well-formed
infixl 6 <+>

(<+>) :: Subst -> Subst -> Subst
s <+> p = foldr step p (Map.toList s)
  where
    step (v, t) acc = put acc v (apply p t)

-- A condition for substitution composition s <+> p: dom (s) \cap ran (p) = \emptyset
compWF :: Subst -> Subst -> Bool
compWF s p = Set.null $
    Set.intersection
      (Map.keysSet s)
      (Set.unions (map fv (Map.elems p)))

-- A property: for all substitutions s, p and for all terms t
--     (t s) p = t (s <+> p)
checkSubst :: (Subst, Subst, T) -> Bool
checkSubst (s, p, t) =
  not (wf s) || not (wf p) || not (compWF s p) || (apply p . apply s $ t) == apply (s <+> p) t

-- This check should pass:
qcEntry = quickCheck $ withMaxSuccess 1000 $ (\ x -> within 100000000 $ checkSubst x)
