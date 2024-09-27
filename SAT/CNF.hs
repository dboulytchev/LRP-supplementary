-- Supplementary materials for the course of logic and relational programming, 2021
-- (C) Dmitry Boulytchev, dboulytchev@gmail.com
-- Conjunctive normal forms.

module CNF where

import Formula
import Data.List
import Control.Monad.State.Lazy

-- A type for CNF: a list (conjunction) of lists (clauses) of
-- literas (positive or negative variable names)
type CNF = [[Var]]

-- Tseitin's conversion
toCNF :: Formula.F -> CNF
toCNF f = filter (/= []) $ (\tseitinsResult -> [fst $ snd tseitinsResult] : fst tseitinsResult) $ tseitins (Formula.maxVar f) f where
  tseitins :: Int -> Formula.F -> (CNF, (Var, Int))
  tseitins newVarOffset (Var var)        = ([[var]], (var, 0))
  tseitins newVarOffset (Neg (Var var))  = ([[-var]], (-var, 0))
  tseitins newVarOffset (Neg f)          = ([-newVar, -cVar] : [newVar, cVar] : childCNF, (newVar, 1 + cNewVars)) where
                                             (cCNF, (cVar, cNewVars)) = tseitins newVarOffset f 
                                             childCNF                 = if cNewVars == 0 then
                                                                          [[]]
                                                                        else
                                                                          cCNF
                                             newVar                   = if cNewVars == 0 then 
                                                                          newVarOffset + 1 
                                                                        else 
                                                                          cVar + 1
  tseitins newVarOffset (l :/\: r)       = (([-newVar, lVar] : [-newVar, rVar] : [newVar, -lVar, -rVar] : leftCNF) ++ rightCNF, (newVar, 1 + lNewVars + rNewVars)) where
                                             (lCNF, (lVar, lNewVars)) = tseitins newVarOffset l 
                                             leftCNF                  = if lNewVars == 0 then
                                                                          [[]]
                                                                        else
                                                                          lCNF
                                             rOffset                  = newVarOffset + lNewVars
                                             (rCNF, (rVar, rNewVars)) = tseitins rOffset r
                                             rightCNF                 = if rNewVars == 0 then
                                                                          [[]]
                                                                        else
                                                                          rCNF
                                             newVar                   = if rNewVars == 0 then 
                                                                          rOffset + 1 
                                                                        else 
                                                                          abs rVar + 1
  tseitins newVarOffset (l :\/: r)       = (([newVar, -lVar] : [newVar, -rVar] : [-newVar, lVar, rVar] : leftCNF) ++ rightCNF, (newVar, 1 + lNewVars + rNewVars)) where
                                             (lCNF, (lVar, lNewVars)) = tseitins newVarOffset l 
                                             leftCNF                  = if lNewVars == 0 then
                                                                          [[]]
                                                                        else
                                                                          lCNF
                                             rOffset                  = newVarOffset + lNewVars
                                             (rCNF, (rVar, rNewVars)) = tseitins rOffset r
                                             rightCNF                 = if rNewVars == 0 then
                                                                          [[]]
                                                                        else
                                                                          rCNF
                                             newVar                   = if rNewVars == 0 then 
                                                                          rOffset + 1 
                                                                        else 
                                                                          abs rVar + 1
  tseitins newVarOffset (l :=>: r)       = (([newVar, lVar] : [newVar, -rVar] : [-newVar, -lVar, rVar] : leftCNF) ++ rightCNF, (newVar, 1 + lNewVars + rNewVars)) where
                                             (lCNF, (lVar, lNewVars)) = tseitins newVarOffset l 
                                             leftCNF                  = if lNewVars == 0 then
                                                                          [[]]
                                                                        else
                                                                          lCNF
                                             rOffset                  = newVarOffset + lNewVars
                                             (rCNF, (rVar, rNewVars)) = tseitins rOffset r
                                             rightCNF                 = if rNewVars == 0 then
                                                                          [[]]
                                                                        else
                                                                          rCNF
                                             newVar                   = if rNewVars == 0 then 
                                                                          rOffset + 1 
                                                                        else 
                                                                          abs rVar + 1
  tseitins newVarOffset (l :<=>: r)      = (([newVar, lVar, rVar] : [newVar, -lVar, -rVar] : [-newVar, -lVar, rVar] : [-newVar, lVar, -rVar] : leftCNF) ++ rightCNF, (newVar, 1 + lNewVars + rNewVars)) where
                                             (lCNF, (lVar, lNewVars)) = tseitins newVarOffset l 
                                             leftCNF                  = if lNewVars == 0 then
                                                                          [[]]
                                                                        else
                                                                          lCNF
                                             rOffset                  = newVarOffset + lNewVars
                                             (rCNF, (rVar, rNewVars)) = tseitins rOffset r
                                             rightCNF                 = if rNewVars == 0 then
                                                                          [[]]
                                                                        else
                                                                          rCNF
                                             newVar                   = if rNewVars == 0 then 
                                                                          rOffset + 1 
                                                                        else 
                                                                          abs rVar + 1


-- The inverse conversion
fromCNF :: CNF -> Formula.F
fromCNF (h : tl) = foldl (\ acc c -> acc :/\: fromClause c) (fromClause h) tl where
  fromClause (h : tl)  = foldl (\ acc v -> acc :\/: fromVar v) (fromVar h) tl
  fromVar n | n < 0     = Neg $ Var (-n)
            | otherwise = Var n

-- The equisatisfability of Tseitin's conversion
equisaT :: F -> Bool
equisaT f = Formula.equisat f (fromCNF $ CNF.toCNF f)

-- Tseitin's conversion gives a CNF
isCNF :: F -> Bool
isCNF = Formula.isCNF . fromCNF . CNF.toCNF 
