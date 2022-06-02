module Identification where

import Data.Set (member)
import FreeVar
import Grammar

instance Eq TypedVar where
  (TypedVar x ϕ) == (TypedVar y ψ) = (x == y) && (ϕ == ψ)

instance Eq Type where
  (Type a) == (Type b) = a == b
  (SuchThat ϕ m) == (SuchThat ψ n) = (ϕ == ψ) && (m == n)
  (Forall (TypedVar x σ) ϕ) == (Forall (TypedVar y τ) ψ)
    | not (x `member` fv ϕ) && not (y `member` fv ψ) = (σ == τ) && (ϕ == ψ)
    | otherwise = (x == y) && (σ == τ) && (ϕ == ψ)
  (And ϕ ψ) == (And α β) = (ϕ == α) && (ψ == β)
  (Or ϕ ψ) == (Or α β) = (ϕ == α) && (ψ == β)
  _ == _ = False

instance Eq Term where
  (Term x) == (Term y) = x == y
  (Lambda x m) == (Lambda y n) = (x == y) && (m == n)
  (Applied m n) == (Applied p q) = (m == p) && (n == q)
  (Pair m n) == (Pair p q) = (m == p) && (n == q)
  (OneOf a b c) == (OneOf d e f) = (a == d) && (b == e) && (c == f)
  (Case a b c) == (Case d e f) = (a == d) && (b == e) && (c == f)
  _ == _ = False
