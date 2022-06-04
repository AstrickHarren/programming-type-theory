module Identification where

import Data.Set (member)
import FreeVar
import Grammar
import Substitute (Substitute (sub))

instance Eq TypedVar where
  (TypedVar x ϕ) == (TypedVar y ψ) = x == y && ϕ == ψ

instance Eq Type where
  (Type a) == (Type b) = a == b
  (SuchThat ϕ m) == (SuchThat ψ n) = ϕ == ψ && m == n
  (Forall (TypedVar x σ) ϕ) == (Forall (TypedVar y τ) ψ) = sub x (Term y) ϕ == ψ
  (And ϕ ψ) == (And α β) = ϕ == α && ψ == β
  (Or ϕ ψ) == (Or α β) = ϕ == α && ψ == β
  _ == _ = False

instance Eq Term where
  (Term x) == (Term y) = x == y
  (Lambda (TypedVar x σ) m) == (Lambda (TypedVar y τ) n) = sub x (Term y) m == n
  (Applied m n) == (Applied p q) = m == p && n == q
  (Pair m n) == (Pair p q) = m == p && n == q
  (OneOf a b c) == (OneOf d e f) = a == d && b == e && c == f
  (Fst a) == (Fst b) = a == b
  (Snd a) == (Snd b) = a == b
  (Case a (x, α) (y, β)) == (Case d (v, ϕ) (w, ψ)) = a == d && sub x (Term v) α == ϕ && sub y (Term w) β == ψ
  _ == _ = False
