module Substitute where

import Data.Set (Set, difference, elemAt, member, union)
import FreeVar
import Grammar

-- returns a var not in the given set (from the global alphaBet)
varNotIn :: Set Var -> Var
varNotIn = elemAt 0 . difference alphaBet

class Substitute a where
  sub :: Var -> Term -> a -> a

subsub :: Substitute a => Var -> Var -> Term -> a -> a
subsub x z n m = sub z n (sub x (Term z) m)

instance Substitute Term where
  -- x[N/x] = N; x[N/y] = x;
  sub y n t@(Term x) = if x == y then n else t
  -- (λx:τ.M)[N/x] = (λx:τ.M);
  -- (λx:τ.M)[N/y] = (λz:τ[N/z].M[z/x][N/z]) w/ z ∉ FV(N) ∪ FV(M) ∪ FV(τ) if x ∈ FV(N)
  -- (λx:τ.M)[N/y] = (λx:τ[N/y].M[N/y]) if x ∉ FV(N)
  sub y n t@(Lambda (TypedVar x τ) m)
    | x == y = t
    | x `member` fv n =
      let z = varNotIn (fv t `union` fv n)
       in Lambda (z `TypedVar` subsub x z n τ) (subsub x z n m)
    | otherwise = Lambda (x `TypedVar` τ) (sub y n m)
  -- (PQ)[N/y] = (P[N/y])(Q[N/y])
  sub y n (Applied p q) = Applied (sub y n p) (sub y n q)
  -- ⟨P, Q⟩[N/y] = ⟨P[N/y], Q[N/y]⟩
  sub y n (Pair p q) = Pair (sub y n p) (sub y n q)
  -- in_(ϕ∨ψ)(M)[N/y] = in_(ϕ[N/y]∨ψ[N/y])(M[N/y])
  sub y n (OneOf ϕ ψ o) = OneOf (sub y n ϕ) (sub y n ψ) $ case o of
    Left m -> Left $ sub y n m
    Right m -> Right $ sub y n m
  -- case(L;x.P;y.Q)[N/z] = case(L[N/z];(x.P)[N/z];(y.Q)[N/z])
  -- (x.M)[N/x] = (x.M)
  -- (x.M)[N/y] = (z.M[z/x][N/z]) w/ z ∉ FV(N) ∪ FV(M) if x ∈ FV(N)
  -- (x.M)[N/y] = (x.M[N/y]) if x ∉ FV(N)
  sub z n (Case l (x, p) (y, q)) =
    Case
      (sub z n l)
      (sub' z n (x, p))
      (sub' z n (y, q))
    where
      sub' y n t@(x, m)
        | x == y = t
        | x `member` fv n =
          let z = varNotIn (fv n `union` fv m)
           in (x, subsub x z n m)
        | otherwise = (x, sub y n m)

instance Substitute Type where
  -- α[N/x] = α
  sub _ _ t@(Type s) = t
  -- (ϕM)[N/x] = ϕ[N/x]M[N/x]
  sub x n (SuchThat ϕ m) = SuchThat (sub x n ϕ) (sub x n m)
  -- (∀x:ϕ.ψ)[N/x] = (∀x:ϕ.ψ)[N/x]
  -- (∀x:ϕ.ψ)[N/y] = (∀z:ϕ[z/x][N/z].ψ[z/x][N/z]) w/ z ∉ FV(ϕ) ∪ FV(ψ) ∪ FV(N) if x ∈ FV(N)
  -- (∀x:ϕ.ψ)[N/y] = (∀x:ϕ[N/y].ψ[N/y]) o.w.
  sub y n t@(Forall (TypedVar x ϕ) ψ)
    | x == y = t
    | x `member` fv n =
      let z = varNotIn (fv t `union` fv n)
       in Forall (z `TypedVar` subsub x z n ϕ) (subsub x z n ψ)
    | otherwise = Forall (x `TypedVar` sub y n ϕ) (sub y n ψ)
  -- (ϕ ∧ ψ)[N/x] = (ϕ[N/x] ∧ ψ[N/x])
  sub x n (And ϕ ψ) = And (sub x n ϕ) (sub x n ψ)
  -- (ϕ ∨ ψ)[N/x] = (ϕ[N/x] ∨ ψ[N/x])
  sub x n (Or ϕ ψ) = Or (sub x n ϕ) (sub x n ψ)