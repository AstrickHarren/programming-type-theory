module FreeVar where

import Data.Set (Set, delete, empty, singleton, union)
import Grammar (Term (..), Type (..), TypedVar (TypedVar), Var)

class FV a where
  fv :: a -> Set Var

instance FV Term where
  -- FV(x) = {x}
  fv (Term x) = singleton x
  -- TODO: Prove this
  -- FV(λx:α.M) = FV(M) ∪ FV(α) - {x}
  fv (Lambda (TypedVar x _) m) = delete x (fv m)
  -- FV(MN) = FV(M) ∪ FV(N)
  fv (Applied m n) = fv m `union` fv n
  -- FV(⟨M, N⟩) = FV(M) ∪ FV(N)
  fv (Pair m n) = fv m `union` fv n
  -- TODO: Proof this
  -- FV(left_(ϕ∨ψ) M) = FV(ϕ) ∪ FV(ψ) ∪ FV(M)
  fv (OneOf ϕ ψ e) =
    fv ϕ `union` fv ψ `union` case e of
      Left m -> fv m
      Right m -> fv m
  -- FV(π1(M)) = FV(M)
  fv (Fst m) = fv m
  -- FV(π2(M)) == FV(M)
  fv (Snd m) = fv m
  -- FV(case(L; x.M; y.N)) = FV(L) ∪ (FV(M) - {x}) ∪ (FV(N) - {y})
  fv (Case l (x, m) (y, n)) =
    fv l `union` delete x (fv m) `union` delete y (fv n)

instance FV Type where
  -- FV(σ) = ∅
  fv (Type s) = empty
  -- FV(ϕM) = FV(M) ∪ FV(ϕ)
  fv (SuchThat ϕ m) = fv m `union` fv ϕ
  -- FV(∀x:ϕ.ψ) = FV(ϕ) ∪ FV(ψ) - {x}
  fv (Forall (TypedVar x ϕ) ψ) = delete x $ fv ϕ `union` fv ψ
  -- FV(ϕ∧ψ) = FV(ϕ) ∪ FV(ψ)
  fv (And ϕ ψ) = fv ϕ `union` fv ψ
  -- FV(ϕ∨ψ) = FV(ϕ) ∪ FV(ψ)
  fv (Or ϕ ψ) = fv ϕ `union` fv ψ
