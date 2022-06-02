{-# LANGUAGE BlockArguments #-}

module TypeCheck where

import Data.Maybe (fromJust)
import Grammar
  ( Context,
    Term (..),
    Type (And, Forall, Or),
    TypedVar (TypedVar),
  )
import Print ()
import Substitute (Substitute (sub))

typeOf :: Context -> Term -> Type
-- Γ, x:ϕ ⊢ x:ϕ
typeOf γ (Term x) = fromJust $ lookup x (map asTuple γ)
  where
    asTuple (TypedVar x t) = (x, t)
-- Γ, x: ϕ ⊢ M: ψ
------------------
-- Γ ⊢ λx:ϕ.M: ∀x:ϕ.ψ
typeOf γ (Lambda (TypedVar x ϕ) m) = Forall v (typeOf (v : γ) m)
  where
    v = x `TypedVar` ϕ
-- Γ ⊢ M: ∀x:ϕ.ψ, Γ ⊢ N: ϕ
---------------------------
-- Γ ⊢ MN: ψ[N/x]
typeOf γ t@(Applied m n) = case typeOf γ m of
  Forall (TypedVar x ϕ) ψ ->
    if typeOf γ n == ϕ
      then sub x n ψ
      else error $ "type check: applicant wrong type in applying " ++ show t
  _ -> error $ "type check: not func type in applying " ++ show t
-- Γ ⊢ M: ϕ, Γ ⊢ N: ψ
----------------------
-- Γ ⊢ ⟨M, N⟩: ϕ ∧ ψ
typeOf γ (Pair m n) = And (typeOf γ m) (typeOf γ n)
-- Γ ⊢ M: ϕ
----------------------
-- Γ ⊢ in_{ϕ∨ψ}(M): ϕ ∧ ψ
typeOf γ t@(OneOf ϕ ψ e) = case e of
  Left m -> checkOrigin m ϕ (Or ϕ ψ)
  Right m -> checkOrigin m ψ (Or ϕ ψ)
  where
    checkOrigin m ϕ σ =
      if typeOf γ m == ϕ
        then σ
        else error $ "type check: type has no origin in summing " ++ show t

-- Γ ⊢ L: ϕ ∨ ψ   Γ, x: ϕ ⊢ M: τ  Γ, y: ψ ⊢ N: τ
-------------------------------------------------
-- Γ ⊢ case(L;x.M;y.N) ⊢ τ
typeOf γ t@(Case l (x, m) (y, n)) = case typeOf γ l of
  (Or ϕ ψ) ->
    let leftType = typeOf ((x `TypedVar` ϕ) : γ) m
        rightType = typeOf ((y `TypedVar` ψ) : γ) m
     in if leftType == rightType then leftType else error $ "type check: case branches with different types in casing: " ++ show t
  _ -> error $ "type check: type not caseable in casing: " ++ show t
