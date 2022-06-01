module Print where

import Data.Set (member)
import FreeVar (FV (fv))
import Grammar (Term (..), Type (..), TypedVar (..))

instance Show TypedVar where
  show (TypedVar x ϕ) = x ++ ":" ++ show ϕ

instance Show Type where
  show (Type s) = s
  show (SuchThat ϕ m) = show ϕ ++ show m
  show (Forall x@(TypedVar v σ) ϕ) =
    if v `member` fv ϕ
      then "∀" ++ show x ++ "." ++ show ϕ
      else show σ ++ " -> " ++ show ϕ
  show (And ϕ ψ) = show ϕ ++ "∧" ++ show ψ
  show (Or ϕ ψ) = show ϕ ++ "∨" ++ show ψ

instance Show Term where
  show (Term s) = s
  show (Lambda x m) = "λ" ++ show x ++ "." ++ show m
  show (Applied m n) =
    "(" ++ show m ++ ")"
      ++ if length (show n) > 1 then "(" ++ show n ++ ")" else show n
  show (Pair m n) = "⟨" ++ show m ++ ", " ++ show n ++ "⟩"
  show (OneOf ϕ ψ m) = case m of
    Left n -> show n
    Right n -> show n
  show (Case l (x, m) (y, n)) =
    "case ("
      ++ show l
      ++ "; "
      ++ show x
      ++ "."
      ++ show m
      ++ "; "
      ++ show y
      ++ "."
      ++ show n
      ++ ")"