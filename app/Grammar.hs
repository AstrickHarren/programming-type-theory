module Grammar where

import Data.Set (Set, fromList)

type Var = String

data TypedVar = TypedVar Var Type

-- Lambda calculus
data Term
  = Term String -- x
  | Lambda TypedVar Term -- λx:α.M
  | Applied Term Term -- MN
  | Pair Term Term -- (x, y)
  | OneOf Type Type (Either Term Term) -- left_ϕ∨ψ(x)

-- Types
data Type
  = Type String -- ϕ
  | SuchThat Type Term -- ϕM
  | Forall TypedVar Type -- ∀x:ϕ.ψ
  | And Type Type -- ϕ∧ψ
  | Or Type Type -- ϕ∨ψ

-- Variable alphabet
alphaBet :: Set String
alphaBet = fromList $ map (: []) ['a' .. 'z']

-- Context
type Context = [TypedVar]

-- Show

instance Show TypedVar where
  show (TypedVar x ϕ) = show x ++ ":" ++ show ϕ

instance Show Type where
  show (Type s) = s
  show (SuchThat ϕ m) = show ϕ ++ show m
  show (Forall x ϕ) = "∀" ++ show x ++ "." ++ show ϕ
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
    Left n -> "(" ++ show m ++ " as " ++ show (ϕ `Or` ψ) ++ ")"
    Right n -> "(" ++ show m ++ " as " ++ show (ϕ `Or` ψ) ++ ")"