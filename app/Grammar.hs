module Grammar where

import Data.Set (Set, fromList, member)

type Var = String

data TypedVar = TypedVar Var Type

-- Lambda calculus
data Term
  = Term Var -- x
  | Lambda TypedVar Term -- λx:α.M
  | Applied Term Term -- MN
  | Pair Term Term -- (x, y)
  | OneOf Type Type (Either Term Term) -- left_ϕ∨ψ(x)
  | Case Term (Var, Term) (Var, Term) -- case(L; x.M; y.N)

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
