module Util where

import Data.Set (union)
import FreeVar (FV (fv))
import Grammar
import Substitute (varNotIn)

is :: Var -> Type -> TypedVar
is = TypedVar

as :: Type -> Var -> TypedVar
as = flip TypedVar

aProofOf :: Var -> Type -> TypedVar
aProofOf = TypedVar

-- Type related
binaryType :: String -> Term -> Term -> Type
binaryType p x = SuchThat (SuchThat (Type p) x)

forall :: [TypedVar] -> Type -> Type
forall xs ϕ = foldr Forall ϕ xs

implies :: Type -> Type -> Type
implies a b =
  let z = varNotIn (fv a `union` fv b)
   in Forall (z `TypedVar` a) b

isImpliedBy :: Type -> Type -> Type
isImpliedBy = flip implies

infixr 1 -->

(-->) :: Type -> Type -> Type
(-->) = implies

infixr 1 <--

(<--) :: Type -> Type -> Type
(<--) = isImpliedBy

infixl 5 ∧

(∧) :: Type -> Type -> Type
(∧) = And

infixl 5 ∨

(∨) :: Type -> Type -> Type
(∨) = Or

iff :: Type -> Type -> Type
iff a b = And (a `implies` b) (b `implies` a)

-- Term related
forany :: [TypedVar] -> Term -> Term
forany = flip $ foldr Lambda

instantiatedWith :: Term -> [Term] -> Term
-- instantiatedWith m [] = m
-- instantiatedWith m (x : xs) = Applied (instantiatedWith m xs) x
instantiatedWith = foldl Applied

since :: Type -> Var -> Term -> Term
since p x = forany [x `is` p]

suppose = forany

because = suppose