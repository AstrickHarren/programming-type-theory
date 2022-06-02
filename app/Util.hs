module Util where

import Data.Set (union)
import FreeVar (FV (fv))
import Grammar
import Substitute (varNotIn)

binaryType :: String -> Term -> Term -> Type
binaryType p x = SuchThat (SuchThat (Type p) x)

forall :: [TypedVar] -> Type -> Type
forall xs ϕ = foldr Forall ϕ xs

implies :: Type -> Type -> Type
implies a b =
  let z = varNotIn (fv a `union` fv b)
   in Forall (z `TypedVar` a) b

iff :: Type -> Type -> Type
iff a b = And (a `implies` b) (b `implies` a)