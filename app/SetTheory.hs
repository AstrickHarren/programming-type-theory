module SetTheory where

import Data.List (mapAccumL)
import Grammar
import TypeCheck
import Util hiding (forall)
import qualified Util

--- Definitions
set = flip TypedVar $ Type "S"

empty = Term "∅"

equals a b = binaryType "=" (Term a) (Term b)

memberOf a b = binaryType "∈" (Term a) (Term b)

subsetOf a b = binaryType "⊂" (Term a) (Term b)

infixl 8 ∈

(∈) = memberOf

infixl 8 ⊂

(⊂) = subsetOf

infixl 6 ===

(===) = equals

-- Utils

-- overload `for all` as `for all sets`
forall :: [Var] -> Type -> Type
forall = Util.forall . map set

-- Axiomatic Defs

equalDef =
  forall ["A", "B"] $
    "A" === "B"
      --> forall
        ["x"]
        ((("x" ∈ "A") --> ("x" ∈ "B")) `And` (("x" ∈ "B") --> ("x" ∈ "A")))

equalItrp =
  forall ["A", "B"] $
    "A" === "B"
      <-- forall
        ["x"]
        ((("x" ∈ "A") --> ("x" ∈ "B")) `And` (("x" ∈ "B") --> ("x" ∈ "A")))

subsetDef =
  forall ["A", "B"] $
    "A" ⊂ "B" --> forall ["x"] ("x" ∈ "A") --> ("x" ∈ "B")

subsetItrp =
  forall ["A", "B"] $
    "A" ⊂ "B" <-- forall ["x"] ("x" ∈ "A") --> ("x" ∈ "B")

-- Inductive Proving
type Axiom = TypedVar

type Claim = TypedVar

type Proof = Term

type Theorem = (Claim, Proof)

inductiveProof :: [Axiom] -> [Theorem] -> [Either String String]
inductiveProof axioms theorems =
  snd $
    mapAccumL
      ( \context (claim@(TypedVar name theorem), proof) ->
          ( claim : context,
            if typeOf context proof == theorem then Right name else Left name
          )
      )
      axioms
      theorems