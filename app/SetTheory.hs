module SetTheory where

import Data.List (mapAccumL)
import Grammar
import TypeCheck
import Util hiding (forall, forany)
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

-- overload `for any` as `for any sets`
forany = Util.forany . map set

proof :: Claim -> Proof -> Theorem
proof = (,)

infixr 1 =::

(=::) = is

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

verifyThms = inductiveProof axioms theorems

whatDoesItActuallyProve :: [Axiom] -> [Theorem] -> [TypedVar]
whatDoesItActuallyProve axioms thms =
  snd $
    mapAccumL
      ( \context (claim@(TypedVar name thm), proof) ->
          (claim : context, typeOf context proof `as` name)
      )
      axioms
      thms

-- Axiomatic Defs
axioms =
  [ "def of equality"
      =:: forall
        ["A", "B"]
        ( "A" === "B"
            --> forall
              ["x"]
              ((("x" ∈ "A") --> ("x" ∈ "B")) `And` (("x" ∈ "B") --> ("x" ∈ "A")))
        ),
    "itrp of equality"
      =:: forall
        ["A", "B"]
        ( "A" === "B"
            <-- forall
              ["x"]
              ((("x" ∈ "A") --> ("x" ∈ "B")) `And` (("x" ∈ "B") --> ("x" ∈ "A")))
        ),
    "def of subset"
      =:: forall
        ["A", "B"]
        ("A" ⊂ "B" --> forall ["x"] (("x" ∈ "A") --> ("x" ∈ "B"))),
    "itrp of subset"
      =:: forall
        ["A", "B"]
        ("A" ⊂ "B" <-- forall ["x"] (("x" ∈ "A") --> ("x" ∈ "B")))
  ]

-- Theorems

theorems =
  [ ( "two way subset implies equality"
        =:: forall
          ["A", "B"]
          ((("A" ⊂ "B") `And` ("B" ⊂ "A")) --> ("A" === "B"))
    )
      `proof` forany
        ["A", "B"]
        ( suppose
            [("A" ⊂ "B" ∧ "B" ⊂ "A") `as` "assumption"]
            $ because
              [ forany
                  ["x"]
                  ( because
                      [Fst $ Term "assumption"]
                      (("A" ⊂ "B") `as` "A ⊂ B")
                      ( because
                          [Term "def of subset" `instantiatedWith` [Term "A", Term "B", Term "A ⊂ B", Term "x"]]
                          ((("x" ∈ "A") --> ("x" ∈ "B")) `as` "equality left")
                          ( because
                              [Snd $ Term "assumption"]
                              (("B" ⊂ "A") `as` "B ⊂ A")
                              ( because
                                  [Term "def of subset" `instantiatedWith` [Term "B", Term "A", Term "B ⊂ A", Term "x"]]
                                  ((("x" ∈ "B") --> ("x" ∈ "A")) `as` "equality right")
                                  (Term "equality left" `Pair` Term "equality right")
                              )
                          )
                      )
                  )
              ]
              (forall ["x"] ((("x" ∈ "A") --> ("x" ∈ "B")) ∧ (("x" ∈ "B") --> ("x" ∈ "A"))) `as` "equality")
              (Term "itrp of equality" `instantiatedWith` [Term "A", Term "B", Term "equality"])
        ),
    ("equality implies subset" =:: forall ["A", "B"] (("A" === "B") --> ("A" ⊂ "B")))
      `proof` forany
        ["A", "B"]
        ( suppose [("A" === "B") `as` "assumption"] $
            because
              [ forany ["x"] $
                  because
                    [Fst $ Term "def of equality" `instantiatedWith` [Term "A", Term "B", Term "assumption", Term "x"]]
                    ((("x" ∈ "A") --> ("x" ∈ "B")) `as` "subseting(x)")
                    (Term "subseting(x)")
              ]
              (forall ["x"] ("x" ∈ "A" --> "x" ∈ "B") `as` "subseting")
              (Term "itrp of subset" `instantiatedWith` [Term "A", Term "B", Term "subseting"])
        ),
    ("equality is symmetric" =:: forall ["A", "B"] ("A" === "B" --> "B" === "A"))
      `proof` forany
        ["A", "B"]
        ( suppose
            [("A" === "B") `as` "assumption"]
            ( because
                [ forany
                    ["x"]
                    ( because
                        [Term "def of equality" `at` ["A", "B", "assumption", "x"]]
                        ( (("x" ∈ "A" --> "x" ∈ "B") ∧ ("x" ∈ "B" --> "x" ∈ "A"))
                            `as` "proof of A = B with x"
                        )
                        ( because
                            [Snd (Term "proof of A = B with x") `Pair` Fst (Term "proof of A = B with x")]
                            ((("x" ∈ "B" --> "x" ∈ "A") ∧ ("x" ∈ "A" --> "x" ∈ "B")) `as` "proof of B = A with x")
                            (Term "proof of B = A with x")
                        )
                    )
                ]
                (forall ["x"] (("x" ∈ "B" --> "x" ∈ "A") ∧ ("x" ∈ "A" --> "x" ∈ "B")) `as` "proof of B = A")
                (Term "itrp of equality" `at` ["B", "A", "proof of B = A"])
            )
        ),
    ("equality implies twoway subset" =:: forall ["A", "B"] ("A" === "B" --> ("A" ⊂ "B") ∧ ("B" ⊂ "A")))
      `proof` forany
        ["A", "B"]
        ( suppose [("A" === "B") `as` "assumption"] $
            because
              [Term "equality implies subset" `at` ["A", "B", "assumption"]]
              (("A" ⊂ "B") `as` "A ⊂ B")
              $ because
                [Term "equality is symmetric" `at` ["A", "B", "assumption"]]
                (("B" === "A") `as` "B = A")
                $ because
                  [Term "equality implies subset" `at` ["B", "A", "B = A"]]
                  (("B" ⊂ "A") `as` "B ⊂ A")
                  (Term "A ⊂ B" `Pair` Term "B ⊂ A")
        )
  ]