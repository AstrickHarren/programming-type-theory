{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Move brackets to avoid $" #-}
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

equalsTerm = binaryType "="

memberOf a b = binaryType "∈" (Term a) (Term b)

memberOfTerm = binaryType "∈"

subsetOf a b = binaryType "⊂" (Term a) (Term b)

subsetOfTerm = binaryType "⊂"

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
        ("A" ⊂ "B" <-- forall ["x"] (("x" ∈ "A") --> ("x" ∈ "B"))),
    "pair"
      =:: forall ["x", "y"] (Type "S"),
    "def of axiom of pair"
      =:: forall
        ["x", "y", "z"]
        ((Term "z" `memberOfTerm` (Term "pair" `at` ["x", "y"])) --> ("z" === "x" ∨ "z" === "y")),
    "itrp of axiom of pair"
      =:: forall
        ["x", "y", "z"]
        ((Term "z" `memberOfTerm` (Term "pair" `at` ["x", "y"])) <-- ("z" === "x" ∨ "z" === "y"))
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
        ),
    ("subset is reflexive" =:: forall ["A"] ("A" ⊂ "A"))
      `proof` forany
        ["A"]
        ( because
            [ forany ["x"] $
                suppose
                  [("x" ∈ "A") `as` "x ∈ A"]
                  $ Term "x ∈ A"
            ]
            (forall ["x"] (("x" ∈ "A") --> ("x" ∈ "A")) `as` "proof of reflexivity")
            $ Term "itrp of subset" `at` ["A", "A", "proof of reflexivity"]
        ),
    ("subset is transitive" =:: forall ["A", "B", "C"] ((("A" ⊂ "B") ∧ ("B" ⊂ "C")) --> ("A" ⊂ "C")))
      `proof` forany
        ["A", "B", "C"]
        ( suppose [(("A" ⊂ "B") ∧ ("B" ⊂ "C")) `as` "assumption"] $
            because
              [ forany ["x"] $
                  because
                    [Fst $ Term "assumption"]
                    (("A" ⊂ "B") `as` "A ⊂ B")
                    $ because
                      [Snd $ Term "assumption"]
                      (("B" ⊂ "C") `as` "B ⊂ C")
                      $ because
                        [Term "def of subset" `at` ["A", "B", "A ⊂ B", "x"]]
                        (("x" ∈ "A" --> "x" ∈ "B") `as` "proof of A ⊂ B with x")
                        $ because
                          [Term "def of subset" `at` ["B", "C", "B ⊂ C", "x"]]
                          (("x" ∈ "B" --> "x" ∈ "C") `as` "proof of B ⊂ C with x")
                          $ suppose [("x" ∈ "A") `as` "x ∈ A"] $
                            -- Replace `instantiatedWith` with better interface
                            Term "proof of B ⊂ C with x"
                              `instantiatedWith` [Term "proof of A ⊂ B with x" `at` ["x ∈ A"]]
              ]
              (forall ["x"] ("x" ∈ "A" --> "x" ∈ "C") `as` "proof of A ⊂ C")
              (Term "itrp of subset" `at` ["A", "C", "proof of A ⊂ C"])
        ),
    ("equality is reflexive" =:: forall ["A"] ("A" === "A"))
      `proof` forany
        ["A"]
        ( because
            [Term "subset is reflexive" `at` ["A"]]
            (("A" ⊂ "A") `as` "A ⊂ A")
            $ Term "two way subset implies equality" `instantiatedWith` [Term "A", Term "A", Term "A ⊂ A" `Pair` Term "A ⊂ A"]
        ),
    ("equality is transitive" =:: forall ["A", "B", "C"] (("A" === "B" ∧ "B" === "C") --> ("A" === "C")))
      `proof` because
        [ forany ["A", "B", "C"] $
            suppose [("A" === "B" ∧ "B" === "C") `as` "assumption"] $
              because [Fst $ Term "assumption"] (("A" === "B") `as` "A = B") $
                because [Snd $ Term "assumption"] (("B" === "C") `as` "B = C") $
                  because [Term "equality implies subset" `at` ["A", "B", "A = B"]] (("A" ⊂ "B") `as` "A ⊂ B") $
                    because [Term "equality implies subset" `at` ["B", "C", "B = C"]] (("B" ⊂ "C") `as` "B ⊂ C") $
                      Term "subset is transitive" `at` ["A", "B", "C"] `instantiatedWith` [Term "A ⊂ B" `Pair` Term "B ⊂ C"]
        ]
        (forall ["A", "B", "C"] (("A" === "B" ∧ "B" === "C") --> ("A" ⊂ "C")) `as` "forward proof")
        ( because
            [ forany ["A", "B", "C"] $
                suppose [("A" === "B" ∧ "B" === "C") `as` "assumption"] $
                  because
                    [ Term "equality is symmetric" `instantiatedWith` [Term "B", Term "C", Snd $ Term "assumption"]
                        `Pair` (Term "equality is symmetric" `instantiatedWith` [Term "A", Term "B", Fst $ Term "assumption"])
                    ]
                    (("C" === "B" ∧ "B" === "A") `as` "symmetric assumption")
                    (Term "forward proof" `at` ["C", "B", "A", "symmetric assumption"])
            ]
            (forall ["A", "B", "C"] (("A" === "B" ∧ "B" === "C") --> ("C" ⊂ "A")) `as` "backward proof")
            $ forany ["A", "B", "C"] $
              suppose [("A" === "B" ∧ "B" === "C") `as` "assumption"] $
                Term "two way subset implies equality"
                  `instantiatedWith` [ Term "A",
                                       Term "C",
                                       Term "forward proof" `at` ["A", "B", "C", "assumption"]
                                         `Pair` (Term "backward proof" `at` ["A", "B", "C", "assumption"])
                                     ]
        ),
    ( "pair is well defined"
        =:: forall
          ["x", "y", "a", "b"]
          ( ("x" === "a" ∧ "y" === "b")
              --> (Term "pair" `at` ["x", "y"]) `equalsTerm` (Term "pair" `at` ["a", "b"])
          )
    )
      `proof` ( because
                  [ forany
                      ["x", "y", "a", "b"]
                      $ suppose [("x" === "a" ∧ "y" === "b") `as` "assumption"] $
                        because [Fst $ Term "assumption"] (("x" === "a") `as` "x = a") $
                          because [Snd $ Term "assumption"] (("y" === "b") `as` "y = b") $
                            because
                              [ forany ["z"] $
                                  suppose [(Term "z" `memberOfTerm` (Term "pair" `at` ["x", "y"])) `as` "z ∈ {x, y}"] $
                                    because
                                      [Term "def of axiom of pair" `at` ["x", "y", "z", "z ∈ {x, y}"]]
                                      (("z" === "x" ∨ "z" === "y") `as` "proof of z ∈ {x, y}")
                                      $ because
                                        [ Case
                                            (Term "proof of z ∈ {x, y}")
                                            ( "z = x",
                                              because [Term "equality is transitive" `instantiatedWith` [Term "z", Term "x", Term "a", Term "z = x" `Pair` Term "x = a"]] (("z" === "a") `as` "z = a") $
                                                OneOf ("z" === "a") ("z" === "b") (Left $ Term "z = a")
                                            )
                                            ( "z = y",
                                              because [Term "equality is transitive" `instantiatedWith` [Term "z", Term "y", Term "b", Term "z = y" `Pair` Term "y = b"]] (("z" === "b") `as` "z = b") $
                                                OneOf ("z" === "a") ("z" === "b") (Right $ Term "z = b")
                                            )
                                        ]
                                        (("z" === "a" ∨ "z" === "b") `as` "proof of z ∈ {a, b}")
                                        (Term "itrp of axiom of pair" `at` ["a", "b", "z", "proof of z ∈ {a, b}"])
                              ]
                              (forall ["z"] ((Term "z" `memberOfTerm` (Term "pair" `at` ["x", "y"])) --> (Term "z" `memberOfTerm` (Term "pair" `at` ["a", "b"]))) `as` "proof of {x, y} ⊂ {a, b}")
                              (Term "itrp of subset" `instantiatedWith` [Term "pair" `at` ["x", "y"], Term "pair" `at` ["a", "b"], Term "proof of {x, y} ⊂ {a, b}"])
                  ]
                  (forall ["x", "y", "a", "b"] (("x" === "a" ∧ "y" === "b") --> Term "pair" `at` ["x", "y"] `subsetOfTerm` (Term "pair" `at` ["a", "b"])) `as` "forward proof")
                  $ because
                    [ forany ["x", "y", "a", "b"] $
                        suppose [("x" === "a" ∧ "y" === "b") `as` "assumption"] $
                          because [Fst $ Term "assumption"] (("x" === "a") `as` "x = a") $
                            because [Snd $ Term "assumption"] (("y" === "b") `as` "y = b") $
                              because [Term "equality is symmetric" `at` ["x", "a", "x = a"]] (("a" === "x") `as` "a = x") $
                                because [Term "equality is symmetric" `at` ["y", "b", "y = b"]] (("b" === "y") `as` "b = y") $
                                  Term "forward proof" `instantiatedWith` ((Term <$> ["a", "b", "x", "y"]) ++ [Term "a = x" `Pair` Term "b = y"])
                    ]
                    (forall ["x", "y", "a", "b"] (("x" === "a" ∧ "y" === "b") --> Term "pair" `at` ["a", "b"] `subsetOfTerm` (Term "pair" `at` ["x", "y"])) `as` "backward proof")
                    $ forany ["x", "y", "a", "b"] $
                      suppose [("x" === "a" ∧ "y" === "b") `as` "assumption"] $
                        Term "two way subset implies equality"
                          `instantiatedWith` [ Term "pair" `at` ["x", "y"],
                                               Term "pair" `at` ["a", "b"],
                                               Term "forward proof" `at` ["x", "y", "a", "b", "assumption"]
                                                 `Pair` (Term "backward proof" `at` ["x", "y", "a", "b", "assumption"])
                                             ]
              )
  ]