module SetTheory where

import Grammar
import TypeCheck
import Util

--- Definitions
set = flip TypedVar $ Type "S"

empty = Term "∅"

equals = binaryType "="

memberOf = binaryType "∈"

subsetOf = binaryType "⊂"

--- Axioms

-- ∀A:S.∀B:S.A=B -> ∀x:S.(x∈A -> x∈B)∧(x∈B -> x∈A)
equalsDef =
  forall [set "A", set "B"] $
    (Term "A" `equals` Term "B")
      `implies` forall
        [set "x"]
        ((Term "x" `memberOf` Term "A") `iff` (Term "x" `memberOf` Term "B"))

-- ∀A:S.∀B:S.∀x:S.(x∈A -> x∈B)∧(x∈B -> x∈A) -> A=B
equalsItrp =
  forall [set "A", set "B"] $
    (Term "A" `equals` Term "B")
      `isImpliedBy` forall
        [set "x"]
        ((Term "x" `memberOf` Term "A") `iff` (Term "x" `memberOf` Term "B"))

axioms =
  [ "equal def" `is` equalsDef,
    "equal itrp" `is` equalsItrp
  ]

whatDoesItProve :: Term -> Type
whatDoesItProve = typeOf axioms

--- Props

-- ∀A. A = A
equalIsReflexive = forall [set "A"] (Term "A" `equals` Term "A")

-- ∀A:S.∀x:S.(x∈A -> x∈A)∧(x∈A -> x∈A)
twoWayReflexiveProof =
  forany [set "A", set "x"] (reflexive `Pair` reflexive)
  where
    reflexive = forany ["p" `aProofOf` (Term "x" `memberOf` Term "A")] (Term "p")

equalIsReflexiveProof =
  forany
    [set "A"]
    ( Term "equal itrp"
        `instantiatedWith` [Term "A", Term "A", twoWayReflexiveProof `instantiatedWith` [Term "A"]]
    )

-- ∀A, B. A = B -> B = A
equalIsSymmetric =
  forall [set "A", set "B"] $
    (Term "A" `equals` Term "B") `implies` (Term "B" `equals` Term "A")

equalIsSymmetricProof =
  forany [set "A", set "B"] $
    since (Term "A" `equals` Term "B") "A=B" $
      Term "equal itrp"
        `instantiatedWith` [ Term "B",
                             Term "A",
                             forany [set "x"] (Snd itrpRealized `Pair` Fst itrpRealized)
                           ]
  where
    itrpRealized = Term "equal def" `instantiatedWith` [Term "A", Term "B", Term "A=B", Term "x"]

-- ∀A, B, C. A = B ∧ B = C -> A = C
equalIsTransitive =
  forall [set "A", set "B", set "C"] $
    (Term "A" `equals` Term "B") `And` (Term "B" `equals` Term "C") `implies` (Term "A" `equals` Term "C")

-- ∀A:S.∀B:S.∀C:S.(A=B)∧(B=C) -> ∀x:S.x∈A -> x∈C
equalIsTransitiveFowardProof =
  forany [set "A", set "B", set "C"] $
    suppose [Term "A" `equals` Term "B" `And` (Term "B" `equals` Term "C") `as` "A=B and B=C"] $
      forany [set "x"] $
        let p = Fst $ Term "equal def" `instantiatedWith` [Term "A", Term "B", Fst (Term "A=B and B=C"), Term "x"]
            q = Fst $ Term "equal def" `instantiatedWith` [Term "B", Term "C", Snd (Term "A=B and B=C"), Term "x"]
         in suppose [Term "x" `memberOf` Term "A" `as` "A∈B"] $ q `instantiatedWith` [p `instantiatedWith` [Term "A∈B"]]

-- ∀A:S.∀B:S.∀C:S.(A=B)∧(B=C) -> ∀x:S.x∈C -> x∈A
equalIsTransitiveBackWardProof =
  forany [set "A", set "B", set "C"] $
    suppose [Term "A" `equals` Term "B" `And` (Term "B" `equals` Term "C") `as` "A=B and B=C"] $
      let prop = Term "A=B and B=C"
          aEb = Fst prop
          bEa = equalIsSymmetricProof `instantiatedWith` [Term "A", Term "B", aEb]
          bEc = Snd prop
          cEb = equalIsSymmetricProof `instantiatedWith` [Term "B", Term "C", bEc]
          cEbANDbEa = cEb `Pair` bEa
       in equalIsTransitiveFowardProof `instantiatedWith` [Term "C", Term "B", Term "A", cEbANDbEa]

equalIsTransitiveProof =
  forany [set "A", set "B", set "C"] $
    suppose [Term "A" `equals` Term "B" `And` (Term "B" `equals` Term "C") `as` "A=B and B=C"] $
      let assumption = Term "A=B and B=C"
          aInc = equalIsTransitiveFowardProof `instantiatedWith` [Term "A", Term "B", Term "C", assumption, Term "x"]
          bInc = equalIsTransitiveBackWardProof `instantiatedWith` [Term "A", Term "B", Term "C", assumption, Term "x"]
          aEb = forany [set "x"] $ aInc `Pair` bInc
       in Term "equal itrp" `instantiatedWith` [Term "A", Term "C", aEb]