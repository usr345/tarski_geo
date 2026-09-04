module Axioms where

open import Data.Empty
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation

------------------------------------------------------------------------
-- Primitive geometric notions
------------------------------------------------------------------------

postulate
  Point : Set

  Bet : Point → Point → Point → Set

  Congr : Point → Point → Point → Point → Set


------------------------------------------------------------------------
-- A1. Congruence pseudo-reflexivity
------------------------------------------------------------------------

postulate
  congr-pseudo-refl :
    ∀ (A B : Point) →
      Congr A B B A


------------------------------------------------------------------------
-- A2. Congruence inner transitivity
------------------------------------------------------------------------

postulate
  congr-inner-transitivity :
    ∀ {A B C D E F : Point} →
      Congr A B C D →
      Congr A B E F →
      Congr C D E F


------------------------------------------------------------------------
-- A3. Congruence identity
------------------------------------------------------------------------

postulate
  congr-id :
    ∀ {A B C : Point} →
      Congr A B C C →
      A ≡ B


------------------------------------------------------------------------
-- A4. Segment construction
------------------------------------------------------------------------

postulate
  segment-construction :
    ∀ (A B C D : Point) →
      Σ Point (λ E →
        Bet A B E ×
        Congr B E C D)


------------------------------------------------------------------------
-- A5. Five-segment axiom
------------------------------------------------------------------------

postulate
  five-segment :
    ∀ {A A' B B' C C' D D' : Point} →
      Congr A B A' B' →
      Congr B C B' C' →
      Congr A D A' D' →
      Congr B D B' D' →
      Bet A B C →
      Bet A' B' C' →
      ¬ (A ≡ B) →
      Congr C D C' D'


------------------------------------------------------------------------
-- A6. Betweenness identity
------------------------------------------------------------------------

postulate
  bet-id :
    ∀ {A B : Point} →
      Bet A B A →
      A ≡ B


------------------------------------------------------------------------
-- A7. Inner Pasch
------------------------------------------------------------------------

postulate
  inner-pasch :
    ∀ {A B C P Q : Point} →
      Bet A P C →
      Bet B Q C →
      Σ Point (λ X →
        Bet P X B ×
        Bet Q X A)


------------------------------------------------------------------------
-- A8. Lower dimension
------------------------------------------------------------------------

postulate
  lower-dim :
    Σ Point (λ A →
      Σ Point (λ B →
        Σ Point (λ C →
          ¬ Bet A B C ×
          (¬ Bet B C A ×
           ¬ Bet C A B))))


------------------------------------------------------------------------
-- A9. Upper dimension
------------------------------------------------------------------------

postulate
  upper-dim :
    ∀ {A B C P Q : Point} →
      ¬ (P ≡ Q) →
      Congr A P A Q →
      Congr B P B Q →
      Congr C P C Q →
      Bet A B C ⊎
      (Bet B C A ⊎
       Bet C A B)


------------------------------------------------------------------------
-- A10. Euclid's axiom
------------------------------------------------------------------------

postulate
  euclid :
    ∀ {A B C D T : Point} →
      Bet A D T →
      Bet B D C →
      ¬ (A ≡ D) →
      Σ Point (λ X →
        Σ Point (λ Y →
          Bet A B X ×
          (Bet A C Y ×
           Bet X T Y)))


------------------------------------------------------------------------
-- A11. Dedekind continuity
------------------------------------------------------------------------

postulate
  continuity :
    ∀ (Xi Upsilon : Point → Set) →
      (Σ Point (λ A →
        ∀ (X Y : Point) →
          Xi X →
          Upsilon Y →
          Bet A X Y)) →
      (Σ Point (λ B →
        ∀ (X Y : Point) →
          Xi X →
          Upsilon Y →
          Bet X B Y))


------------------------------------------------------------------------
-- Law of Exluded Middle
------------------------------------------------------------------------

postulate
  excluded-middle :
    ∀ (A : Set) →
      A ⊎ ¬ A
