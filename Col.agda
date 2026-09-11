module Col where

open import Axioms
open import Data.Empty
open import Data.Product
open import Data.Sum renaming ([_,_] to ⊎-elim)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation
open import Congr
open import Bet



Col : Point → Point → Point → Set
Col A B C = Bet A B C ⊎ (Bet B C A ⊎ Bet C A B)

col-from-bet1 : ∀ {A B C : Point} → Bet A B C → Col A B C
col-from-bet1 H = inj₁ H

col-from-bet2 : ∀ {A B C : Point} → Bet B C A → Col A B C
col-from-bet2 H = inj₂ (inj₁ H)

col-from-bet3 : ∀ {A B C} → Bet C A B → Col A B C
col-from-bet3 H = inj₂ (inj₂ H)

col-swap : ∀ {A B C} → Col A B C → Col B A C
col-swap {A} {B} {C} H =
  let
    proof : (Bet A B C ⊎ Bet B C A ⊎ Bet C A B) → (Bet B A C ⊎ Bet A C B ⊎ Bet C B A)
    proof = λ where

     (inj₁ ABC) → inj₂ (inj₂ (bet-sym ABC))

     (inj₂ (inj₁ ACB)) → inj₂ (inj₁ (bet-sym ACB))

     (inj₂ (inj₂ CAB)) → inj₁ (bet-sym CAB)

  in proof H
 

col-rotate1 : ∀ {A B C} → Col A B C → Col B C A
col-rotate1 {A} {B} {C} H =
 let
  proof : (Bet A B C ⊎ Bet B C A ⊎ Bet C A B) → (Bet B C A ⊎ Bet C A B ⊎ Bet A B C)
  proof = λ where

   (inj₁ ABC) → inj₂ (inj₂ ABC)

   (inj₂ (inj₁ BCA)) → inj₁ BCA

   (inj₂ (inj₂ CAB)) → inj₂ (inj₁ CAB)

 in proof H

col-rotate2 : ∀ {A B C} → Col A B C → Col C A B
col-rotate2 {A} {B} {C} H =
 let
  proof : (Bet A B C ⊎ Bet B C A ⊎ Bet C A B) → (Bet C A B ⊎ Bet A B C ⊎ Bet B C A)
  proof = λ where

   (inj₁ ABC) → inj₂ (inj₁ ABC)

   (inj₂ (inj₁ BCA)) → inj₂ (inj₂ BCA)

   (inj₂ (inj₂ CAB)) → inj₁ CAB

 in proof H

col-left : ∀ {A B : Point} → Col A A B
col-left {A} {B} =
 let

  L1 : Bet A A B
  L1 = bet-left A B

  Goal : Col A A B
  Goal = inj₁ L1
  in Goal

col-right : ∀ {A B : Point} → Col A B B
col-right {A} {B} =
 let

 L1 : Bet A B B
 L1 = bet-right A B

 Goal : Col A B B
 Goal = inj₁ L1
 in Goal


col-elim : ∀ {A B C : Point} {P : Set} → (Bet A B C → P) → (Bet B C A → P) → (Bet C A B → P) → Col A B C → P
col-elim {A} {B} {C} {P} f1 f2 f3 H =
  let

    proof : Col A B C → P
    proof = λ where

      (inj₁ L1) →
        f1 L1

      (inj₂ (inj₁ L1)) →
        f2 L1

      (inj₂ (inj₂ L1)) →
        f3 L1

  in proof H

 {- Потом можно будет писать col-elim (λ ABC → ...) (λ BCA → ...) (λ CAB → ...) H -}

NonCol : Point → Point → Point → Set
NonCol A B C = ¬ Col A B C


