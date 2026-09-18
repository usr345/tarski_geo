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
open import Function.Base using (_$_)
open import BetCongr


Col : Point → Point → Point → Set
Col A B C = Bet A B C ⊎ (Bet B C A ⊎ Bet C A B)

col-from-bet1 : ∀ {A B C : Point} → Bet A B C → Col A B C
col-from-bet1 H = inj₁ H

col-from-bet2 : ∀ {A B C : Point} → Bet B C A → Col A B C
col-from-bet2 H = inj₂ (inj₁ H)

col-from-bet3 : ∀ {A B C} → Bet C A B → Col A B C
col-from-bet3 H = inj₂ (inj₂ H)

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

col-rotate3 : ∀ {A B C} → Col A B C → Col C B A
col-rotate3 {A} {B} {C} = col-elim case1 case2 case3

 where

 case1 = λ ABC → col-from-bet1 (bet-sym (ABC))

 case2 = λ BCA → col-from-bet3 (bet-sym (BCA))

 case3 = λ CAB → col-from-bet2 (bet-sym (CAB))


col-rotate4 : ∀ {A B C} → Col A B C → Col B A C
col-rotate4 {A} {B} {C} H =
  let
    proof : (Bet A B C ⊎ Bet B C A ⊎ Bet C A B) → (Bet B A C ⊎ Bet A C B ⊎ Bet C B A)
    proof = λ where

     (inj₁ ABC) → inj₂ (inj₂ (bet-sym ABC))

     (inj₂ (inj₁ ACB)) → inj₂ (inj₁ (bet-sym ACB))

     (inj₂ (inj₂ CAB)) → inj₁ (bet-sym CAB)

  in proof H

col-rotate5 : ∀ {A B C} → Col A B C → Col A C B
col-rotate5 = col-elim case1 case2 case3

 where

 case1 = λ ABC → col-from-bet2 (bet-sym (ABC))

 case2 = λ BCA → col-from-bet1 (bet-sym (BCA))

 case3 = λ CAB → col-from-bet3 (bet-sym (CAB))

col-cases : ∀ A B C → Col A B C ⊎ Col A C B ⊎ Col B A C ⊎ Col B C A ⊎ Col C A B ⊎ Col C B A → Col A B C
col-cases A B C (inj₁ Col-ABC) =
  Col-ABC

col-cases A B C (inj₂ (inj₁ Col-ACB)) =
  col-rotate5 Col-ACB

col-cases A B C (inj₂ (inj₂ (inj₁ Col-BAC))) =
  col-rotate4 Col-BAC

col-cases A B C (inj₂ (inj₂ (inj₂ (inj₁ Col-BCA)))) =
  col-rotate2 Col-BCA

col-cases A B C (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ Col-CAB))))) =
  col-rotate1 Col-CAB

col-cases A B C (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ Col-CBA))))) =
  col-rotate3 {A = C} {B = B} {C = A} Col-CBA

col-perm : ∀ {A B C} → Col A B C → Col A B C × Col A C B × Col B A C × Col B C A × Col C A B × Col C B A
col-perm {A} {B} {C} ABC = ABC , (col-rotate5 ABC) , (col-rotate4 ABC) , (col-rotate1 ABC) , (col-rotate2 ABC) , (col-rotate3 ABC)

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

col-ABA : ∀ A B → Col A B A
col-ABA A B = inj₂ $ inj₁ $ bet-right B A

L4-13 : ∀ {A B C A' B' C'} → Col A B C → Congr A B A' B' → Congr B C B' C' → Congr A C A' C' → Col A' B' C'
L4-13 {A} {B} {C} {A'} {B'} {C'} col-ABC congr-ABA'B' congr-BCB'C' congr-ACA'C' = col-elim case1 case2 case3 col-ABC where

 case1 = λ bet-ABC → col-from-bet1 $ L14-6 bet-ABC congr-ABA'B' congr-BCB'C' congr-ACA'C'

 case2 = λ bet-BCA → col-from-bet2 $ L14-6 bet-BCA congr-BCB'C' (congr-reverse congr-ACA'C') (congr-reverse congr-ABA'B')

 case3 = λ bet-CAB → col-from-bet3 $ L14-6 bet-CAB (congr-reverse congr-ACA'C') congr-ABA'B' (congr-reverse congr-BCB'C')

{- L4-14 : ∀ {A B C A' B'} → Col A B C -> Congr A B A' B' -> Σ Point (λ C' → Congr A B A' B' × Congr B C B' C' × Congr A C A' C')
L4-14 = {!!} -}
