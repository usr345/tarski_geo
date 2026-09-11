module Congr where

open import Axioms
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation

congr-refl : ∀ (A B : Point) → Congr A B A B
congr-refl A B =
 let
 
 axiom : Congr B A A B
 axiom = congr-pseudo-refl B A
 
 Goal : Congr A B A B
 Goal = congr-inner-trans axiom axiom
 in Goal

congr-sym : ∀ {A B C D : Point} → Congr A B C D → Congr C D A B
congr-sym {A} {B} {C} {D} H =
 let
 
 L1 : Congr A B A B
 L1 = congr-refl A B
 
 Goal : Congr C D A B
 Goal = congr-inner-trans H L1
 in Goal
 
congr-reverse-id : ∀ {A C D : Point} → Congr A A C D → C ≡ D
congr-reverse-id {A} {C} {D} H =
 let
 
 L1 : Congr C D A A
 L1 = congr-sym H
 
 Goal : C ≡ D
 Goal = congr-id L1
 in Goal

congr-trans : ∀ {A B C D E F : Point} → Congr A B C D → Congr C D E F → Congr A B E F
congr-trans {A} {B} {C} {D} {E} {F} H1 H2 =
 let
 
 L1 : Congr C D A B
 L1 = congr-sym H1
  
 Goal : Congr A B E F
 Goal = congr-inner-trans L1 H2
 in Goal

congr-left-comm : ∀ {A B C D : Point} → Congr A B C D → Congr B A C D
congr-left-comm {A} {B} {C} {D} H =
 let
 
 L1 : Congr A B B A
 L1 = congr-pseudo-refl A B

 Goal : Congr B A C D
 Goal = congr-inner-trans L1 H
 in Goal

congr-right-comm : ∀ {A B C D : Point} → Congr A B C D → Congr A B D C
congr-right-comm {A} {B} {C} {D} H =
 let

 L1 : Congr C D A B
 L1 = congr-sym H

 L2 : Congr C D D C
 L2 = congr-pseudo-refl C D

 Goal : Congr A B D C
 Goal = congr-inner-trans L1 L2
 in Goal

congr-reverse : ∀ {A B C D : Point} → Congr A B C D → Congr B A D C
congr-reverse {A} {B} {C} {D} H =
 let
 
 L1 : Congr B A C D
 L1 = congr-left-comm H

 Goal : Congr B A D C
 Goal = congr-right-comm L1
 in Goal

congr-trivial-id : ∀ (A B : Point) → Congr A A B B
congr-trivial-id A B =
 let
 
 L1 : Σ Point (λ E → Bet A A E × Congr A E B B)
 L1 = segment-construction A A B B

 E ,(Bet-AAE , Congr-AEBB) = L1

 L2 : A ≡ E
 L2 = congr-id Congr-AEBB

 Goal : Congr A A B B
 Goal = subst (λ E → Congr A E B B) (sym L2) Congr-AEBB
 in Goal

congr-summa : ∀ {A B C A' B' C' : Point} → Bet A B C → Bet A' B' C' → Congr A B A' B' → Congr B C B' C' → Congr A C A' C'
congr-summa {A} {B} {C} {A'} {B'} {C'} H1 H2 H3 H4 with LEM (A ≡ B)
... | inj₁ Heq =
  let

    L1 : Congr A C B' C'
    L1 = subst (λ X → Congr X C B' C')(sym Heq) H4

    L2 : Congr B B A' B'
    L2 = subst (λ X → Congr X B A' B') Heq H3

    L3 : Congr A' B' B B
    L3 = congr-sym L2

    Heq' : A' ≡ B'
    Heq' = congr-id L3

    Goal : Congr A C A' C'
    Goal =  subst (λ X → Congr A C X C') (sym Heq') L1
    in Goal

... | inj₂ Hneq =
  let

    L1 : Congr A A A' A'
    L1 = congr-trivial-id A A'

    L2 : Congr B A B' A'
    L2 = congr-reverse H3

    L3 : Congr C A C' A'
    L3 = five-segment H3 H4 L1 L2 H1 H2 Hneq

    Goal : Congr A C A' C'
    Goal = congr-reverse L3
    in Goal


 
