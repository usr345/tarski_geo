module Bet where
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
  Goal = congr-inner-transitivity axiom axiom
  in Goal

congr-reverse : ∀ {A B C D : Point} → Congr A B C D → Congr C D A B
congr-reverse {A} {B} {C} {D} H =
 let
  L1 : Congr A B A B
  L1 = congr-refl A B
 
  Goal : Congr C D A B
  Goal = congr-inner-transitivity H L1
  in Goal
 
congr-reverse-id : ∀ {A C D : Point} → Congr A A C D → C ≡ D
congr-reverse-id {A} {C} {D} H =
 let
 
  L1 : Congr C D A A
  L1 = congr-reverse H
 
  Goal : C ≡ D
  Goal = congr-id L1
  in Goal

bet-right : ∀ (A B : Point) → Bet A B B
bet-right A B =
 let
  construction : Σ Point (λ E → Bet A B E × Congr B E B B)
  construction = segment-construction A B B B

  E , (Bet-ABE , Congr-BEBB) = construction

  L1 : Congr B B B E
  L1 = congr-reverse Congr-BEBB
    
  L2 : B ≡ E
  L2 = congr-reverse-id L1

  L3 : E ≡ B
  L3 = sym L2

  Goal : Bet A B B
  Goal = subst (λ X → Bet A B X) L3 Bet-ABE
  in Goal

bet-sym : ∀ {A B C : Point} → Bet A B C → Bet C B A
bet-sym {A} {B} {C} H =
 let
 L1 : Bet B C C
 L1 = bet-right B C
 
 construction : Σ Point (λ X → Bet B X B × Bet C X A)
 construction = inner-pasch H L1

 X , (Bet-BXB , Bet-CXA) = construction

 L2 : B ≡ X
 L2 = bet-id Bet-BXB

 L3 : X ≡ B
 L3 = sym L2

 Goal : Bet C B A
 Goal = subst (λ X → Bet C X A) L3 Bet-CXA
 in Goal

bet-left : ∀ (A B : Point) → Bet A A B
bet-left A B =
 let
 L1 : Bet B A A
 L1 = bet-right B A

 Goal : Bet A A B
 Goal = bet-sym L1
 in Goal

cba-bcd : ∀ {A B C D : Point} → Bet C B A → Bet A C D → Bet B C D
cba-bcd {A} {B}{C}{D} H1 H2 =
 let
  L1 : Bet D C A
  L1 = bet-sym H2

  construction : Σ Point (λ X → Bet B X D × Bet C X C)
  construction = inner-pasch H1 L1

  X , (Bet-BXD , Bet-CXC) = construction

  L2 : C ≡ X
  L2 = bet-id Bet-CXC

  Goal : Bet B C D
  Goal = subst (λ Y → Bet B Y D) (sym L2) Bet-BXD
  in Goal

bet-unique-middle : ∀ {A B C : Point} → Bet A B C → Bet A C B → B ≡ C
bet-unique-middle {A} {B} {C} H1 H2 =
 let
  L1 : Bet C B A
  L1 = bet-sym H1

  L2 : Bet B C A
  L2 = bet-sym H2

  construction : Σ Point (λ X → Bet B X B × Bet C X C)
  construction = inner-pasch L1 L2

  X , (Bet-BXB , Bet-CXC) = construction

  L3 : B ≡ X
  L3 = bet-id Bet-BXB

  L4 : C ≡ X
  L4 = bet-id Bet-CXC

  Goal : B ≡ C
  Goal = trans L3 (sym L4)
  in Goal

bet-inner-trans : ∀ {A B C D : Point} → Bet A B D → Bet B C D → Bet A B C
bet-inner-trans {A} {B} {C} {D} H1 H2 =
 let
  L1 : Bet D B A
  L1 = bet-sym H1

  L2 : Bet C B A
  L2 = cba-bcd H2 L1

  Goal : Bet A B C
  Goal = bet-sym L2
  in Goal

bet-exchange3 : ∀ {A B C D : Point} → Bet A B C → Bet A C D → Bet B C D
bet-exchange3 {A} {B} {C} {D} H1 H2 =
 let
  L1 : Bet D C A
  L1 = bet-sym H2

  L2 : Bet C B A
  L2 = bet-sym H1

  construction : Σ Point (λ X → Bet C X C × Bet B X D)
  construction = inner-pasch L1 L2

  X , (L3 , L4) = construction

  L5 : Bet C X C
  L5 = L3

  L6 : Bet B X D
  L6 = L4

  L7 : C ≡ X
  L7 = bet-id L5

  Goal : Bet B C D
  Goal = subst (λ Y → Bet B Y D) (sym L7) L6
  in Goal

construction-uniqueness : ∀ {Q A X Y B C : Point} → Q ≢ A →  Bet Q A X → Congr A X B C → Bet Q A Y → Congr A Y B C → X ≡ Y
construction-uniqueness {Q} {A} {X} {Y} {B} {C} H1 H2 H3 H4 H5 =
 let
  L1 : Congr B C A X
  L1 = congr-reverse H3

  L2 : Congr B C A Y
  L2 = congr-reverse H5

  L3 : Congr A X A Y
  L3 = congr-inner-transitivity L1 L2

  L4 : Congr Q A Q A
  L4 = congr-refl Q A

  L5 : Congr Q Y Q Y
  L5 = congr-refl Q Y

  L6 : Congr A Y A Y
  L6 = congr-refl A Y

  L7 : Congr X Y Y Y
  L7 = five-segment L4 L3 L5 L6 H2 H4 H1

  Goal : X ≡ Y
  Goal = congr-id L7
  in Goal

outer-transitivity-between2 : ∀ {A B C D : Point} → Bet A B C → Bet B C D → B ≢ C → Bet A C D
outer-transitivity-between2 {A} {B} {C} {D} H1 H2 H3 =
 let
  construction : Σ Point (λ X → Bet A C X × Congr C X C D)
  construction = segment-construction A C C D

  X , (L1 , L2) = construction

  L3 : Congr C D C X
  L3 = congr-reverse L2

  L4 : Bet B C X
  L4 = bet-exchange3 H1 L1

  L5 : Congr C X C X
  L5 = congr-refl C X

  L6 : D ≡ X
  L6 = construction-uniqueness H3 H2 L3 L4 L5

  Goal : Bet A C D
  Goal = subst (λ Y → Bet A C Y) (sym L6) L1
  in Goal


       {- Ниже два варианта от ИИ по разбору дизъюнкции.
              ⊎ вводится через /u+ -}

between-exchange2 : ∀ {A B C D : Point} → Bet A B D → Bet B C D → Bet A C D
between-exchange2{A} {B} {C} {D} H1 H2 with excluded-middle (B ≡ C)

... | inj₁ L1 =
  subst (λ X → Bet A X D) L1 H1

... | inj₂ L1 =
  let
    L2 : Bet D B A
    L2 = bet-sym H1

    L3 : Bet C B A
    L3 = cba-bcd H2 L2

    L4 : Bet A B C
    L4 = bet-sym L3

    Goal : Bet A C D
    Goal = outer-transitivity-between2 L4 H2 L1
  in Goal

⊎-elim :
  ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
  (A → C) →
  (B → C) →
  A ⊎ B →
  C
⊎-elim f g (inj₁ x) = f x
⊎-elim f g (inj₂ y) = g y


between-exchange2-new : ∀ {A B C D : Point} → Bet A B D →  Bet B C D →  Bet A C D
between-exchange2-new {A} {B} {C} {D} H1 H2 =
  ⊎-elim
    (λ (L1 : B ≡ C) →
      subst (λ X → Bet A X D) L1 H1)

    (λ (L1 : B ≢ C) →
      let
        L2 : Bet D B A
        L2 = bet-sym H1

        L3 : Bet C B A
        L3 = cba-bcd H2 L2

        L4 : Bet A B C
        L4 = bet-sym L3

      in outer-transitivity-between2 L4 H2 L1)

    (excluded-middle (B ≡ C))


     {- пример от ИИ доказательства теоремы, требующего несколько разборов дизъюнкции -}
distrib :  ∀ {A B C D : Set} → (A ⊎ B) → (C ⊎ D) → (A × C) ⊎ ((A × D) ⊎ ((B × C) ⊎ (B × D)))
distrib {A} {B} {C} {D} H1 H2 =
  ⊎-elim
    case-A
    case-B
    H1
  where

    case-A : A → (A × C) ⊎ ((A × D) ⊎ ((B × C) ⊎ (B × D)))
    case-A L1 =
      ⊎-elim
        case-AC
        case-AD
        H2
      where

        case-AC : C → (A × C) ⊎ ((A × D) ⊎ ((B × C) ⊎ (B × D)))
        case-AC L2 =
          inj₁ (L1 , L2)

        case-AD : D → (A × C) ⊎ ((A × D) ⊎ ((B × C) ⊎ (B × D)))
        case-AD L2 =
          inj₂ (inj₁ (L1 , L2))


    case-B : B → (A × C) ⊎ ((A × D) ⊎ ((B × C) ⊎ (B × D)))
    case-B L1 =
      ⊎-elim
        case-BC
        case-BD
        H2
      where

        case-BC : C → (A × C) ⊎ ((A × D) ⊎ ((B × C) ⊎ (B × D)))
        case-BC L2 =
          inj₂ (inj₂ (inj₁ (L1 , L2)))

        case-BD : D → (A × C) ⊎ ((A × D) ⊎ ((B × C) ⊎ (B × D)))
        case-BD L2 =
          inj₂ (inj₂ (inj₂ (L1 , L2)))
