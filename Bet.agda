module Bet where

open import Axioms
open import Data.Empty
open import Data.Product
open import Data.Sum renaming ([_,_] to ⊎-elim)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation
open import Congr

bet-right : ∀ (A B : Point) → Bet A B B
bet-right A B =
 let
  construction : Σ Point (λ E → Bet A B E × Congr B E B B)
  construction = segment-construction A B B B

  E , (Bet-ABE , Congr-BEBB) = construction

  L1 : Congr B B B E
  L1 = congr-sym Congr-BEBB
    
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

two-distinct-points : Σ Point (λ A → Σ Point (λ B → ¬ A ≡ B))
two-distinct-points =
  let

    axiom = lower-dim
    A , B , C ,(not-ABC , not-BCA , not-CAB) = axiom

    A-neq-B : ¬ A ≡ B
    A-neq-B = λ hyp →
      let
        L1 : Bet B B C
        L1 = bet-left B C

        L2 : ¬ Bet B B C
        L2 = subst (λ X → ¬ Bet X B C) hyp not-ABC

        L3 : ⊥
        L3 = L2 L1
        in L3
    Goal : Σ Point (λ A → Σ Point (λ B → ¬ A ≡ B))
    Goal = A , (B , A-neq-B)
    in Goal
    

point-construction-different :
  ∀ (A B : Point) →
  Σ Point (λ C → Bet A B C × ¬ B ≡ C)
point-construction-different A B =
  let

    lemma : Σ Point (λ C → Σ Point (λ D → ¬ C ≡ D))
    lemma = two-distinct-points

    C , D , C-neq-D = lemma

    axiom : Σ Point (λ E → Bet A B E × Congr B E C D)
    axiom = segment-construction A B C D

    E ,(Bet-ABE , Congr-BECD) = axiom

    B-neq-E : ¬ B ≡ E
    B-neq-E B-eq-E =
      let
        L1 : Congr E E C D
        L1 = subst (λ X → Congr X E C D) B-eq-E Congr-BECD

        L2 : Congr C D E E
        L2 = congr-sym L1

        L3 : C ≡ D
        L3 = congr-id L2

        L4 : ⊥
        L4 = C-neq-D L3
        in L4

    Goal : Σ Point (λ C → Bet A B C × (¬ B ≡ C))
    Goal = E ,(Bet-ABE , B-neq-E)
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

14-2 : ∀ {A B C D A' B' C' D' : Point} → Bet A B C → Bet A' B' C' → Congr A C A' C' → Congr B C B' C' → Congr A D A' D'
 → Congr C D C' D' → Congr B D B' D'
14-2 {A} {B} {C} {D} {A'} {B'} {C'} {D'} H1 H2 H3 H4 H5 H6 =
  let

    case1 : A ≡ C → Congr B D B' D'
    case1 A-eq-C =
      let

        L1 : Bet C B C
        L1 = subst (λ X → Bet X B C) A-eq-C H1

        L2 : C ≡ B
        L2 = bet-id L1

        L3 : Congr B D C' D'
        L3 = subst (λ X → Congr X D C' D') L2 H6

        L4 : Congr C C A' C'
        L4 = subst (λ X → Congr X C A' C') A-eq-C H3

        L5 : Congr A' C' C C
        L5 = congr-sym L4

        L6 : A' ≡ C'
        L6 = congr-id L5

        L7 : Bet C' B' C'
        L7 = subst (λ X → Bet X B' C') L6 H2

        L8 : C' ≡ B'
        L8 = bet-id L7

        Subgoal : Congr B D B' D'
        Subgoal = subst (λ X → Congr B D X D') L8 L3
        in Subgoal

    case2 : ¬ (A ≡ C) → Congr B D B' D'
    case2 A-neq-C =
      let

        L1 : Σ Point (λ E → Bet A C E × ¬ (C ≡ E))
        L1 = point-construction-different A C

        E ,(ACE , C-neq-E) = L1

        axiom1 : Σ Point (λ E' → Bet A' C' E' × Congr C' E' C E)
        axiom1 = segment-construction A' C' C E

        E' ,(ACE' , C'E'CE) = axiom1

        L2 : Congr C E C' E'
        L2 = congr-sym C'E'CE

        axiom2 : Congr E D E' D'
        axiom2 = five-segment H3 L2 H5 H6 ACE ACE' A-neq-C

        L3 : Congr E C E' C'
        L3 = congr-reverse L2

        L4 : Congr C B C' B'
        L4 = congr-reverse H4

        L5 : Bet C B A
        L5 = bet-sym H1

        L6 : Bet B C E
        L6 = cba-bcd L5 ACE

        L7 : Bet E C B
        L7 = bet-sym L6

        L8 : Bet C' B' A'
        L8 = bet-sym H2

        L9 : Bet B' C' E'
        L9 = cba-bcd L8 ACE'

        L10 : Bet E' C' B'
        L10 = bet-sym L9

        E-neq-C : ¬ (E ≡ C)
        E-neq-C = λ E-eq-C → C-neq-E (sym E-eq-C)
        
        Subgoal : Congr B D B' D'
        Subgoal = five-segment L3 L4 axiom2 H6 L7 L10 E-neq-C
        in Subgoal
        
    Goal : Congr B D B' D'
    Goal = ⊎-elim case1 case2 (LEM (A ≡ C))
    in Goal

14-3 : ∀ {A B C A' B' C' : Point} → Bet A B C → Bet A' B' C' → Congr A C A' C' → Congr B C B' C' → Congr A B A' B'
14-3 {A} {B} {C} {A'} {B'} {C'} H1 H2 H3 H4 =
 let
 
 L1 : Congr A A A' A'
 L1 = congr-trivial-id A A'

 L2 : Congr C A C' A'
 L2 = congr-reverse H3

 L3 : Congr B A B' A'
 L3 = 14-2 H1 H2 H3 H4 L1 L2

 Goal : Congr A B A' B'
 Goal = congr-reverse L3
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

construction-uniqueness : ∀ {Q A X Y B C : Point} → Q ≢ A →  Bet Q A X → Congr A X B C → Bet Q A Y → Congr A Y B C → X ≡ Y
construction-uniqueness {Q} {A} {X} {Y} {B} {C} H1 H2 H3 H4 H5 =
 let
  L1 : Congr B C A X
  L1 = congr-sym H3

  L2 : Congr B C A Y
  L2 = congr-sym H5

  L3 : Congr A X A Y
  L3 = congr-inner-trans L1 L2

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
  L3 = congr-sym L2

  H1-rev : Bet C B A
  H1-rev = bet-sym H1

  L4 : Bet B C X
  L4 = cba-bcd H1-rev L1

  L5 : Congr C X C X
  L5 = congr-refl C X

  L6 : D ≡ X
  L6 = construction-uniqueness H3 H2 L3 L4 L5

  Goal : Bet A C D
  Goal = subst (λ Y → Bet A C Y) (sym L6) L1
  in Goal


       {- Ниже два варианта того, как можно разбирать дизъюнкцию.
              ⊎ вводится через /u+ -}

between-exchange2 : ∀ {A B C D : Point} → Bet A B D → Bet B C D → Bet A C D
between-exchange2 {A} {B} {C} {D} H1 H2 with LEM (B ≡ C)

... | inj₁ Heq =
  subst (λ X → Bet A X D) Heq H1

... | inj₂ Hneq =
  let
    L2 : Bet D B A
    L2 = bet-sym H1

    L3 : Bet C B A
    L3 = cba-bcd H2 L2

    L4 : Bet A B C
    L4 = bet-sym L3

    Goal : Bet A C D
    Goal = outer-transitivity-between2 L4 H2 Hneq
  in Goal

between-exchange2-new : ∀ {A B C D : Point} → Bet A B D → Bet B C D → Bet A C D
between-exchange2-new {A} {B} {C} {D} H1 H2 =
  let

    case1 : B ≡ C → Bet A C D
    case1 L1 = subst (λ X → Bet A X D) L1 H1

    case2 : B ≢ C → Bet A C D
    case2 L1 =
      let

        L2 : Bet D B A
        L2 = bet-sym H1

        L3 : Bet C B A
        L3 = cba-bcd H2 L2

        L4 : Bet A B C
        L4 = bet-sym L3

        Subgoal : Bet A C D
        Subgoal = outer-transitivity-between2 L4 H2 L1
        in Subgoal

    Goal : Bet A C D
    Goal = ⊎-elim case1 case2  (LEM (B ≡ C))
    in Goal

bet-outer-trans : ∀ {A B C D : Point} → Bet A B C → Bet B C D → ¬ (B ≡ C) → Bet A B D
bet-outer-trans {A} {B} {C} {D} H1 H2 H3 =
  let

    L1 : Bet A C D
    L1 = outer-transitivity-between2 H1 H2 H3

    L2 : Bet C B A
    L2 = bet-sym H1

    L3 : Bet D C B
    L3 = bet-sym H2

    L4 : Bet D C A
    L4 = bet-sym L1

    L5 : ¬ (C ≡ B)
    L5 = λ C-eq-B → H3 (sym C-eq-B)

    L6 : Bet D B A
    L6 = outer-transitivity-between2 L3 L2 L5

    Goal : Bet A B D
    Goal = bet-sym L6
    in Goal

bet-concat : ∀ {A B C D : Point} → Bet A B C → Bet A C D → Bet A B D
bet-concat {A} {B} {C} {D} H1 H2 =
  let

    L1 : Bet C B A
    L1 = bet-sym H1

    L2 : Bet B C D
    L2 = cba-bcd L1 H2

    case1 : B ≡ C → Bet A B D
    case1 L3 = subst (λ X → Bet A X D) (sym L3) H2

    case2 : ¬ (B ≡ C) → Bet A B D
    case2 L3 = bet-outer-trans H1 L2 L3

    Goal : Bet A B D
    Goal = ⊎-elim case1 case2 (LEM (B ≡ C))
    in Goal

contra-inner-trans : ∀ {A B C D : Point} → Bet A B D → ¬ Bet A B C → ¬ Bet B C D
contra-inner-trans H1 H2 = λ hyp → H2 (bet-inner-trans H1 hyp)

not-bet-not-eq : ∀ {A B C : Point} → ¬ Bet A B C → ¬ B ≡ C
not-bet-not-eq {A} {B} {C} H1 =
  λ hyp → let

      L1 : ¬ Bet A C C
      L1 = subst (λ X → ¬ Bet A X C) hyp H1

      L2 : Bet A C C
      L2 = bet-right A C

      Goal : ⊥
      Goal = L1 L2
      in Goal


