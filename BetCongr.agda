module BetCongr where

open import Axioms
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation
open import Function.Base using (case_of_; case_returning_of_)
open import Function.Base using (_$_)
open import Bet
open import Congr


L14-2 : ∀ {A B C D A' B' C' D'} → Bet A B C → Bet A' B' C' → Congr A C A' C' → Congr B C B' C' → Congr A D A' D' → Congr C D C' D'
 → Congr B D B' D'
L14-2 {A} {B} {C} {D} {A'} {B'} {C'} {D'} ABC ABC₁ AC-AC₁ BC-BC₁ AD-AD₁ CD-CD₁ = case LEM (A ≡ C) of λ where
 (inj₁ A≡C) → eq-case A≡C
 (inj₂ A≢C) → neq-case A≢C

  where

   eq-case : A ≡ C → Congr B D B' D'
   eq-case A≡C = case A≡C of λ where

     refl →
        let
          ABA : Bet A B A
          ABA = ABC

          C≡B : A ≡ B
          C≡B = bet-id ABA

          BD-C'D' : Congr B D C' D'
          BD-C'D' = subst (λ X → Congr X D C' D') C≡B CD-CD₁

          AA-A'C' : Congr A A A' C'
          AA-A'C' = AC-AC₁

          A'C'-AA : Congr A' C' A A
          A'C'-AA = congr-sym AA-A'C'

          A'≡C' : A' ≡ C'
          A'≡C' = congr-id  A'C'-AA

          C'B'C' : Bet C' B' C'
          C'B'C' = subst (λ X → Bet X B' C') A'≡C' ABC₁

          C'≡B' : C' ≡ B'
          C'≡B' = bet-id C'B'C'

          Goal : Congr B D B' D'
          Goal = subst (λ X → Congr B D X D') C'≡B' BD-C'D'
          in Goal

   neq-case : A ≢ C → Congr B D B' D'
   neq-case A≢C = case point-construction-different A C of λ where

      (E , ACE , C≢E) →
          case segment-construction A' C' C E of λ where

         (E' , A'C'E' , C'E'-CE) →
           let
             CE-C'E' : Congr C E C' E'
             CE-C'E' = congr-sym C'E'-CE

             ED-E'D' : Congr E D E' D'
             ED-E'D' = five-segment AC-AC₁ CE-C'E' AD-AD₁ CD-CD₁ ACE A'C'E' A≢C

             EC-E'C' : Congr E C E' C'
             EC-E'C' = congr-reverse CE-C'E'

             CB-C'B' : Congr C B C' B'
             CB-C'B' = congr-reverse BC-BC₁

             CBA : Bet C B A
             CBA = bet-sym ABC

             BCE : Bet B C E
             BCE = CBA-ACD-BCD CBA ACE

             ECB : Bet E C B
             ECB = bet-sym BCE

             CBA₁ : Bet C' B' A'
             CBA₁ = bet-sym ABC₁

             BCE₁ : Bet B' C' E'
             BCE₁ = CBA-ACD-BCD CBA₁ A'C'E'

             ECB₁ : Bet E' C' B'
             ECB₁ = bet-sym BCE₁

             E≢C : E ≢ C
             E≢C = λ E≡C → C≢E (sym E≡C)

             Goal : Congr B D B' D'
             Goal = five-segment EC-E'C' CB-C'B'  ED-E'D' CD-CD₁ ECB ECB₁ E≢C
             in Goal


L14-3 : ∀ {A B C A' B' C'} → Bet A B C → Bet A' B' C' → Congr A C A' C' → Congr B C B' C' → Congr A B A' B'

L14-3 {A} {B} {C} {A'} {B'} {C'} Bet-ABC Bet-A'B'C' Congr-ACA'C' Congr-BCB'C' =
 congr-reverse (L14-2 {A = A} {B = B} {C = C} {D = A} {A' = A'} {B' = B'} {C' = C'} {D' = A'}
 Bet-ABC Bet-A'B'C' Congr-ACA'C' Congr-BCB'C'
 (congr-trivial-id A A') (congr-reverse Congr-ACA'C'))

L14-3-1 : ∀ {A B C A' B' C'} → Bet A B C → Bet A' B' C' → Congr A B A' B' → Congr A C A' C' → Congr B C B' C'

L14-3-1 {A} {B} {C} {A'} {B'} {C'} ABC A'B'C' AB-A'B' AC-A'C' = L14-2 {A = C} {B = B} {C = A} {D = C} {A' = C'} {B' = B'} {C' = A'} {D' = C'}
 (bet-sym ABC) (bet-sym A'B'C') (congr-reverse AC-A'C')
 (congr-reverse AB-A'B') (congr-trivial-id C C') AC-A'C'

L14-5 : ∀ {A B C A' C'} → Bet A B C → Congr A C A' C' → Σ Point (λ B' → Bet A' B' C' × Congr A B A' B' × Congr B C B' C')
L14-5 {A} {B} {C} {A'} {C'} ABC AC-A'C' =
  let
    construction : Σ Point (λ X → Bet A' C' X × C' ≢ X)
    construction = point-construction-different A' C'

    X , (A'C'X , C'≢X) = construction

    B'-construction : Σ Point (λ B' → Bet X C' B' × Congr C' B' C B)
    B'-construction = segment-construction X C' C B

    B' , (XC'B' , C'B'-CB) = B'-construction

    CB-C'B' : Congr C B C' B'
    CB-C'B' = congr-sym C'B'-CB

    BC-B'C' : Congr B C B' C'
    BC-B'C' = congr-reverse CB-C'B'

    Y-construction : Σ Point (λ Y → Bet X B' Y × Congr B' Y B A)
    Y-construction = segment-construction X B' B A

    Y , (XB'Y , B'Y-BA) = Y-construction

    B'C'X : Bet B' C' X
    B'C'X = bet-sym XC'B'

    C'B'Y : Bet C' B' Y
    C'B'Y = CBA-ACD-BCD B'C'X XB'Y

    CBA : Bet C B A
    CBA = bet-sym ABC

    C'Y-CA : Congr C' Y C A
    C'Y-CA = congr-summa C'B'Y CBA C'B'-CB B'Y-BA

    YB'X : Bet Y B' X
    YB'X = bet-sym XB'Y

    YC'X : Bet Y C' X
    YC'X = ABD-BCD-ACD YB'X B'C'X

    XC'Y : Bet X C' Y
    XC'Y = bet-sym YC'X

    X≢C' : X ≢ C'
    X≢C' = λ X≡C' → C'≢X (sym X≡C')

    A'C'-AC : Congr A' C' A C
    A'C'-AC = congr-sym AC-A'C'

    C'A'-CA : Congr C' A' C A
    C'A'-CA = congr-reverse A'C'-AC

    XC'A' : Bet X C' A'
    XC'A' = bet-sym A'C'X

    Y=A' : Y ≡ A'
    Y=A' = construction-uniqueness X≢C' XC'Y C'Y-CA XC'A' C'A'-CA

    B'A'-BA : Congr B' A' B A
    B'A'-BA = subst (λ Z → Congr B' Z B A) Y=A' B'Y-BA

    A'B'-AB : Congr A' B' A B
    A'B'-AB = congr-reverse B'A'-BA

    AB-A'B' : Congr A B A' B'
    AB-A'B' = congr-sym A'B'-AB

    C'B'A' : Bet C' B' A'
    C'B'A' = subst (λ Z → Bet C' B' Z) Y=A' C'B'Y

    A'B'C' : Bet A' B' C'
    A'B'C' = bet-sym C'B'A'

    Goal : Σ Point (λ B' → Bet A' B' C' × Congr A B A' B' × Congr B C B' C')
    Goal = B' , A'B'C' , AB-A'B' , BC-B'C'
    in Goal

L14-6 : ∀ {A B C A' B' C'} → Bet A B C → Congr A B A' B' → Congr B C B' C' → Congr A C A' C' → Bet A' B' C'
L14-6 {A} {B} {C} {A'} {B'} {C'} ABC AB-A'B' BC-B'C' AC-A'C' =
 let construction : Σ Point (λ X → Bet A' X C' × Congr A B A' X × Congr B C X C')
     construction = L14-5 ABC AC-A'C'

     (X , (A'XC' , AB-A'X , BC-XC')) = construction

     A'X-AB : Congr A' X A B
     A'X-AB = congr-sym AB-A'X

     A'X-A'B' : Congr A' X A' B'
     A'X-A'B' = congr-trans A'X-AB AB-A'B'

     XC'-BC : Congr X C' B C
     XC'-BC = congr-sym BC-XC'

     XC'-B'C' : Congr X C' B' C'
     XC'-B'C' = congr-trans XC'-BC BC-B'C'

     C'X-C'B' : Congr C' X C' B'
     C'X-C'B' = congr-reverse XC'-B'C'

     A'C'-A'C' : Congr A' C' A' C'
     A'C'-A'C' = congr-refl A' C'

     XC'-XC' : Congr X C' X C'
     XC'-XC' = congr-refl X C'

     XX-XB' : Congr X X X B'
     XX-XB' = L14-2 {A = A'} {B = X} {C = C'} {D = X} {A' = A'} {B' = X} {C' = C'} {D' = B'}
      A'XC' A'XC' A'C'-A'C' XC'-XC' A'X-A'B' C'X-C'B'

     XB'-XX : Congr X B' X X
     XB'-XX = congr-sym XX-XB'

     X=B' : X ≡ B'
     X=B' = congr-id XB'-XX

     Goal : Bet A' B' C'
     Goal = subst (λ Z → Bet A' Z C') X=B' A'XC'
     in Goal

cong3-bet-eq : ∀ {A B C X} → Bet A B C → Congr A B A X → Congr B C X C → X ≡ B
cong3-bet-eq {A} {B} {C} {X }ABC AB-AX BC-XC = sym (congr-id (congr-sym
 (L14-2 {A = A} {B = B} {C = C} {D = B} {A' = A} {B' = B} {C' = C} {D' = X}
 ABC ABC (congr-refl A C) (congr-refl B C) AB-AX (congr-reverse BC-XC))))

