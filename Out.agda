module Out where

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
open import Col


Out : Point → Point → Point → Set
Out A B C = A ≢ B × A ≢ C × (Bet A B C ⊎ Bet A C B)

bet-out : ∀ {A B C} → A ≢ B → Bet A B C → Out A B C
bet-out {A} {B} {C} A≢B Bet-ABC = witness1 , witness2 , witness3 where

 witness1 = A≢B

 witness2 = bet-id-neq1 Bet-ABC  A≢B

 witness3 = (inj₁ Bet-ABC)

bet-out-1 : ∀ {A B C} → A ≢ B -> Bet C B A -> Out A B C
bet-out-1 {A} {B} {C} A≢B Bet-CBA = bet-out A≢B (bet-sym Bet-CBA)

out-dec : ∀ {A B C} → Out A B C ⊎ (¬ Out A B C)
out-dec {A} {B} {C}= LEM (Out A B C)

out-diff1 :  ∀ {A B C} → Out A B C → A ≢ B
out-diff1 {A} {B} {C} ( A≢B , _ , _ ) =  A≢B

out-diff2 :  ∀ {A B C} → Out A B C → A ≢ C
out-diff2 {A} {B} {C} ( _ , A≢C , _ ) =  A≢C

out-distinct :  ∀ {A B C} → Out A B C -> A ≢ B × A ≢ C
out-distinct ( A≢B , A≢C , _ )  =  A≢B , A≢C

out-col : ∀ {A B C} → Out A B C → Col A B C
out-col (A≢B , A≢C , ABC⊎ACB) = ⊎-elim case1 case2 ABC⊎ACB where

 case1 = (λ ABC → inj₁ ABC)

 case2 = (λ ACB → inj₂ (inj₁ (bet-sym ACB)))
  



