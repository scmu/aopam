{-# OPTIONS --cubical #-}
module Min where

open import Cubical.Foundations.Prelude 
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma.Base using (_×_) 
open import Cubical.Functions.Logic hiding (_⊓_; _⊔_)
open import Cubical.HITs.PropositionalTruncation as PT  hiding (map)
import Cubical.HITs.PropositionalTruncation.Monad as TruncMonad
open import Cubical.Data.Sum.Base using (_⊎_)
open import Cubical.Foundations.Powerset as P using (ℙ; _∈_; _⊆_)
open import PowersetExt

open import Data.List hiding (foldr)

open import Sets
open import Monad
open import Reasoning

private
  variable
    X Y Z : Type

record MinR {Y : Set} (R : Y → ℙ Y) : Set₁ where
  field
    -- The minR function itself
    minR : ℙ Y → ℙ Y
    
    -- The universal property
    universal-property-⇒ : {X : Set} → ∀ (P f : X → ℙ Y) →
      (P ⊑ minR ∘ f) →
      ((P ⊑ f) × ((P <=< (f °)) ⊑ R ))
    universal-property-⇐ : {X : Set} → ∀ (P f : X → ℙ Y) →
      ((P ⊑ f) × ((P <=< (f °)) ⊑ R )) → 
      (P ⊑ minR ∘ f)
    
  thm0 : {X : Set} (f : X → ℙ Y) → minR ∘ f ⊑ f
  thm0 {X} f = fst (universal-property-⇒ (minR ∘ f) f (⊑-refl (minR ∘ f)))
  
  thm1 : {X : Set} (f : X → ℙ Y) → (minR ∘ f) <=< (f °) ⊑ R
  thm1 {X}  f = snd (universal-property-⇒ (minR ∘ f) f (⊑-refl (minR ∘ f)))


foldr : (X → Y → ℙ Y) → ℙ Y → List X → ℙ Y
foldr f e [] = e
foldr f e (x ∷ xs) = f x =<< foldr f e xs

converse-swap : (R : Y → ℙ Z) → (S : X → ℙ Y) → ((R <=< S) °) ⊑ ((S °) <=< (R °)) 
converse-swap R S = λ z x x∈lhs → rec squash₁ (λ {(y , y∈Sx , z∈Ra) → ∣  y , (z∈Ra , y∈Sx) ∣₁}) x∈lhs


⊆to⊆' : {X : Set} → {A B : ℙ X} → A ⊆ B → A ⊆' B
⊆to⊆' {X} {A} {B} A⊆B = incl A B A⊆B


test2 : (f : X → Y → ℙ Y) → (e : ℙ Y) → (x : X) → (xs : List X) → (R : Y → ℙ Y) → (R-trans : R-trans R) → (mr : MinR R)  → (precond : (R <=< (f x °)) ⊑ ((f x °) <=< R)) → ((MinR.minR mr ∘ f x) <=< (MinR.minR mr ∘ foldr f e)) <=< ((f x <=< foldr f e) °) ⊑ R
test2 {X} {Y} f e x xs R R-trans mr precond y = reasoning (
  ⊆begin 
  (((MinR.minR mr ∘ f x) <=< (MinR.minR mr ∘ foldr f e)) <=< ((f x <=< foldr f e) °)) y 
  ⊆⟨ ⊆to⊆'( <=<-monotonic-right ((MinR.minR mr ∘ f x) <=< (MinR.minR mr ∘ foldr f e)) (((f x <=< foldr f e) °)) ((((foldr f e) °) <=< ((f x)°) )) (converse-swap (f x) (foldr f e)) y) ⟩
  (((MinR.minR mr ∘ f x) <=< (MinR.minR mr ∘ foldr f e)) <=< (((foldr f e) °) <=< ((f x)°) )) y
  ⊆⟨ ⊆to⊆' (pf0 y) ⟩ --  (minR · g) <=< g ° ⊆ R
  (((MinR.minR mr ∘ f x) <=< R) <=< (f x °)) y
  ⊆⟨ ⊆to⊆' (pf1 y) ⟩ --  R <=< (f x) ◦ ⊆ (f x) ◦ <=< R
  (((MinR.minR mr ∘ f x) <=< (f x °)) <=< R) y
  ⊆⟨ ⊆to⊆' ((<=<-monotonic-left R (MinR.thm1 mr (f x))) y) ⟩ -- (minR · f x) <=< (f x) ◦ <=< R
  (R <=< R) y
  ⊆⟨ ⊆to⊆' ((<=<-refl R R-trans) y) ⟩ 
  R y
  ⊆∎)
  where
    a = MinR.minR mr ∘ f x
    fx° = f x °
    g = foldr f e
    pf0 : (( a <=< (MinR.minR mr ∘ g)) <=< ((g °) <=< fx°)) ⊑ 
          (( a <=< R) <=< fx°)
    pf0 = ⊑-trans tr1 tr2
      where 
        tr1 : (( a <=< (MinR.minR mr ∘ g)) <=< ((g °) <=< fx°)) ⊑ 
              (( a <=< ((MinR.minR mr ∘ g) <=< (g °))) <=< fx°)
        tr1 = {!  !}
        tr2 : (( a <=< ((MinR.minR mr ∘ g) <=< (g °))) <=< fx°) ⊑ (( a <=< R) <=< fx°)
        tr2 = {!   !}

    pf1 : (((MinR.minR mr ∘ f x) <=< R) <=< (f x °)) ⊑ (((MinR.minR mr ∘ f x) <=< (f x °)) <=< R)
    pf1 = ⊑-trans (⊑-trans trivial trivial2) trivial3
      where
        trivial : (((MinR.minR mr ∘ f x) <=< R) <=< (f x °)) ⊑ (MinR.minR mr ∘ f x) <=< (R <=< (f x °))
        trivial = <=<-assoc-left (MinR.minR mr ∘ f x) R (f x °)
        
        trivial2 : (MinR.minR mr ∘ f x) <=< (R <=< (f x °)) ⊑ (MinR.minR mr ∘ f x) <=< ((f x °) <=< R)
        trivial2 = <=<-monotonic-right (MinR.minR mr ∘ f x) ((R <=< (f x °))) (((f x °) <=< R)) precond

        trivial3 : (MinR.minR mr ∘ f x) <=< ((f x °) <=< R) ⊑ (((MinR.minR mr ∘ f x) <=< (f x °)) <=< R)
        trivial3 = <=<-assoc-right (MinR.minR mr ∘ f x)  (f x °) R
    