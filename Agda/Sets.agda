{-# OPTIONS --cubical #-}
module Sets where

open import Cubical.Foundations.Prelude 
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma.Base using (_×_) 
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Functions.Logic
open import Cubical.HITs.PropositionalTruncation as PT hiding (map)
import Cubical.HITs.PropositionalTruncation.Monad as TruncMonad
open import Cubical.Foundations.Powerset as P using (ℙ; _∈_; _⊆_)
open import Cubical.Data.Sum.Base using (_⊎_)    
open import PowersetExt

private
  variable
    X Y Z : Set

{-
Defined in Cubical.Foundations.Powerset.

ℙ : Type ℓ → Type (ℓ-suc ℓ)
ℙ X = X → hProp _ 
    = X → Σ[ Y ∈ Type _] (isProp Y)
    = X → Σ[ Y ∈ Type _] ((y₀ y₁ : Y) → y₀ ≡ y₁)
-}


∪-op : {X : Set} → ℙ X → ℙ X → ℙ X
∪-op A B x = ∥ (x ∈ A) ⊎ (x ∈ B) ∥₁ , squash₁ -- (x ∈ A ⊎ x ∈ B) ≡  ⟨ A x ⟩ ⊎ ⟨ B x ⟩

infixl 6 _∪_

_∪_ : ℙ X → ℙ X → ℙ X
_∪_ = ∪-op

-- Union is commutative
∪-comm : {X : Set} (A B : ℙ X) → A ∪ B ≡ B ∪ A
∪-comm {X} A B = P.⊆-extensionality (A ∪ B) (B ∪ A) ((λ x x₁ → rec (snd ((B ∪ A) x)) (helper x A B) x₁) , λ x x₁ → rec (snd ((A ∪ B) x)) (helper x B A) x₁)
    where
        helper : (x : X) → (A B : ℙ X) → (x ∈ A) ⊎ (x ∈ B) → (B ∪ A) x .fst
        helper x A B (_⊎_.inl x₁) = ∣ _⊎_.inr x₁ ∣₁
        helper x A B (_⊎_.inr x₁) = ∣ _⊎_.inl x₁ ∣₁

-- Union is associative
∪-assoc : {X : Set} (A B C : ℙ X) → (A ∪ B) ∪ C ≡ A ∪ (B ∪ C)
∪-assoc A B C = P.⊆-extensionality (A ∪ B ∪ C) (A ∪ (B ∪ C)) ((λ x x₁ → rec (snd ((A ∪ (B ∪ C)) x)) (helper x A B C) x₁) , λ x x₁ → rec (snd ((A ∪ B ∪ C) x)) (helper3 x A B C) x₁)
    where
        helper : (x : X) → (A B C : ℙ X) → (x ∈ A ∪ B) ⊎ (x ∈ C) → (A ∪ (B ∪ C)) x .fst
        helper x A B C (_⊎_.inl x₁) = rec (snd ((A ∪ (B ∪ C)) x)) helper2 x₁
            where
                helper2 : (x ∈ A) ⊎ (x ∈ B) → (A ∪ (B ∪ C)) x .fst
                helper2 (_⊎_.inl x) = ∣ _⊎_.inl x ∣₁
                helper2 (_⊎_.inr x) = ∣ _⊎_.inr ∣ _⊎_.inl x ∣₁ ∣₁
        helper x A B C (_⊎_.inr x₁) = ∣ _⊎_.inr ∣ _⊎_.inr x₁ ∣₁ ∣₁

        helper3 : (x : X) → (A B C : ℙ X) → (x ∈ A) ⊎ (x ∈ B ∪ C) → (A ∪ B ∪ C) x .fst
        helper3 x A B C (_⊎_.inl x₁) = ∣ _⊎_.inl ∣ _⊎_.inl x₁ ∣₁ ∣₁
        helper3 x A B C (_⊎_.inr x₁) = rec (snd ((A ∪ B ∪ C) x)) helper4 x₁
            where
                helper4 : (x ∈ B) ⊎ (x ∈ C) → (A ∪ B ∪ C) x .fst
                helper4 (_⊎_.inl x) = ∣ _⊎_.inl ∣ _⊎_.inr x ∣₁ ∣₁
                helper4 (_⊎_.inr x) = ∣ _⊎_.inr x ∣₁

-- Subset properties for union
⊆-∪-left : {X : Set} (A B : ℙ X) → A ⊆ (A ∪ B)
⊆-∪-left A B x = inl

⊆-∪-right : {X : Set} (A B : ℙ X) → B ⊆ (A ∪ B)
⊆-∪-right A B x = inr



-- intersection

_∩_ : {X : Set} → ℙ X → ℙ X → ℙ X
_∩_ A B x = ((x ∈ A) × (x ∈ B)) , isProp× (P.∈-isProp A x) (P.∈-isProp B x)

-- ∈-∩ : {X : Set} →  (x : X) → (A B : ℙ X) → x ∈ (A ∩ B) ≃ (x ∈ A × x ∈ B)
-- ∈-∩ = ?

∩-comm : {X : Set} (A B : ℙ X) → A ∩ B ≡ B ∩ A
∩-comm {X} A B = P.⊆-extensionality (A ∩ B) (B ∩ A) ((λ x z → z .snd , z .fst) , (λ x z → z .snd , z .fst))

∩-assoc :  {X : Set} (A B C : ℙ X) → (A ∩ B) ∩ C ≡ A ∩ (B ∩ C)
∩-assoc {X} A B C = P.⊆-extensionality ((A ∩ B) ∩ C) (A ∩ (B ∩ C)) ((λ x z → z .fst .fst , (z .fst .snd , z .snd)) , (λ x z → (z .fst , z .snd .fst) , z .snd .snd))

∩-∪-dist : {X : Set} (A B C : ℙ X) → A ∩ (B ∪ C) ≡ (A ∩ B) ∪ (A ∩ C)
∩-∪-dist {X} A B C = P.⊆-extensionality (A ∩ (B ∪ C)) ((A ∩ B) ∪ (A ∩ C)) ((λ x x₁ → rec (snd (((A ∩ B) ∪ (A ∩ C))x)) (helper x x₁) (x₁ .snd)) , λ x x₁ → rec (snd ((A ∩ (B ∪ C))x)) (helper2 x) x₁)
    where 
        helper : (x : X) → (x ∈ (A ∩ (B ∪ C))) → (x ∈ B) ⊎ (x ∈ C) → ((A ∩ B) ∪ (A ∩ C)) x .fst
        helper x (fst₁ , snd₁) (_⊎_.inl x₁) = ∣ _⊎_.inl (fst₁ , x₁) ∣₁
        helper x (fst₁ , snd₁) (_⊎_.inr x₁) = ∣ _⊎_.inr (fst₁ , x₁) ∣₁

        helper2 : (x : X) → (x ∈ (A ∩ B)) ⊎ (x ∈ (A ∩ C)) → (A ∩ (B ∪ C)) x .fst
        helper2 x (_⊎_.inl x₁) = x₁ .fst , ∣ _⊎_.inl (x₁ .snd) ∣₁
        helper2 x (_⊎_.inr x₁) = x₁ .fst , ∣ _⊎_.inr (x₁ .snd) ∣₁

-- todo
-- ∪-∩-dist : {X : Set} → (A B C : ℙ X) → A ∪ (B ∩ C) ≡ (A ∪ B) ∩ (A ∪ C)
-- ∪-∩-dist {X} A B C = P.⊆-extensionality (A ∪ (B ∩ C)) ((A ∪ B) ∩ (A ∪ C)) {!   !}


⊆-∩-left : {X : Set} → (A B : ℙ X) → (A ∩ B) ⊆' A
⊆-∩-left {X} A B = incl (A ∩ B) A (λ x z → z .fst)

⊆-∩-right : {X : Set} → (A B : ℙ X) → (A ∩ B) ⊆' B
⊆-∩-right {X} A B = incl (A ∩ B) B (λ x z → z .snd)


-- ∪ and ⊆ 
⊆-∪-monotonic-left : {X : Set} → (A B C : ℙ X) → A ⊆' B → (A ∪ C) ⊆' (B ∪ C)
⊆-∪-monotonic-left {X} A B C (incl .A .B A⊆B) = incl (A ∪ C) (B ∪ C) (λ x₁ x₂ → rec squash₁ ((λ {(_⊎_.inl x∈A) → ∣ _⊎_.inl (A⊆B x₁ x∈A) ∣₁ ; (_⊎_.inr x∈C) → ∣ _⊎_.inr x∈C ∣₁ })) x₂)

⊆-∪-monotonic-right : {X : Set} → (A B C : ℙ X) → A ⊆' B → (C ∪ A) ⊆' (C ∪ B)
⊆-∪-monotonic-right {X} A B C (incl .A .B A⊆B) = incl (C ∪ A) (C ∪ B) (λ x₁ x₂ → rec squash₁ (λ { (_⊎_.inl x∈C) → ∣ _⊎_.inl x∈C ∣₁ ; (_⊎_.inr x∈A) → ∣ _⊎_.inr (A⊆B x₁ x∈A) ∣₁ }) x₂)