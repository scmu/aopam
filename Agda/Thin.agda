{-# OPTIONS --cubical #-}
module Thin where

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
-- open import List
open import Sets
open import Monad
open import Table

private 
  variable
    ℓ : Level

foldrM : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} →
         (A → B → ℙ B) → ℙ B → List A → ℙ B
foldrM f e []       = e 
foldrM f e (x ∷ xs) = f x =<< foldrM f e xs

-- Approach 1: Use record to define ThinQ
record ThinQ {A : Type ℓ} (Q : A → ℙ A) : Type (ℓ-suc ℓ) where
  field
    thin : T A → ℙ (T A)
    universal-property-⇒ : (xs ys : T A) → ys ∈ thin xs → (table2set ys ⊆ table2set xs) × ((∀ x → x ∈T xs → Σ A (λ y → (y ∈T ys) × ((y ∈ Q x)))))
    universal-property-⇐ : (xs ys : T A) → (table2set ys ⊆ table2set xs) × ((∀ x → x ∈T xs → Σ A (λ y → (y ∈T ys) × ((y ∈ Q x))))) → ys ∈ thin xs

-- the proof will be moved to Fold.agda

foldrM-fixed-point-general :
  ∀ {A B : Type ℓ}
  → (g : ℙ A → ℙ A)
  → (f : B → A → ℙ A)
  → (e : ℙ A)
  → (∀ {m k} → g (k =<< m) ⊆ ((λ a → g (k a)) =<< g m)) -- g preserves bind
  → ∀ xs → g (foldrM f e xs) ⊆ foldrM (λ b a → g (f b a)) (g e) xs
foldrM-fixed-point-general = {!   !}

foldrM-fixed-point-general₂ :
  ∀ {A B C : Type ℓ}
  → (g : ℙ A → ℙ C)
  → (f : B → A → ℙ A)
  → (h : C → A)
  → (e : ℙ A)
  → (∀ {m k} → g (k =<< m) ⊆ (((λ a → g (k (h a))) =<< g m)))  -- bind-preserving (跨型別)
  → ∀ xs → foldrM (λ b c → g (f b (h c))) (g e) xs ⊆ (g ∘ foldrM f e) xs
foldrM-fixed-point-general₂ g f h e bp [] x₁ x₂ = x₂
foldrM-fixed-point-general₂ g f h e bp (x ∷ xs) x₁ x₂ = {!   !}

foldrM-fixed-point-property :
  ∀ {A B : Type ℓ}
  → (g : T A → ℙ (T A))
  → (f : B → A → ℙ A)
  → (e : ℙ A)
  → (x : B)
  → (xs : List B)
  → (finA : Finite A)
  → ((g ∘ collect {finA = finA} ∘ (f x <=< table2set)) =<< (g ∘ collect  {finA = finA}  ∘ foldrM f e) xs) ⊆ (g ∘ collect  {finA = finA}  ∘ foldrM f e) (x ∷ xs)
foldrM-fixed-point-property g f e x xs finA = {! g ∘ collect   !}



-- ((GG ∘ (f x <=< table2set)) =<< (GG ∘ foldrM f e) xs) ⊆ (GG ∘ foldrM f e) (x ∷ xs)  = GG (f x =<< foldrM f e xs)
-- GG : ℙ A → ℙ (T A)
-- 
