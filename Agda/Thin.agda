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
open import List
open import Sets
open import Monad
open import Table

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
