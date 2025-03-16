{-# OPTIONS --cubical #-}

module PowersetExt where

open import Cubical.Foundations.Powerset


data _⊆'_ {X : Set} : ℙ X → ℙ X → Set₁ where 
   incl : (A B : ℙ X) → A ⊆ B → A ⊆' B

⊆'-refl-explicit : {X : Set} → (A : ℙ X) → A ⊆' A
⊆'-refl-explicit A = incl A A (λ x z → z)

⊆'-refl : {X : Set} {A : ℙ X} → A ⊆' A
⊆'-refl {X} {A} = incl A A (λ x z → z)
