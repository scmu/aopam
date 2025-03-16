{-# OPTIONS --cubical #-}

module Reasoning where

open import Cubical.Foundations.Powerset as P using (ℙ; _∈_; _⊆_)
open import PowersetExt
open import Cubical.Foundations.Prelude 

-- Properties of _⊆_
private
    variable
        X : Set

trans : ∀ {x y z : ℙ X} → x ⊆ y → y ⊆ z → x ⊆ z
trans = λ x₁ x₂ x₃ x₄ → x₂ x₃ (x₁ x₃ x₄)


module ⊆-Reasoning {X : Set} where
  infix  1 ⊆begin_
  infixr 2 _⊆⟨_⟩_ 
  infix  3 _⊆∎

  ⊆begin_ : ∀ {x y : ℙ X} → x ⊆' y → x ⊆' y
  ⊆begin x⊆y  =  x⊆y

  _⊆⟨_⟩_ : (x : ℙ X) {y z : ℙ X} → x ⊆' y → y ⊆' z → x ⊆' z
  x ⊆⟨ incl .x .y x⊆y ⟩ incl y z y⊆z = incl x z (λ x₁ z₁ → y⊆z x₁ (x⊆y x₁ z₁))

  _⊆∎ : ∀ (xs : ℙ X) → xs ⊆' xs
  xs ⊆∎ = incl xs xs (λ _ → λ z → z)

  reasoning : ∀ {x y : ℙ X} → x ⊆' y → x ⊆ y
  reasoning (incl _ _ p) = p 

open ⊆-Reasoning public using (⊆begin_; _⊆⟨_⟩_; _⊆∎; reasoning)


