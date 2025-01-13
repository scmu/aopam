{-# OPTIONS --cubical #-}

module Reasoning where

open import Cubical.Foundations.Powerset as P using (ℙ; _∈_; _⊆_)

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

  ⊆begin_ : ∀ {x y : ℙ X} → x ⊆ y → x ⊆ y
  ⊆begin x⊆y  =  x⊆y

  _⊆⟨_⟩_ : (x : ℙ X) {y z : ℙ X} → x ⊆ y → y ⊆ z → x ⊆ z
  x ⊆⟨ x⊆y ⟩ y⊆z  =  λ x₁ z₁ → y⊆z x₁ (x⊆y x₁ z₁)

  _⊆∎ : ∀ (x : ℙ X) → x ⊆ x
  x ⊆∎  = λ px px∈x → px∈x

open ⊆-Reasoning public using (⊆begin_; _⊆⟨_⟩_; _⊆∎)

