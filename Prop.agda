{-# OPTIONS --prop #-}
module Prop where

open import Relation.Binary.PropositionalEquality
open import Data.Product hiding (map)
open import Agda.Primitive

postulate
    funExt : {X : Set} → {P Q : X → Prop} → ((x : X) → (P x ≡ Q x)) → P ≡ Q
    propExt : ∀ {P Q : Prop} → (P → Q) → (Q → P) → P ≡ Q

⇔toPathProp : ∀ {P Q : Prop} → (P → Q) → (Q → P) → P ≡ Q
⇔toPathProp = propExt

data ∥_∥₁  {ℓ} (A : Set ℓ) : Prop ℓ where
  ∣_∣₁ : A → ∥ A ∥₁

rec : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} (P : Prop ℓ₂) → (A → P) → ∥ A ∥₁ → P
rec  P f (∣ x ∣₁) = f x

record ↑ᵖ (P : Prop) : Set where
  constructor lift
  field
    lower : P

unlift : {P : Prop} → ↑ᵖ P → P 
unlift (lift lower) = lower

infix 5 _∧_

record _∧_ (P Q : Prop) : Prop where
  constructor _,_
  field
    proj₁ : P
    proj₂ : Q

infix 5 _∨_

-- P ∨ Q is a Set, and hence can be truncated to a Prop 

data _∨_ (P Q : Prop) : Set where
  inj₁ : P → P ∨ Q
  inj₂ : Q → P ∨ Q