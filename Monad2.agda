{-# OPTIONS --prop #-}
module Monad2 where

open import Relation.Binary.PropositionalEquality
open import Data.Product hiding (map)
open import Agda.Primitive


private
    variable
        X Y Z : Set

data _≐_ {ℓ} {A : Set ℓ} (x : A) : A → Prop ℓ where
  refl : x ≐ x

_∘_ : (Y → Z) → (X → Y) → (X → Z)
(f ∘ g) x = f (g x)

id : ∀ {l} {X : Set l} → X → X
id x = x

data ∥_∥₁  {ℓ} (A : Set ℓ) : Prop ℓ where
  ∣_∣₁ : A → ∥ A ∥₁

rec : ∀ {ℓ₁ ℓ₂} (A : Set ℓ₁) (P : Prop ℓ₂) → (A → P) → ∥ A ∥₁ → P
rec A P f (∣ x ∣₁) = f x

record ↑ᵖ (P : Prop) : Set where
  constructor lift
  field
    lower : P

unlift : {P : Prop} → ↑ᵖ P → P 
unlift (lift lower) = lower


map : {X Y : Set} → (X → Y) → (X → Prop) → (Y → Prop)
map {X} {Y} f P y = ∥ (Σ X (λ x → ↑ᵖ (P x) × (f x ≡ y) )) ∥₁


postulate
    funExt : {X : Set} → {P Q : X → Prop} → ((x : X) → (P x ≡ Q x)) → P ≡ Q
    propExt : ∀ {P Q : Prop} → (P → Q) → (Q → P) → P ≡ Q

⇔toPathProp : ∀ {P Q : Prop} → (P → Q) → (Q → P) → P ≡ Q
⇔toPathProp = propExt


map-id : (xs : X → Prop) → map id xs ≡ id xs
map-id {X} xs = funExt λ x₀ → ⇔toPathProp (λ x₁ → rec (Σ X (λ x → ↑ᵖ (xs x) × id x ≡ x₀)) (xs x₀) (λ {(x , x∈xs , eq) → lem eq x∈xs }) x₁) λ x → ∣ (x₀ , (lift x , refl)) ∣₁
  where
    lem : {x₀ x : X} → {xs : X → Prop} → (eq : id x ≡ x₀) →  (x∈xs : ↑ᵖ (xs x)) → xs x₀
    lem refl x∈xs = x∈xs .↑ᵖ.lower



map-compose : {X Y Z : Set} → (f : X → Y) → (g : Y → Z)
            → (xs : X → Prop) → map (g ∘ f) xs ≡ map g (map f xs)
map-compose {X} {Y} {Z}  f g xs = funExt (λ z → ⇔toPathProp (rec (Σ X (λ x₁ → ↑ᵖ (xs x₁) × (g ∘ f) x₁ ≡ z)) (map g (map f xs) z) (λ z →
     ∣
     f (z .proj₁) ,
     lift ∣ z .proj₁ , z .proj₂ .proj₁ , refl ∣₁ , z .proj₂ .proj₂
     ∣₁)) {!   !})


_>>=_ : (X → Prop) → (X → (Y → Prop)) → (Y → Prop)
(_>>=_ {X} {Y} xs f) y =  ∥ (Σ X (λ x → ↑ᵖ (xs x) × ↑ᵖ (f x y) )) ∥₁

return : X → (X → Prop)
return x x' = ∥ x ≡ x' ∥₁


