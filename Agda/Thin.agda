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
open import Reasoning


-- TODO: universe polymorphism in Monda.agda
-- redefine some operations with level:
_>>='_ : ∀ {ℓ} {X : Type ℓ} {Y : Type ℓ} → ℙ X → (X → ℙ Y) → ℙ Y
(_>>='_ {X = X} {Y = Y} xs f) y = ∥ Σ X (λ x → fst (xs x) × fst (f x y)) ∥₁ , squash₁ -- ∥ Σ X (λ x → fst (xs x) × fst (f x y)) ∥₁ , squash₁

_=<<'_ : ∀ {ℓ} {X : Type ℓ} {Y : Type ℓ} → (X → ℙ Y) → ℙ X → ℙ Y 
f =<<' m = m >>=' f

_<=<'_ : ∀ {ℓ} {X : Type ℓ} {Y : Type ℓ} {Z : Type ℓ} →  (Y → ℙ Z) → (X → ℙ Y) → (X → ℙ Z)
(f <=<' g) x = f =<<' g x

_⊑'_ : ∀ {ℓ} {X : Type ℓ} {Y : Type ℓ} → (X → ℙ Y) → (X → ℙ Y) → Type ℓ
r ⊑' s = ∀ x → r x ⊆ s x

foldrM : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} →
         (A → B → ℙ B) → ℙ B → List A → ℙ B
foldrM f e []       = e 
foldrM f e (x ∷ xs) = f x =<<' foldrM f e xs


-- Approach 1: Use record to define ThinQ
record ThinQ {A : Type ℓ} (Q : A → ℙ A) : Type (ℓ-suc (ℓ-suc ℓ)) where
  field
    thin : ℙ A → ℙ (ℙ A)

    -- universal property in AOP:
    -- ys, xs : P A  ,  Q : A → A  ,  thin: P A → P A
    -- ys ∈ thin xs  ≡  ys ⊆ xs ∧ (∀ x ∈ xs : (∃ y ∈ ys : y Q x))

    -- non-deterministic setting
    -- Q is a relation, A → P A
    -- given a set xs : P A, thinQ will non-deterministically return all possible outcomes, which is a set of sets P (P A)

    universal-property-⇒ : (xs ys : ℙ A) → (ys ∈ thin xs) → (ys ⊆ xs) × (∀ x → x ∈ xs → Σ A (λ y → (y ∈ ys) × (y ∈ Q x)))
    universal-property-⇐ : (xs ys : ℙ A) → (ys ⊆ xs) × (∀ x → x ∈ xs → Σ A (λ y → (y ∈ ys) × (y ∈ Q x))) → (ys ∈ thin xs)
     
  thinning-theorem : ∀ {B : Type ℓ} (f : B → A → ℙ A) (e : ℙ A) (xs : List B) → (foldrM (λ x → thin ∘ {! \m -> (m >>= f x) !}) (thin e)) xs ⊆ (thin (foldrM f e xs))
  thinning-theorem = {!   !}

-- Approach 2:
thinQQ : {A : Type ℓ} → (Q : A → ℙ A) → ℙ A → ℙ (ℙ A)
thinQQ {ℓ} {A} Q xs = λ ys → ∥ (ys ⊆ xs) × (∀ x → x ∈ xs →  (Σ[ y ∈ A ] (y ∈ ys) × {! y ∈ Q x   !})) ∥₁ , squash₁
-- level issue