-- For set S : P A
-- there is a mapping `collect` : P A → T A
-- and a ∈T is ∈ in the type T
-- and it satisfies   a ∈ S ⇔ a ∈T (collect S)
-- maybe we also need a `g` that map T A → P A

{-# OPTIONS --cubical #-}

module Table where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.List.Base
open import Cubical.Data.Bool.Base
open import Cubical.Foundations.Powerset as P using (ℙ; _∈_; _⊆_)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.Sigma.Base using (_×_) 
open import Cubical.Relation.Nullary

private 
  variable
    ℓ : Level

T : ∀ {ℓ} → Type ℓ → Type ℓ
T A = List A


-- operators

data _∈T_ {ℓ} {A : Type ℓ} (a : A) : T A → Type ℓ where
  here  : ∀ {xs}   → a ∈T (a ∷ xs)
  there : ∀ {x xs} → a ∈T xs → a ∈T (x ∷ xs)




record Finite (A : Type ℓ) : Type ℓ where
  field
    enum : List A
    complete : ∀ a → a ∈T enum  -- every a is in the enumeration

hProp2Bool : ∀ {ℓ} {A : Type ℓ} → hProp ℓ → Bool
hProp2Bool _ = true

filter : ∀ {ℓ} {A : Type ℓ} → (A → Bool) → List A → List A
filter p []       = []
filter p (x ∷ xs) = if p x then x ∷ filter p xs else filter p xs

collect : ∀ {ℓ} {A : Type ℓ} → {finA : Finite A} →  ℙ A → T A
collect {ℓ} {A} {finA} pa = filter (λ a → hProp2Bool {A = A} (pa a)) (Finite.enum finA)

-- table T A → set ℙ A
table2set : ∀ {ℓ} {A : Type ℓ} → T A → ℙ A
table2set xs = λ a → ∥ (a ∈T xs) ∥₁ , squash₁