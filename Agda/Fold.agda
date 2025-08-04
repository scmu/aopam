{-# OPTIONS --cubical #-}
module Fold where

open import Data.List hiding (foldr)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Foundations.Powerset as P using (ℙ; _∈_; _⊆_)
open import Cubical.Data.Sigma.Base using (_×_) 

open import Monad_v2
  
private
    variable
        ℓ : Level
        A B C : Type ℓ 

foldrM : (A → B → ℙ B) → ℙ B → List A → ℙ B
foldrM f e []       = e 
foldrM f e (x ∷ xs) = f x =<< foldrM f e xs

-- tools, [todo : move to other files]

⊆-elim :
  ∀ {ℓ : Level} {A : Type ℓ} {ys xs : ℙ A} {m : A}
  → ys ⊆ xs
  → m ∈ ys
  → m ∈ xs
⊆-elim {ℓ} {A} {ys} {xs} {m} = λ z → z m

⊆-trans :  ∀ {ℓ : Level} {A : Type ℓ} → ∀ {x y z : ℙ A} → x ⊆ y → y ⊆ z → x ⊆ z
⊆-trans = λ x₁ x₂ x₃ x₄ → x₂ x₃ (x₁ x₃ x₄)


folrM-fixed-point-properties-⇐ :
  (f : A → B → ℙ B)
  → (e : ℙ B)
  → (h : List A → ℙ B)
  → (base : e ⊆ h [])
  → (step : ∀ x xs → (f x =<< h xs) ⊆ h (x ∷ xs))
  → foldrM f e ⊑ h
folrM-fixed-point-properties-⇐ f e h base step [] b b∈fold = base b b∈fold
folrM-fixed-point-properties-⇐ f e h base step (x ∷ xs) b b∈fold = 
    let 
        -- goal b ∈ h (x ∷ xs)
        -- 1. b ∈ (f x =<< h xs)
        -- 2. step x xs b : b ∈ (f x =<< h xs) → b ∈ h (x ∷ xs)
        lem : b ∈ (f x =<< h xs)
        lem = rec squash₁ (λ {(b' , (b'∈fold , b∈fxb') ) → ∣ b' , folrM-fixed-point-properties-⇐ f e h base step xs b' b'∈fold , b∈fxb' ∣₁ }) b∈fold
    in step x xs b lem

folrM-fixed-point-properties-⇒ :
  (f : A → B → ℙ B)
  → (e : ℙ B)
  → (h : List A → ℙ B)
  → (base : h [] ⊆ e)
  → (step : ∀ x xs → h (x ∷ xs) ⊆ (f x =<< h xs))
  → h ⊑ foldrM f e
folrM-fixed-point-properties-⇒ f e h base step [] b b∈h[] = base b b∈h[]
folrM-fixed-point-properties-⇒ f e h base step (x ∷ xs) b b∈hxss = 
    let 
        lem : (f x =<< h xs) ⊆ (f x =<< foldrM f e xs) 
        lem = =<<-monotonic {m0 = h xs} {m1 = foldrM f e xs} (f x) (folrM-fixed-point-properties-⇒  f e h base step xs)
        trans = ⊆-trans {x = h (x ∷ xs)} {y = (f x =<< h xs)} {z = (f x =<< foldrM f e xs) } (step x xs) lem
    in trans b b∈hxss


postulate
    foldrM-monotonic : 
        (f₀ : A → B → ℙ B)
        → (f₁ : A → B → ℙ B)
        → (e₀ : ℙ B)
        → (e₁ : ℙ B)
        → (∀ x → f₀ x ⊑ f₁ x) 
        → e₀ ⊆ e₁
        → foldrM f₀ e₀ ⊑ foldrM f₁ e₁

    foldRM-fusion :
        (g : A → B → ℙ B)
        → (f : A → B → ℙ B)
        → (e : ℙ B)
        → (h : ℙ B → ℙ B) 
        →  ∀ x m → (g x =<< h m) ⊆ h (f x =<< m)
        →  foldrM g (h e) ⊑ h ∘ foldrM f e

-- foldRM-fusion :
--     (g : A → B → ℙ B)
--   → (f : A → B → ℙ B)
--   → (e : ℙ B)
--   → (h : ℙ B → ℙ B) 
--   →  ∀ x m → (g x =<< h m) ⊆ h (f x =<< m)
--   →  foldrM g (h e) ⊑ h ∘ foldrM f e
-- foldRM-fusion g f e h a m p [] b b∈he = b∈he
-- foldRM-fusion g f e h a m p (x ∷ xs) b q = {!  folrM-fixed-point-properties-⇒ ? ? ? ? ? ? b ? !}


-- foldrM-monotonic : 
--       (f₀ : A → B → ℙ B)
--     → (f₁ : A → B → ℙ B)
--     → (e₀ : ℙ B)
--     → (e₁ : ℙ B)
--     → (∀ x → f₀ x ⊑ f₁ x) 
--     → e₀ ⊆ e₁
--     → foldrM f₀ e₀ ⊑ foldrM f₁ e₁
-- foldrM-monotonic f₀ f₁ e₀ e₁ x x₁ x₂ x₃ x₄ = {!   !}