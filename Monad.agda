{-# OPTIONS --cubical #-}
module Monad where

open import Cubical.Foundations.Prelude 
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma.Base using (_×_) 
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Functions.Logic
-- open import Cubical.Data.Prod
--   hiding (map)
open import Cubical.HITs.PropositionalTruncation as PT
  hiding (map)
import Cubical.HITs.PropositionalTruncation.Monad as TruncMonad
open import Cubical.Foundations.Powerset as P using (ℙ; _∈_; _⊆_)
open import Cubical.Data.Sum.Base using (_⊎_)

variable
  X Y : Set
  
id : ∀ {l} {X : Set l} → X → X
id x = x

_∘_ : {X Y Z : Set} → (Y → Z) → (X → Y) → (X → Z)
(f ∘ g) x = f (g x)

-- functor

map : (X → Y) → ℙ X → ℙ Y
map {X} {Y} f xs y = ∥ Σ X (λ x → (x ∈ xs) × (f x ≡ y)) ∥₁ , squash₁

-- functor laws

map-id : (xs : ℙ X) → map id xs ≡ id xs
map-id xs = funExt (λ x → ⇔toPath 
             (rec (snd (xs x)) λ { (x , x∈xs , eq) → subst (λ w → fst (xs w)) eq x∈xs }) 
              λ x∈xs → ∣ x , x∈xs , refl  ∣₁
              )

map-compose : {X Y Z : Set} → (f : X → Y) → (g : Y → Z)
            → (xs : ℙ X) → map (g ∘ f) xs ≡ map g (map f xs)
map-compose f g xs = funExt λ z → ⇔toPath 
              (rec (snd (map g (map f xs) z)) 
                   λ { (x , x∈xs , eq) → ∣ f x , ∣ x , x∈xs , refl ∣₁ , eq ∣₁ }) 
              λ p → do (y , q , gy≡z) ← p
                       (x , r , fx≡y) ← q 
                       return (x , r , subst (λ w → g w ≡ z) (sym fx≡y) gy≡z)
    where open TruncMonad


-- monad

_>>=_ : {X Y : Set} → ℙ X → (X → ℙ Y) → ℙ Y
(_>>=_ {X} {Y} xs f) y =  ∥ Σ X (λ x → fst (xs x) × fst (f x y)) ∥₁ , 
                          squash₁ -- prop := (prop, f prop)

return : {X : Set} → X → ℙ X
return x x' = ∥ x ≡ x' ∥₁ , squash₁

-- monad laws 

ret-right-id : {X : Set} (m : ℙ X) 
             → (m >>= return) ≡ m
ret-right-id m = funExt λ x → ⇔toPath 
                 (rec (snd (m x)) λ { (x' , x'∈m , eq') → 
                    rec (snd (m x)) (λ eq → subst _ eq x'∈m) eq' })
                  λ x∈m → ∣ x , x∈m , ∣ refl ∣₁ ∣₁ 

ret-left-id : {X : Set} (x : X) → (f : X → ℙ Y) 
            → (return x >>= f) ≡ f x 
ret-left-id x f = funExt λ y → ⇔toPath 
  (rec (snd (f x y)) λ {(x' , x'∈ , y∈) → 
    rec (snd (f x y)) (λ eq → subst _ (sym eq) y∈)  x'∈}) 
  λ y∈ → ∣ x , ∣ refl ∣₁ , y∈ ∣₁  

>>=-assoc : {X Y Z : Set}
  → (m : ℙ X) → (f : X → ℙ Y) → (g : Y → ℙ Z)
  → (m >>= f) >>= g ≡ m >>= (λ x → f x >>= g)
>>=-assoc m f g = funExt λ z → ⇔toPath 
  (rec (snd ((m >>= (λ x → f x >>= g)) z)) 
    (λ { (y , y∈ , z∈) → rec (snd ((m >>= (λ x → f x >>= g)) z)) 
           (λ {(x , x∈ , y∈) → ∣ x , x∈ , ∣ y , y∈ , z∈ ∣₁ ∣₁}) y∈})) 
  (rec (snd (((m >>= f) >>= g) z)) 
    λ {(x , x∈ , z∈) → rec (snd (((m >>= f) >>= g) z)) 
      (λ {(y , y∈ , z∈) → ∣ y , ∣ x , x∈ , y∈ ∣₁ , z∈ ∣₁}) z∈})  
  