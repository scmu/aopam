{-# OPTIONS --cubical #-}
module Monad where

open import Cubical.Foundations.Prelude 
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma.Base using (_×_) 
open import Cubical.Functions.Logic hiding (_⊓_; _⊔_)
open import Cubical.HITs.PropositionalTruncation as PT  hiding (map)
import Cubical.HITs.PropositionalTruncation.Monad as TruncMonad
open import Cubical.Foundations.Powerset as P using (ℙ; _∈_; _⊆_)

open import Sets
  
id : ∀ {l} {X : Set l} → X → X
id x = x

_∘_ : (Y → Z) → (X → Y) → (X → Z)
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

_>>=_ : ℙ X → (X → ℙ Y) → ℙ Y
(_>>=_ {X} {Y} xs f) y =  ∥ Σ X (λ x → fst (xs x) × fst (f x y)) ∥₁ , 
                          squash₁ -- prop := (prop, f prop)

return : X → ℙ X
return x x' = ∥ x ≡ x' ∥₁ , squash₁

-- monad laws 

ret-right-id : (m : ℙ X) 
             → (m >>= return) ≡ m
ret-right-id m = funExt λ x → ⇔toPath 
                 (rec (snd (m x)) λ { (x' , x'∈m , eq') → 
                    rec (snd (m x)) (λ eq → subst _ eq x'∈m) eq' })
                  λ x∈m → ∣ x , x∈m , ∣ refl ∣₁ ∣₁ 

ret-left-id : (x : X) → (f : X → ℙ Y) 
            → (return x >>= f) ≡ f x 
ret-left-id x f = funExt λ y → ⇔toPath 
  (rec (snd (f x y)) λ {(x' , x'∈ , y∈) → 
    rec (snd (f x y)) (λ eq → subst _ (sym eq) y∈)  x'∈}) 
  λ y∈ → ∣ x , ∣ refl ∣₁ , y∈ ∣₁  

>>=-assoc : (m : ℙ X) → (f : X → ℙ Y) → (g : Y → ℙ Z)
          → (m >>= f) >>= g ≡ m >>= (λ x → f x >>= g)
>>=-assoc m f g = funExt λ z → ⇔toPath 
  (rec (snd ((m >>= (λ x → f x >>= g)) z)) 
    (λ { (y , y∈ , z∈) → rec (snd ((m >>= (λ x → f x >>= g)) z)) 
           (λ {(x , x∈ , y∈) → ∣ x , x∈ , ∣ y , y∈ , z∈ ∣₁ ∣₁}) y∈})) 
  (rec (snd (((m >>= f) >>= g) z)) 
    λ {(x , x∈ , z∈) → rec (snd (((m >>= f) >>= g) z)) 
      (λ {(y , y∈ , z∈) → ∣ y , ∣ x , x∈ , y∈ ∣₁ , z∈ ∣₁}) z∈})  
  
-- other monadic operators

_=<<_ : (X → ℙ Y) → ℙ X → ℙ Y
f =<< m = m >>= f

_<=<_ : (Y → ℙ Z) → (X → ℙ Y) → (X → ℙ Z)
(f <=< g) x = f =<< g x

-- set monad

-- ⊑ and ⊒

infixr 6 _⊑_ _⊒_

_⊑_ : (X → ℙ Y) → (X → ℙ Y) → Set
r ⊑ s = ∀ x → r x ⊆ s x

⊑-trans : {r s t : X → ℙ Y} → r ⊑ s → s ⊑ t → r ⊑ t
⊑-trans = {!   !}

_⊒_ : (X → ℙ Y) → (X → ℙ Y) → Set
r ⊒ s = s ⊑ r

⊒-trans : {r s t : X → ℙ Y} → r ⊒ s → s ⊒ t → r ⊒ t
⊒-trans = {!   !}

-- ⊓ and ⊔

_⊓_ : (X → ℙ Y) → (X → ℙ Y) → (X → ℙ Y)
(r ⊓ s) x = r x ∩ s x

  -- ⊓-universal :  r ⊑ s ⊓ t  ⇔  r ⊑ s  ×  r ⊑ t

⊓-universal-⇒ : {r s t : X → ℙ Y}
              →  r ⊑ s ⊓ t  →  r ⊑ s × r ⊑ t
⊓-universal-⇒ = {!   !}

⊓-universal-⇐ : {r s t : X → ℙ Y}
              →  r ⊑ s × r ⊑ t  →  r ⊑ s ⊓ t
⊓-universal-⇐ = {!   !}

⊓-monotonic : {r s t u : X → ℙ Y}
              → r ⊑ t → s ⊑ u → r ⊓ s ⊑ t ⊓ u
⊓-monotonic = {!   !}

_⊔_ : (X → ℙ Y) → (X → ℙ Y) → (X → ℙ Y)
(r ⊔ s) x = r x ∪ s x

   -- ⊔-universal : r ⊔ s ⊑ t  ⇔  r ⊑ t  ×  s ⊑ t

⊔-universal-⇒ : {r s t : X → ℙ Y}
              → r ⊔ s ⊑ t → r ⊑ t × s ⊑ t
⊔-universal-⇒ = {!   !}

⊔-universal-⇐ : {r s t : X → ℙ Y}
              → r ⊑ t × s ⊑ t → r ⊔ s ⊑ t
⊔-universal-⇐ = {!   !}

⊔-monotonic : {r s t u : X → ℙ Y}
              → r ⊑ t → s ⊑ u → r ⊔ s ⊑ t ⊔ u
⊔-monotonic = {!   !}

  -- converse

_° : (X → ℙ Y) → (Y → ℙ X)
(r °) y x = r x y

°-idempotent : (r : X → ℙ Y) → (r °) ° ≡ r
°-idempotent r = refl

  -- factor
  
_/_ : (X → ℙ Z) → (X → ℙ Y) → (Y → ℙ Z)
(t / s) y z = ∥ (∀ x → y ∈ s x → z ∈ t x) ∥₁ , squash₁

/-universal-⇒ : (r : Y → ℙ Z) → (s : X → ℙ Y) → (t : X → ℙ Z) 
              → r <=< s ⊑ t → r ⊑ t / s
/-universal-⇒ r s t = {!   !}

/-universal-⇐ : (r : Y → ℙ Z) → (s : X → ℙ Y) → (t : X → ℙ Z) 
              → r ⊑ t / s → r <=< s ⊑ t 
/-universal-⇐ r s t = {!   !}

_↾_ : (s : X → ℙ Y) → (R : Y → ℙ Y) → X → ℙ Y
s ↾ r = s ⊓ (r / (s °))
