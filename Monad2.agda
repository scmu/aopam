{-# OPTIONS --prop #-}
module Monad2 where

open import Relation.Binary.PropositionalEquality
open import Data.Product hiding (map)
open import Agda.Primitive hiding (_⊔_)
open import Prop
open import Data.Sum.Base hiding (map)
open import Data.Sum.Base using (_⊎_)    

private
    variable
        X Y Z : Set

_∘_ : (Y → Z) → (X → Y) → (X → Z)
(f ∘ g) x = f (g x)

id : ∀ {l} {X : Set l} → X → X
id x = x

data _≐_ {ℓ} {A : Set ℓ} (x : A) : A → Prop ℓ where
  refl : x ≐ x


map : {X Y : Set} → (X → Y) → (X → Prop) → (Y → Prop)
map {X} {Y} f P y = ∥ (Σ X (λ x → ↑ᵖ (P x) × (f x ≡ y) )) ∥₁

map-id : (xs : X → Prop) → map id xs ≡ id xs
map-id {X} xs = funExt λ x₀ → ⇔toPathProp (λ x₁ → rec  (xs x₀) (λ {(x , x∈xs , eq) → lem eq x∈xs }) x₁) λ x → ∣ (x₀ , (lift x , refl)) ∣₁
  where
    lem : {x₀ x : X} → {xs : X → Prop} → (eq : id x ≡ x₀) →  (x∈xs : ↑ᵖ (xs x)) → xs x₀
    lem refl x∈xs = x∈xs .↑ᵖ.lower



map-compose : {X Y Z : Set} → (f : X → Y) → (g : Y → Z)
            → (xs : X → Prop) → map (g ∘ f) xs ≡ map g (map f xs)
map-compose {X} {Y} {Z}  f g xs = funExt (λ z → ⇔toPathProp (rec (map g (map f xs) z) (λ z →
     ∣
     f (z .proj₁) ,
     lift ∣ z .proj₁ , z .proj₂ .proj₁ , refl ∣₁ , z .proj₂ .proj₂
     ∣₁)) {!   !})


_>>=_ : (X → Prop) → (X → (Y → Prop)) → (Y → Prop)
(_>>=_ {X} {Y} xs f) y =  ∥ (Σ X (λ x → ↑ᵖ (xs x) × ↑ᵖ (f x y) )) ∥₁

return : X → (X → Prop)
return x x' = ∥ x ≡ x' ∥₁

ret-right-id : (m : X → Prop) 
             → (m >>= return) ≡ m
ret-right-id {X} m = funExt (λ x → ⇔toPathProp 
                                      (rec (m x) (λ {(x' , x'∈m , eq) 
                                      → rec  (m x) (λ eq' → unlift (subst (λ w → ↑ᵖ (m w)) eq' x'∈m)) (unlift eq) })) 
                                      λ mx → ∣ (x , ((lift mx) , (lift ∣ refl ∣₁))) ∣₁)

ret-left-id : (x : X) → (f : X → (Y → Prop)) 
            → (return x >>= f) ≡ f x 
ret-left-id {X} x f = funExt λ y → ⇔toPathProp 
                                (rec (f x y) (λ {(x' , x'∈ , y∈) 
                                  → rec  (f x y) (λ eq → unlift (subst (λ w →  ↑ᵖ (f w y)) (sym eq) y∈)) (unlift x'∈) } )) 
                                λ x∈Py → ∣ (x , ((lift ∣ refl ∣₁) , (lift x∈Py))) ∣₁

>>=-assoc : (m : X → Prop) → (f : X → (Y → Prop)) → (g : Y → (Z → Prop))
          → (m >>= f) >>= g ≡ m >>= (λ x → f x >>= g)
>>=-assoc {X} {Y} m f g = funExt λ z → ⇔toPathProp 
                                        (rec ((m >>= (λ x → f x >>= g)) z) (λ {(y , y∈ , z∈) → rec ((m >>= (λ x → f x >>= g)) z) (λ z₁ →
                                             ∣
                                             z₁ .proj₁ , z₁ .proj₂ .proj₁ , lift ∣ y , z₁ .proj₂ .proj₂ , z∈ ∣₁
                                             ∣₁) (unlift y∈)}) )
                                        (rec (((m >>= f) >>= g) z) λ {(x , x∈ , z∈) → rec (((m >>= f) >>= g) z) (λ z₁ →
                                             ∣
                                             z₁ .proj₁ , lift ∣ x , x∈ , z₁ .proj₂ .proj₁ ∣₁ , z₁ .proj₂ .proj₂
                                             ∣₁) (unlift z∈) })

-- other monadic operators

_=<<_ : (X → (Y → Prop)) → (X → Prop) → (Y → Prop)
f =<< m = m >>= f

_<=<_ : (Y → (Z → Prop)) → (X → (Y → Prop)) → (X → (Z → Prop))
(f <=< g) x = f =<< g x

_<$>_ : (X → Y) → (X → Prop) → (Y → Prop)
f <$> m  = m >>= λ x → return (f x)      -- _<$>_ = map

-- set monad

_∈_ : {X : Set} → X → (X → Prop) → Prop
x ∈ A = A x

_⊆_ : {X : Set} → (X → Prop) → (X → Prop) → Prop
A ⊆ B = ∀ x → x ∈ A → x ∈ B

-- monotonicity

<$>-monotonic : ∀ {m0 m1 : X → Prop} → (f : X → Y) → m0 ⊆ m1 → (f <$> m0) ⊆ (f <$> m1)
<$>-monotonic {X} {Y} {m0} {m1} f m0⊆m1 y y∈f<$>m0 = rec (y ∈ (f <$> m1)) (λ {(x , ↑ᵖm0x , eq) → ∣ (x , lift (m0⊆m1 x (unlift ↑ᵖm0x)) , eq) ∣₁ }) y∈f<$>m0

>>=-monotonic : ∀ {m0 m1 : X → Prop} → (f : X → (Y → Prop)) → m0 ⊆ m1 → (m0 >>= f) ⊆ (m1 >>= f)
>>=-monotonic {X} {Y} {m0} {m1} f m0⊆m1 y x∈m0>>=f = rec _ ((λ {(x , ↑ᵖm0x , eq) → ∣ x , lift (m0⊆m1 x (unlift ↑ᵖm0x)) , eq ∣₁})) x∈m0>>=f
-- ⊑ and ⊒

infixr 6 _⊑_ _⊒_

_⊑_ : (X → (Y → Prop)) → (X → (Y → Prop)) → Prop
r ⊑ s = ∀ x → r x ⊆ s x

⊑-trans : {r s t : X → (Y → Prop)} → r ⊑ s → s ⊑ t → r ⊑ t
⊑-trans = λ r⊑s s⊑t x y y∈rx → s⊑t x y (r⊑s x y y∈rx)

_⊒_ : (X → (Y → Prop)) → (X → (Y → Prop)) → Prop
r ⊒ s = s ⊑ r

⊒-trans : {r s t : X → (Y → Prop)} → r ⊒ s → s ⊒ t → r ⊒ t
⊒-trans = λ r⊒s s⊒t x y y∈tx → r⊒s x y (s⊒t x y y∈tx)

-- -- ⊓ and ⊔

_∩_ : {X : Set} → (X → Prop) → (X → Prop) → (X → Prop)
_∩_ A B x = (x ∈ A) ∧ (x ∈ B)

_⊓_ : (X → (Y → Prop)) → (X → (Y → Prop)) → (X → (Y → Prop))
(r ⊓ s) x = r x ∩ s x
 
--   -- ⊓-universal :  r ⊑ s ⊓ t  ⇔  r ⊑ s  ×  r ⊑ t

⊓-universal-⇒ : {r s t : X → (Y → Prop) }
              →  r ⊑ s ⊓ t  →  (r ⊑ s) ∧ (r ⊑ t)
⊓-universal-⇒ r⊑s⊓t = (λ x y y∈rx → r⊑s⊓t x y y∈rx ._∧_.proj₁) , (λ x y y∈rx → r⊑s⊓t x y y∈rx ._∧_.proj₂)

⊓-universal-⇐ : {r s t : X → (Y → Prop) }
              →  (r ⊑ s) ∧ (r ⊑ t)  →  r ⊑ s ⊓ t
⊓-universal-⇐ r⊑s×r⊑t x y y∈rx = r⊑s×r⊑t ._∧_.proj₁ x y y∈rx , r⊑s×r⊑t ._∧_.proj₂ x y y∈rx

⊓-monotonic : {r s t u : X → (Y → Prop) }
              → r ⊑ t → s ⊑ u → r ⊓ s ⊑ t ⊓ u
⊓-monotonic = λ r⊑t s⊑u x y y∈r⊓s'x → r⊑t x y (y∈r⊓s'x ._∧_.proj₁) , s⊑u x y (y∈r⊓s'x ._∧_.proj₂)

_∪_ : {X : Set} → (X → Prop) → (X → Prop) → (X → Prop)
_∪_ A B x = ∥ (x ∈ A) ∨ (x ∈ B) ∥₁ 

_⊔_ : (X → (Y → Prop) ) → (X → (Y → Prop)) → (X → (Y → Prop))
(r ⊔ s) x = r x ∪ s x

⊔-universal-⇒ : {r s t : X → (Y → Prop)}
              → r ⊔ s ⊑ t → (r ⊑ t) ∧ (s ⊑ t)
⊔-universal-⇒ r⊔s⊑t = (λ x x₁ z → r⊔s⊑t x x₁ ∣ inj₁ z ∣₁) ,
  (λ x x₁ z → r⊔s⊑t x x₁ ∣ inj₂ z ∣₁)

⊔-universal-⇐ : {r s t : X → (Y → Prop)}
              → (r ⊑ t) ∧ (s ⊑ t) → r ⊔ s ⊑ t
⊔-universal-⇐ (r⊑t , s⊑t) = λ x y y∈r⊔s'x → rec _ (λ { (_∨_.inj₁ y∈rx) → r⊑t x y y∈rx ; (_∨_.inj₂ y∈sx) → s⊑t x y y∈sx }) y∈r⊔s'x

⊔-monotonic : {r s t u : X → (Y → Prop)}
              → r ⊑ t → s ⊑ u → r ⊔ s ⊑ t ⊔ u
⊔-monotonic r⊑t s⊑u x y y∈r⊔s'x = rec _ ((λ { (_∨_.inj₁ y∈rx) → ∣ inj₁ (r⊑t x y y∈rx) ∣₁ ; (_∨_.inj₂ y∈sx) → ∣ inj₂ (s⊑u x y y∈sx) ∣₁ })) y∈r⊔s'x
  