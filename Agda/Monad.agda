{-# OPTIONS --cubical #-}
module Monad where

open import Cubical.Foundations.Prelude 
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma.Base using (_×_) 
open import Cubical.Functions.Logic hiding (_⊓_; _⊔_)
open import Cubical.HITs.PropositionalTruncation as PT  hiding (map)
import Cubical.HITs.PropositionalTruncation.Monad as TruncMonad
open import Cubical.Data.Sum.Base using (_⊎_)
open import Cubical.Foundations.Powerset as P using (ℙ; _∈_; _⊆_)
open import Sets
open import PowersetExt


variable
  X Y Z : Set
  ℓ ℓ₁ ℓ₂ ℓ₃ : Level

id : ∀ {l} {X : Set l} → X → X
id x = x

-- _∘_ : (Y → Z) → (X → Y) → (X → Z)
-- (f ∘ g) x = f (g x)

_∘_ : {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
     → (B → C) → (A → B) → (A → C)
g ∘ f = λ x → g (f x)

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

-- set monad

-- ⊑ and ⊒

infixr 6 _⊑_ _⊒_

_⊑_ : (X → ℙ Y) → (X → ℙ Y) → Set
r ⊑ s = ∀ x → r x ⊆ s x

⊑-refl : {A B : Set} → (r : A → ℙ B) → r ⊑ r
⊑-refl = λ r x x₁ z → z

⊑-trans : {r s t : X → ℙ Y} → r ⊑ s → s ⊑ t → r ⊑ t
⊑-trans = λ r⊑s s⊑t x y y∈rx → s⊑t x y (r⊑s x y y∈rx)

_⊒_ : (X → ℙ Y) → (X → ℙ Y) → Set
r ⊒ s = s ⊑ r

⊒-trans : {r s t : X → ℙ Y} → r ⊒ s → s ⊒ t → r ⊒ t
⊒-trans = λ r⊒s s⊒t x y y∈tx → r⊒s x y (s⊒t x y y∈tx)
-- ⊓ and ⊔

_⊓_ : (X → ℙ Y) → (X → ℙ Y) → (X → ℙ Y)
(r ⊓ s) x = r x ∩ s x

  -- ⊓-universal :  r ⊑ s ⊓ t  ⇔  r ⊑ s  ×  r ⊑ t

⊓-universal-⇒ : {r s t : X → ℙ Y}
              →  r ⊑ s ⊓ t  →  r ⊑ s × r ⊑ t
⊓-universal-⇒ = λ r⊑s⊓t → (λ x y y∈rx → fst (r⊑s⊓t x y y∈rx)) , λ x y y∈rx → snd (r⊑s⊓t x y y∈rx)

⊓-universal-⇐ : {r s t : X → ℙ Y}
              →  r ⊑ s × r ⊑ t  →  r ⊑ s ⊓ t
⊓-universal-⇐ = λ r⊑s×r⊑t x y y∈rx → (fst r⊑s×r⊑t x y y∈rx) , (snd r⊑s×r⊑t x y y∈rx)

⊓-monotonic : {r s t u : X → ℙ Y}
              → r ⊑ t → s ⊑ u → r ⊓ s ⊑ t ⊓ u
⊓-monotonic = λ r⊑t s⊑u x y y∈r⊓s'x → r⊑t x y (fst (y∈r⊓s'x)) , s⊑u x y (snd (y∈r⊓s'x))

_⊔_ : (X → ℙ Y) → (X → ℙ Y) → (X → ℙ Y)
(r ⊔ s) x = r x ∪ s x

   -- ⊔-universal : r ⊔ s ⊑ t  ⇔  r ⊑ t  ×  s ⊑ t

⊔-universal-⇒ : {r s t : X → ℙ Y}
              → r ⊔ s ⊑ t → r ⊑ t × s ⊑ t
⊔-universal-⇒ = λ r⊔s⊑t → (λ x y y∈rx → r⊔s⊑t x y ∣ _⊎_.inl y∈rx ∣₁) , λ x y y∈sx → r⊔s⊑t x y ∣ _⊎_.inr y∈sx ∣₁

⊔-universal-⇐ : {r s t : X → ℙ Y}
              → r ⊑ t × s ⊑ t → r ⊔ s ⊑ t
⊔-universal-⇐ {X} {Y} {r} {s} {t} r⊑t×s⊑t x y c∈r⊔s'b = rec (snd(t x y)) (λ {(_⊎_.inl y∈rx) → fst r⊑t×s⊑t x y y∈rx ; (_⊎_.inr y∈sx) → snd r⊑t×s⊑t x y y∈sx}) c∈r⊔s'b 

⊔-monotonic : {r s t u : X → ℙ Y}
              → r ⊑ t → s ⊑ u → r ⊔ s ⊑ t ⊔ u
⊔-monotonic = λ r⊑t s⊑u x y y∈r⊔s'x → rec squash₁ (λ {(_⊎_.inl y∈rx) → ∣ _⊎_.inl (r⊑t x y y∈rx) ∣₁ ; (_⊎_.inr y∈sx) → ∣ _⊎_.inr (s⊑u x y y∈sx) ∣₁ }) y∈r⊔s'x 
  
-- other monadic operators

_=<<_ : (X → ℙ Y) → ℙ X → ℙ Y
f =<< m = m >>= f

_<=<_ : (Y → ℙ Z) → (X → ℙ Y) → (X → ℙ Z)
(f <=< g) x = f =<< g x

_<$>_ : (X → Y) → ℙ X → ℙ Y
f <$> m  = m >>= λ x → return (f x)      -- _<$>_ = map

-- monotonicity

<$>-monotonic : ∀ {m0 m1 : ℙ X} → (f : X → Y) → m0 ⊆' m1 → (f <$> m0) ⊆' (f <$> m1)
<$>-monotonic {x0} {x1} {m0} {m1} f (incl .m0 .m1 m0⊆m1) = incl (f <$> m0) (f <$> m1) λ x₁ x₂ → rec squash₁ (λ ( x0 , a∈m0 , eq)  → ∣ x0 , m0⊆m1 x0 a∈m0 , eq ∣₁ ) x₂

>>=-monotonic : ∀ {m0 m1 : ℙ X} → (f : X → ℙ Y) → m0 ⊆' m1 → (m0 >>= f) ⊆' (m1 >>= f)
>>=-monotonic {x0} {x1} {m0} {m1} f (incl .m0 .m1 m0⊆m1) = incl (m0 >>= f) (m1 >>= f) λ x₁ x₂ → rec squash₁ (λ (x0 , x0∈m0 , x₁∈fx0) → ∣ x0 , m0⊆m1 x0 x0∈m0 , x₁∈fx0 ∣₁) x₂

<=<-monotonic-left : ∀ {m0 m1 : Y → ℙ Z} → (f : X → ℙ Y) → m0 ⊑ m1 → (m0 <=< f) ⊑ (m1 <=< f)
<=<-monotonic-left {Y} {Z} {X} {m0} {m1} f m0⊑m1 x z z∈m0<=<fx = rec squash₁ (λ {(y , y∈fx , z∈m0y) → ∣ y , y∈fx , m0⊑m1 y z z∈m0y ∣₁ }) z∈m0<=<fx

<=<-monotonic-right : ∀ (m : Y → ℙ Z) → (f g : X → ℙ Y) → f ⊑ g → (m <=< f) ⊑ (m <=< g)
<=<-monotonic-right {Y} {Z} {X} m f g f⊑g x z z∈m<=<fx = rec squash₁ (λ {(y , y∈fx , z∈my) → ∣ y , f⊑g x y y∈fx , z∈my ∣₁}) z∈m<=<fx

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
/-universal-⇒ r s t = λ r<=<s⊑t y z z∈ry → ∣ (λ x y∈sx → r<=<s⊑t x z ∣ (y , y∈sx , z∈ry) ∣₁) ∣₁

/-universal-⇐ : (r : Y → ℙ Z) → (s : X → ℙ Y) → (t : X → ℙ Z) 
              → r ⊑ t / s → r <=< s ⊑ t 
/-universal-⇐ r s t = λ  r⊑t/s x z z∈r<=<s'x → rec (t x z .snd) (λ {(y , y∈sx , z∈ry) → rec (t x z .snd) (λ f → f x y∈sx) (r⊑t/s y z z∈ry) }) z∈r<=<s'x


-- <=< properties
R-trans : (R : X → ℙ X) → Type _
R-trans R = ∀ x y z → y ∈ R x → z ∈ R y → z ∈ R x

<=<-refl :  (R : X → ℙ X) → (R-trans R) → (R <=< R) ⊑ R
<=<-refl R R-trans x x₁ x₁∈lhs = rec (P.∈-isProp (R x) x₁) (λ { (y , y∈Rx , z∈Ry) → R-trans x y x₁ y∈Rx z∈Ry}) x₁∈lhs

<=<-assoc-left : (R S T : X → ℙ X) → (R <=< S) <=< T ⊑ R <=< (S <=< T)
<=<-assoc-left R S T x x' x'∈lhs = rec squash₁ (λ {(y ,  y∈Tx , x'∈R<=<Sy) → rec squash₁ (λ {(z , z∈Sy , x'∈Rz) → ∣ z , ∣ y , y∈Tx , z∈Sy ∣₁ , x'∈Rz  ∣₁ }) x'∈R<=<Sy }) x'∈lhs

<=<-assoc-right : (R S T : X → ℙ X) → R <=< (S <=< T) ⊑ (R <=< S) <=< T
<=<-assoc-right R S T x x' x'∈lhs = rec squash₁ (λ {(z , z∈S<=<Tx , x'∈Rz) → rec squash₁ (λ z₁ →
     ∣ z₁ .fst , z₁ .snd .fst , ∣ z , z₁ .snd .snd , x'∈Rz ∣₁ ∣₁) z∈S<=<Tx}) x'∈lhs 