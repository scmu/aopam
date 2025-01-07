{-# OPTIONS --cubical #-}

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

map : (X → Y) → ℙ X → ℙ Y
map {X} {Y} f xs y = ∥ Σ X (λ x → (x ∈ xs) × (f x ≡ y)) ∥₁ , squash₁

incl : {X : Set} → (e₀ e₁ : ℙ X) 
     -- → (∀ x → fst (e₀ x) → fst (e₁ x))
     → (x : X) → ⟨ e₀ x ⇒ e₁ x ⟩
incl e₀ e₁ x = {! rec (snd (e₁ x))   !} -- rec (snd (e₁ x)) (f x)

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
{-                   
              (rec (snd (map (g ∘ f) xs z)) 
                  λ { (y , y∈fxs , eq₁) → 
                   rec (snd (map (g ∘ f) xs z)) 
                      (λ {(x , x∈xs , eq₂) → 
                       ∣ x , x∈xs , subst (λ w → g w ≡ z) (sym eq₂) eq₁ ∣₁ }) y∈fxs  })
-}


_>>=_ : {X Y : Set} → ℙ X → (X → ℙ Y) → ℙ Y
(_>>=_ {X} {Y} xs f) y =  ∥ Σ X (λ x → fst (xs x) × fst (f x y)) ∥₁ , squash₁ -- prop := (prop, f prop)

return : {X : Set} → X → ℙ X
return x x' = ∥ x ≡ x' ∥₁ , squash₁


ret-right-id : {X : Set} (m : ℙ X) 
             → (m >>= return) ≡ m
ret-right-id m = funExt λ x → ⇔toPath 
                 (rec (snd (m x)) λ { (x' , x'∈m , eq') → 
                    rec (snd (m x)) (λ eq → subst _ eq x'∈m) eq' })
                  λ x∈m → ∣ x , x∈m , ∣ refl ∣₁ ∣₁ 
    -- where open TruncMonad

ret-right-id' : {X : Set} (m : ℙ X) 
             → (m >>= return) ≡ m
ret-right-id' m = funExt λ x → ⇔toPath (λ y → rec (snd (m x)) (λ { (x' , x'∈m , eq') → rec (snd (m x)) (λ x≡x' → subst (λ r → fst (m r)) x≡x' x'∈m) eq'})  y ) (λ prop → ∣  x , (prop , ∣ refl ∣₁) ∣₁)


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
  
-- union

∪-op : {X : Set} → ℙ X → ℙ X → ℙ X
∪-op A B x = ∥ (x ∈ A) ⊎ (x ∈ B) ∥₁ , squash₁ -- (x ∈ A ⊎ x ∈ B) ≡  ⟨ A x ⟩ ⊎ ⟨ B x ⟩

infixl 6 _∪_

_∪_ : ℙ X → ℙ X → ℙ X
_∪_ = ∪-op

-- Union is commutative
∪-comm : {X : Set} (A B : ℙ X) → A ∪ B ≡ B ∪ A
∪-comm {X} A B = P.⊆-extensionality (A ∪ B) (B ∪ A) ((λ x x₁ → rec (snd ((B ∪ A) x)) (helper x A B) x₁) , λ x x₁ → rec (snd ((A ∪ B) x)) (helper x B A) x₁)
    where
        helper : (x : X) → (A B : ℙ X) → (x ∈ A) ⊎ (x ∈ B) → (B ∪ A) x .fst
        helper x A B (_⊎_.inl x₁) = ∣ _⊎_.inr x₁ ∣₁
        helper x A B (_⊎_.inr x₁) = ∣ _⊎_.inl x₁ ∣₁

-- Union is associative
∪-assoc : {X : Set} (A B C : ℙ X) → (A ∪ B) ∪ C ≡ A ∪ (B ∪ C)
∪-assoc A B C = P.⊆-extensionality (A ∪ B ∪ C) (A ∪ (B ∪ C)) ((λ x x₁ → rec (snd ((A ∪ (B ∪ C)) x)) (helper x A B C) x₁) , λ x x₁ → rec (snd ((A ∪ B ∪ C) x)) (helper3 x A B C) x₁)
    where
        helper : (x : X) → (A B C : ℙ X) → (x ∈ A ∪ B) ⊎ (x ∈ C) → (A ∪ (B ∪ C)) x .fst
        helper x A B C (_⊎_.inl x₁) = rec (snd ((A ∪ (B ∪ C)) x)) helper2 x₁
            where
                helper2 : (x ∈ A) ⊎ (x ∈ B) → (A ∪ (B ∪ C)) x .fst
                helper2 (_⊎_.inl x) = ∣ _⊎_.inl x ∣₁
                helper2 (_⊎_.inr x) = ∣ _⊎_.inr ∣ _⊎_.inl x ∣₁ ∣₁
        helper x A B C (_⊎_.inr x₁) = ∣ _⊎_.inr ∣ _⊎_.inr x₁ ∣₁ ∣₁

        helper3 : (x : X) → (A B C : ℙ X) → (x ∈ A) ⊎ (x ∈ B ∪ C) → (A ∪ B ∪ C) x .fst
        helper3 x A B C (_⊎_.inl x₁) = ∣ _⊎_.inl ∣ _⊎_.inl x₁ ∣₁ ∣₁
        helper3 x A B C (_⊎_.inr x₁) = rec (snd ((A ∪ B ∪ C) x)) helper4 x₁
            where
                helper4 : (x ∈ B) ⊎ (x ∈ C) → (A ∪ B ∪ C) x .fst
                helper4 (_⊎_.inl x) = ∣ _⊎_.inl ∣ _⊎_.inr x ∣₁ ∣₁
                helper4 (_⊎_.inr x) = ∣ _⊎_.inr x ∣₁

-- Subset properties for union
⊆-∪-left : {X : Set} (A B : ℙ X) → A ⊆ (A ∪ B)
⊆-∪-left A B x = inl

⊆-∪-right : {X : Set} (A B : ℙ X) → B ⊆ (A ∪ B)
⊆-∪-right A B x = inr



-- intersection

_∩_ : {X : Set} → ℙ X → ℙ X → ℙ X
_∩_ A B x = ((x ∈ A) × (x ∈ B)) , isProp× (P.∈-isProp A x) (P.∈-isProp B x)

-- ∈-∩ : {X : Set} →  (x : X) → (A B : ℙ X) → x ∈ (A ∩ B) ≃ (x ∈ A × x ∈ B)
-- ∈-∩ = ?

∩-comm : {X : Set} (A B : ℙ X) → A ∩ B ≡ B ∩ A
∩-comm {X} A B = P.⊆-extensionality (A ∩ B) (B ∩ A) ((λ x z → z .snd , z .fst) , (λ x z → z .snd , z .fst))

∩-assoc :  {X : Set} (A B C : ℙ X) → (A ∩ B) ∩ C ≡ A ∩ (B ∩ C)
∩-assoc {X} A B C = P.⊆-extensionality ((A ∩ B) ∩ C) (A ∩ (B ∩ C)) ((λ x z → z .fst .fst , (z .fst .snd , z .snd)) , (λ x z → (z .fst , z .snd .fst) , z .snd .snd))

∩-∪-dist : {X : Set} (A B C : ℙ X) → A ∩ (B ∪ C) ≡ (A ∩ B) ∪ (A ∩ C)
∩-∪-dist {X} A B C = P.⊆-extensionality (A ∩ (B ∪ C)) ((A ∩ B) ∪ (A ∩ C)) ((λ x x₁ → rec (snd (((A ∩ B) ∪ (A ∩ C))x)) (helper x x₁) (x₁ .snd)) , λ x x₁ → rec (snd ((A ∩ (B ∪ C))x)) (helper2 x) x₁)
    where 
        helper : (x : X) → (x ∈ (A ∩ (B ∪ C))) → (x ∈ B) ⊎ (x ∈ C) → ((A ∩ B) ∪ (A ∩ C)) x .fst
        helper x (fst₁ , snd₁) (_⊎_.inl x₁) = ∣ _⊎_.inl (fst₁ , x₁) ∣₁
        helper x (fst₁ , snd₁) (_⊎_.inr x₁) = ∣ _⊎_.inr (fst₁ , x₁) ∣₁

        helper2 : (x : X) → (x ∈ (A ∩ B)) ⊎ (x ∈ (A ∩ C)) → (A ∩ (B ∪ C)) x .fst
        helper2 x (_⊎_.inl x₁) = x₁ .fst , ∣ _⊎_.inl (x₁ .snd) ∣₁
        helper2 x (_⊎_.inr x₁) = x₁ .fst , ∣ _⊎_.inr (x₁ .snd) ∣₁

-- todo
∪-∩-dist : {X : Set} → (A B C : ℙ X) → A ∪ (B ∩ C) ≡ (A ∪ B) ∩ (A ∪ C)
∪-∩-dist {X} A B C = P.⊆-extensionality (A ∪ (B ∩ C)) ((A ∪ B) ∩ (A ∪ C)) {!   !}


⊆-∩-left : {X : Set} → (A B : ℙ X) → (A ∩ B) ⊆ A
⊆-∩-left {X} A B = λ x z → z .fst

⊆-∩-right : {X : Set} → (A B : ℙ X) → (A ∩ B) ⊆ B
⊆-∩-right {X} A B = λ x z → z .snd
