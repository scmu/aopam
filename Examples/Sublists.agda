{-# OPTIONS --cubical #-}
module Examples.Sublists where

open import Cubical.Foundations.Powerset as P -- using (ℙ; _∈_; _⊆_; ⊆-refl)
open import Cubical.Foundations.Prelude
open import Cubical.HITs.PropositionalTruncation.Base
open import Cubical.Data.Sum.Base using (_⊎_)

open import Data.List
open import Sets
open import Monad
open import Cubical.Foundations.HLevels
open import Reasoning 
-- using (⊆begin_; _⊆⟨_⟩_; _⊆∎)

sublists : List X → ℙ (List X) 
sublists []       = return []
sublists (x ∷ xs) = yss ∪ (_∷_ x) <$> yss
    where yss = sublists xs

  -- sublists having an even number of elements 

evnsublists : List X → ℙ (List X)
evnsublists []           = return []
evnsublists (x ∷ [])     = return []
evnsublists (x ∷ y ∷ xs) = yss ∪ (_∷_ x) <$> ((_∷_ y) <$> yss)
   where yss = evnsublists xs

sublists⊇[] : (xs : List X) → return [] ⊆ sublists xs  
sublists⊇[] [] _ x∈return[] = x∈return[]
sublists⊇[] (x ∷ xs) ys ys∈return[] = ∣ _⊎_.inl (sublists⊇[] xs ys ys∈return[]) ∣₁

sublists⊒evnsublists : ∀ {X} → sublists {X} ⊒ evnsublists {X}
sublists⊒evnsublists {X} [] = λ x z → z
sublists⊒evnsublists {X} (x ∷ []) = λ x₁ z → ∣ _⊎_.inl z ∣₁
sublists⊒evnsublists {X} (x ∷ y ∷ xs) = 
  ⊆begin
    evnsublists (x ∷ y ∷ xs)
  ⊆⟨ (λ x z → z) ⟩ -- refl
    evnsublists xs ∪ (_∷_ x) <$> ((_∷_ y) <$> evnsublists xs)
  ⊆⟨ ⊆-∪-monotonic-left (evnsublists xs) (sublists xs) ((_∷_ x) <$> ((_∷_ y) <$> evnsublists xs)) (sublists⊒evnsublists xs) ⟩ -- induction on leftmost evnsublists xs
    sublists xs ∪ (_∷_ x) <$> ((_∷_ y) <$> evnsublists xs)
  ⊆⟨ ⊆-∪-monotonic-right ((_∷_ x) <$> ((_∷_ y) <$> evnsublists xs)) ((_∷_ x) <$> ((_∷_ y) <$> sublists xs)) (sublists xs) (<$>-monotonic (_∷_ x) (<$>-monotonic (_∷_ y) (sublists⊒evnsublists xs))) ⟩  -- induction on evnsublists xs
    sublists xs ∪ (_∷_ x) <$> ((_∷_ y) <$> sublists xs)
  ⊆⟨ ⊆-∪-monotonic-right ((_∷_ x) <$> ((_∷_ y) <$> sublists xs)) ((_∷_ x) <$> (sublists xs ∪ (_∷_ y) <$> sublists xs)) (sublists xs) (>>=-monotonic (λ ys → return (x ∷ ys)) λ x₁ x₂ → ∣ _⊎_.inr x₂ ∣₁) ⟩ -- >>=-monotonic
    sublists xs ∪ (_∷_ x) <$> (sublists xs ∪ (_∷_ y) <$> sublists xs)
  ⊆⟨ (λ x z → z) ⟩ -- refl
    sublists xs ∪ (_∷_ x) <$> (sublists (y ∷ xs))
  ⊆⟨ ⊆-∪-monotonic-left (sublists xs) ((sublists xs ∪ (_∷_ y) <$> sublists xs)) ((_∷_ x) <$> (sublists (y ∷ xs))) (λ x₁ z → ∣ _⊎_.inl z ∣₁) ⟩
    (sublists xs ∪ (_∷_ y) <$> sublists xs) ∪ (_∷_ x) <$> (sublists (y ∷ xs)) --  ⊆-∪-monotonic-left
  ⊆⟨ (λ x z → z) ⟩ -- refl
    sublists (y ∷ xs) ∪ (_∷_ x) <$> (sublists (y ∷ xs))
  ⊆⟨ (λ x z → z) ⟩ -- refl
    sublists (x ∷ y ∷ xs)
  ⊆∎



{- 
    evnsublists (x ∷ y ∷ xs) 
  =   {- definition of evnsublists -}
    evnsublists xs ∪ (_∷_ x) <$> ((_∷_ y) <$> evnsublists xs)
  ⊆   {- induction -} -- split to two steps
    sublists xs ∪ (_∷_ x) <$> ((_∷_ y) <$> sublists xs)
  ⊆   {- mononticity of (>>=) -}
    sublists xs ∪ (_∷_ x) <$> (sublists xs ∪ (_∷_ y) <$> sublists xs)
  =   {- definition of sublists -}
    sublists xs ∪ (_∷_ x) <$> (sublists (y ∷ xs)) 
  ⊆   {- mononticity of ∪ -} 
    (sublists xs ∪ (_∷_ y) <$> sublists xs) ∪ (_∷_ x) <$> (sublists (y ∷ xs)) 
  =   {- definition of sublists -}
    sublists (y ∷ xs) ∪ (_∷_ x) <$> (sublists (y ∷ xs)) 
  =   {- definition of sublists -}
    sublists (x ∷ y ∷ xs)
-}

  