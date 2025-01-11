{-# OPTIONS --cubical #-}
module Examples.Sublists where

open import Cubical.Foundations.Powerset as P using (ℙ; _∈_; _⊆_)

open import Data.List
open import Sets
open import Monad

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
sublists⊇[] = {!   !}

sublists⊒evnsublists : ∀ {X} → sublists {X} ⊒ evnsublists {X}
sublists⊒evnsublists = {!   !}

{- 
    evnsublists (x ∷ y ∷ xs) 
  =   {- definition of evnsublists -}
    evnsublists xs ∪ (_∷_ x) <$> ((_∷_ y) <$> evnsublists xs)
  ⊆   {- induction -}
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