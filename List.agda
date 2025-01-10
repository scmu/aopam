{-# OPTIONS --cubical #-}
module List where

open import Data.List hiding (foldr)
open import Cubical.Foundations.Powerset as P using (ℙ; _∈_; _⊆_)
open import Monad

variable
    A B : Set
  
foldr : (A → B → ℙ B) → ℙ B → List A → ℙ B
foldr f e []       = e 
foldr f e (x ∷ xs) = f x =<< foldr f e xs 