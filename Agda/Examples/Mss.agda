{-# OPTIONS --cubical #-}
module Examples.Mss where

open import Data.List hiding (foldr)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Foundations.Powerset as P using (ℙ; _∈_; _⊆_)
open import Cubical.Data.Sigma.Base using (_×_) 

open import Monad_v2
open import Fold 
open import Sets 

private
    variable
        ℓ : Level
        X Y A B C : Type ℓ 


-- todo move it to List.agda
sublists : List A → ℙ (List A) 
sublists []       = return []
sublists (x ∷ xs) = yss ∪ (_∷_ x) <$> yss
    where yss = sublists xs