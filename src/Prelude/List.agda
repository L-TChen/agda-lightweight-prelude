{-# OPTIONS --overlapping-instances #-}

module Prelude.List where

open import Prelude.Base
open import Prelude.Instance

open import Data.List as L public
  hiding (foldr; map; [_]; _++_; length; replicate; zip; zipWith)
import Data.List.Properties as Lₚ

instance
  ListMonad : Monad {ℓ} L.List
  ListMonad = record
    { return = L.[_]
    ; _>>=_ = λ xs f → concat $ L.map f xs 
    }
  ListListLike : ∀ {A : Set ℓ} → ListLike {ℓ} (λ _ → L.List A)
  ListListLike {A = A} = record
    { base = A
    ; empty = L.[]
    ; singleton = L.[_]
    ; _++_ = L._++_
    ; length = L.length
    ; toList   = snd
    ; fromList = λ xs → L.length xs , xs
    }

  ListAlternative : Alternative {ℓ} L.List
  ListAlternative = record
    { azero = []
    ; _<|>_ = L._++_
    }

  ListFoldable : Foldable {ℓ} L.List
  ListFoldable = record { foldr = L.foldr }

  ListTraversable : Traversable {ℓ} L.List
  ListTraversable = record
    { traverse = λ f → L.foldr (λ x ys → ⦇ _∷_ (f x) ys ⦈) (pure []) }

  ListShow : ⦃ _ : Show A ⦄ → Show (List A)
  ListShow = record { show = L.foldr (λ x xs → show x +++ " ∷ " +++ xs) " []" }

  ListDecEq : ⦃ _ : DecEq A ⦄ → DecEq (L.List A)
  ListDecEq ⦃ record { _≟_ = _≟_ } ⦄ = record { _≟_ = Lₚ.≡-dec _≟_ }
