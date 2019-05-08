{-# OPTIONS --overlapping-instances #-}

module Prelude.List where

open import Prelude.Base
open import Prelude.Instance
open import Data.List as List public
  hiding (foldr; map; [_]; _++_; length; replicate)
import Data.List.Properties as Lₚ

open import Data.DifferenceList as DiffList public
  using (DiffList)

instance
  ListMonad : Monad {ℓ} List
  ListMonad = record
    { return = List.[_]
    ; _>>=_ = λ xs f → concat $ List.map f xs 
    }
  ListListLike : ∀ {A : Set ℓ} → ListLike {ℓ} (List A)
  ListListLike {A = A} = record
    { base = A
    ; empty = List.[]
    ; singleton = List.[_]
    ; _++_ = List._++_
    ; length = List.length
    ; toList   = id
    ; fromList = id }

  ListAlternative : Alternative {ℓ} List
  ListAlternative = record
    { empty = []
    ; _<|>_ = _++_
    }

  ListFoldable : Foldable {ℓ} List
  ListFoldable = record { foldr = List.foldr }

  ListTraversable : Traversable {ℓ} List
  ListTraversable = record
    { traverse = λ f → foldr (λ x ys → _∷_ <$> f x <*> ys) (pure []) }

  ++-Monoid : {A : Set ℓ} → Monoid (List A)
  ++-Monoid = record { ε = [] ; _∙_ = _++_ }

  ListDecEq : ⦃ _ : DecEq A ⦄ → DecEq (List A)
  ListDecEq ⦃ record { _≟_ = _≟_ } ⦄ = record { _≟_ = Lₚ.≡-dec _≟_ }

  DiffList-ListLike : {A : Set ℓ} → ListLike (DiffList A)
  DiffList-ListLike {A = A} = record
    { base  = A
    ; empty = id ; singleton = λ a → a ∷_ ; _++_ = λ xs ys → xs ∘ ys
    ; length   = List.length ∘ DiffList.toList
    ; fromList = DiffList.fromList
    ; toList   = DiffList.toList }
  
  DiffList-Monoid : {A : Set ℓ} → Monoid (DiffList A)
  DiffList-Monoid = record { ε = id ; _∙_ = λ xs ys → xs ∘ ys } 
