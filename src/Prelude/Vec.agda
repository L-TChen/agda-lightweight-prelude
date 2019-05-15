{-# OPTIONS --overlapping-instances #-}

module Prelude.Vec where

open import Prelude.Base
open import Prelude.Instance

import Data.List as L
  using (length)
open import Data.Vec as Vec public
  using (Vec; []; _∷_)

diag : Vec (Vec A n) n -> Vec A n
diag []               = []
diag ((x ∷ xs) ∷ xss) = x ∷ diag (Vec.map Vec.tail xss)

instance
  VecMonad : Monad {ℓ} (λ A → Vec A n)
  VecMonad = record
    { return = Vec.replicate
    ; _>>=_  = λ ma f → diag (Vec.map f ma)
    }

  VecFoldable : Foldable {ℓ} (λ A → Vec A n)
  VecFoldable {n = zero}  = record { foldr = λ { f z []       → z } }
  VecFoldable {n = suc n} = record { foldr = λ { f z (x ∷ xs) → f x (foldr f z xs) } }

  VecTraversable : Traversable {ℓ} (λ A → Vec A n)
  VecTraversable {n = zero}  = record { traverse = λ { _ []       → pure [] } }
  VecTraversable {n = suc n} = record { traverse = λ { f (x ∷ xs) → ⦇ _∷_ (f x) (traverse f xs) ⦈} } 

  private
    ℕ-+-monoid : Monoid ℕ
    ℕ-+-monoid = record
      { ε = 0
      ; semigroup = record { _∙_ = _+_ }
      } 
  VecAlternative : MAlternative {ℓ₁ = ℓ} ℕ λ n A → Vec A n
  VecAlternative = record { azero = [] ; _<|>_ = Vec._++_ }
  
  VecListLike : ∀ {A : Set ℓ} → ListLike (Vec A)
  VecListLike {A = A} = record
    { base      = A
    ; singleton = Vec.[_]
    ; empty     = []
    ; _++_      = Vec._++_
    ; length    = λ {n} xs → n
    ; fromList  = λ xs → L.length xs , Vec.fromList xs
    ; toList    = λ { (n , xs) → Vec.toList xs }
    }
