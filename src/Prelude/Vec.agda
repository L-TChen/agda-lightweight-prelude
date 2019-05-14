{-# OPTIONS --overlapping-instances #-}

module Prelude.Vec where

open import Prelude.Base
open import Prelude.Instance

open import Data.Vec as Vec public
  using (Vec; []; _∷_)

diag : Vec (Vec A n) n -> Vec A n
diag []             = []
diag ((x ∷ xs) ∷ xss) = x ∷ diag (Vec.map Vec.tail xss)

instance
  VecMonad : Monad {ℓ} (λ A → Vec A n)
  VecMonad = record
    { return = Vec.replicate
    ; _>>=_  = λ ma f → diag (Vec.map f ma)
    }
{-
  VecListLike : ∀ {A : Set ℓ} {n} → ListLike (Vec A n)
  VecListLike {A = A} = record
    { base = A
    ; singleton = {!Vec.[_]!}
    ; empty = {!!}
    ; _++_ = {!!}
    ; length = {!!}
    ; fromList = {!!}
    ; toList = {!!}
    }
-}
