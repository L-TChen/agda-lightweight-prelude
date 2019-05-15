module Prelude.DiffList where

open import Prelude.Base
open import Prelude.Instance

open import Data.DifferenceList as DList public
  hiding (_∷_; []; concat; drop; take; _++_; [_]; fromList; toList; lift; map)

import Data.List.Properties as Lₚ
import Data.List as L

module DiffList = DList

instance
  DiffListMonad : Monad {ℓ} DiffList
  DiffListMonad = record
    { return = DList.[_]
    ; _>>=_ = λ xs f → DList.concat $ DList.map f xs }

  DListAlternative : Alternative {ℓ} DiffList
  DListAlternative = record
    { azero = DList.[]
    ; _<|>_ = DList._++_ }

  DList-ListLike : {A : Set ℓ} → ListLike (λ _ → DiffList A)
  DList-ListLike {A = A} = record
    { base  = A
    ; empty = id ; singleton = DList.[_] ; _++_ = λ xs ys → xs ∘ ys
    ; length   = L.length ∘ DList.toList
    ; fromList = λ xs → L.length xs , DList.fromList xs
    ; toList   = λ { (_ , xs) → DList.toList xs }
    }
  
--  DiffListDecEq : ⦃ _ : DecEq A ⦄ → DecEq (DiffList A)
-- this requires functional extensionality 
