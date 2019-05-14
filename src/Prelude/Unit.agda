module Prelude.Unit where

open import Prelude.Base
open import Prelude.Instance

open import Data.Unit as Unit public
  hiding (_≟_; _≤_; _≤?_; decSetoid; preorder; setoid)

instance
  ⊤-DecEq : DecEq ⊤
  ⊤-DecEq = record { _≟_ = Unit._≟_ }

  ⊤-Ord : Ord ⊤
  ⊤-Ord = record { _<=_ = λ x y → ⌊ x Unit.≤? y ⌋ }
