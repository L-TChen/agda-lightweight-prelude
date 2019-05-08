module Prelude.Bool where

open import Prelude.Instance
open import Data.Bool as Bool public
  hiding (_≟_; decSetoid)

instance
  BoolDecEq : DecEq Bool
  BoolDecEq = record { _≟_ = Bool._≟_ }
