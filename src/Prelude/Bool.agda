module Prelude.Bool where

open import Prelude.Instance
open import Data.Bool as Bool public
  hiding (_≟_; decSetoid; _≤_; _<_)

instance
  BoolDecEq : DecEq Bool
  BoolDecEq = record { _≟_ = Bool._≟_ }

  BoolPOrd : POrd Bool
  BoolPOrd = record { _≤_ = Bool._≤_ ; _<_ = Bool._<_ }
