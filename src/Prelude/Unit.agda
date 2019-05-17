module Prelude.Unit where

open import Prelude.Base

import Data.Unit as U 
open module Unit = U public
  hiding (tt; ⊤; _≟_; _≤_; _≤?_; decSetoid; preorder; setoid)

instance
  ⊤-Eq : Eq ⊤
  ⊤-Eq = record { _==_ = λ _ _ → true }
  
  ⊤-Ord : Ord ⊤
  ⊤-Ord = record { _<=_ = λ _ _ → true }

  ⊤-DecEq : DecEq ⊤
  ⊤-DecEq = record { _≟_ = Unit._≟_ }
