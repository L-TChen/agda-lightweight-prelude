{-# OPTIONS --safe --without-K  #-}

module Prelude.Unit where

open import Prelude.Core
open import Prelude.Decidable

import Data.Unit as U 
--open module Unit = U public
--  hiding (module ⊤; tt; ⊤; _≟_; _≤_; _≤?_; decSetoid; preorder; setoid)

instance
  ⊤-Eq : Eq ⊤
  ⊤-Eq = record { _==_ = λ _ _ → true }
  
  ⊤-Ord : Ord ⊤
  ⊤-Ord = record { _<=_ = λ _ _ → true ; _<?_ = λ _ _ → false }

  ⊤-DecEq : DecEq ⊤
  ⊤-DecEq = record { _≟_ = U._≟_ }
