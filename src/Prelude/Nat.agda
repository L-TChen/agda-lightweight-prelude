module Prelude.Nat where

open import Prelude.Base
  hiding (module ℕ)

import Data.Nat as Nat
open module ℕ = Nat public
  hiding   (ℕ; suc; zero; _≤_; _<_; _+_; _<?_; _≤?_; _≥?_; _≟_; _>_; _≥_)
  renaming (_⊔_ to max; _⊓_ to min)
open import Data.Nat.Properties as Natₚ

instance
  ℕ-DecEq : DecEq ℕ
  ℕ-DecEq = record { _≟_ = Natₚ._≟_ }

  ℕ-POrd : POrd ℕ
  ℕ-POrd = record { _≤_ = Nat._≤_ ; _<_ = Nat._<_ }

  ℕ-DecOrd : DecOrd ℕ
  ℕ-DecOrd = record { _≤?_ = ℕ._≤?_  }
{-
  max-Lattice : ⊔-⊥-Lattice ℕ _≤_
  max-Lattice = record
    { ⊥   = zero
    ; lat = record {
      super = record {
        _∙_ = max } } }

  min-Lattice : ⊔-Lattice ℕ _≥_
  min-Lattice = record
    { super = record { _∙_ = min } }
-}
