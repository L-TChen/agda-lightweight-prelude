module Prelude.Nat where

open import Prelude.Base
open import Prelude.Instance

open import Data.Nat.Base as Nat public
  hiding (pred; _≤_; _<_)
  renaming (_⊔_ to max; _⊓_ to min)
open import Data.Nat.Properties as Natₚ

instance
  ℕ-DecEq : DecEq ℕ
  ℕ-DecEq = record { _≟_ = Natₚ._≟_ }

  ℕ-Enum : Enum ℕ
  ℕ-Enum = record { succ = ℕ.suc ; pred = Nat.pred ; toEnum = id ; fromEnum = id }

  ℕ-POrd : POrd ℕ
  ℕ-POrd = record { _≤_ = Nat._≤_ ; _<_ = Nat._<_ }
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
