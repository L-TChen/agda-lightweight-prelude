module Prelude.Nat where

open import Prelude.Base
open import Prelude.Instance

open import Data.Nat.Base as ℕ public
  hiding (suc; pred)
  renaming (_⊔_ to max; _⊓_ to min)
open import Data.Nat.Properties as ℕₚ

instance
  ℕ-DecEq : DecEq ℕ
  ℕ-DecEq = record { _≟_ = ℕₚ._≟_ }

  ℕ-Enum : Enum ℕ
  ℕ-Enum = record
    { succ = ℕ.suc ; pred = ℕ.pred ; toEnum = id ; fromEnum = id }
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
