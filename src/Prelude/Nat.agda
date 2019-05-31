{-# OPTIONS --safe --without-K  #-}

module Prelude.Nat where

open import Prelude.Core
open import Prelude.Decidable

open import Agda.Builtin.Word  as W    public
  using (Word64)
  
open import Data.Nat as Nat public
  hiding (_<_; _≤_; _≤?_; _<?_; _>_; _≟_; _≥_; _≥?_; _∸_; _*_)
  renaming (_⊔_ to max; _⊓_ to min)
open import Data.Nat.Properties as Natₚ
open import  Data.Nat.Show             public
  renaming (show to showℕ)
  
instance
  ℕ-DecEq : DecEq ℕ
  ℕ-DecEq = record { _≟_ = Natₚ._≟_ }

  ℕ-POrd : POrd ℕ
  ℕ-POrd = record { _≤_ = Nat._≤_ ; _<_ = Nat._<_ }

  ℕ-DecOrd : DecOrd ℕ
  ℕ-DecOrd = record { _≤?_ = Nat._≤?_  }

  ℕS      : Show ℕ
  show ⦃ ℕS ⦄ = showℕ

  wordS : Show Word64
  show ⦃ wordS ⦄ = show ∘ W.primWord64ToNat
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
