{-# OPTIONS --safe --without-K  #-}

module Prelude.Decidable where

open import Prelude.Core

open import Relation.Nullary           public

record DecEq (A : Set ℓ) : Set (lsuc ℓ) where
  field
    _≟_ : (x y : A) → Dec (x ≡ y)
    
  DecEq⇒Eq : Eq A
  _==_ ⦃ DecEq⇒Eq ⦄ x y with x ≟ y
  ... | yes _ = true
  ... | no  _ = false
open DecEq ⦃...⦄ public

record DecOrd (A : Set ℓ) : Set (lsuc ℓ) where
  field
    ⦃ pord ⦄ : POrd A
    _≤?_ : (x y : A) → Dec (x ≤ y)

  _≥?_ = flip _≤?_

  DecOrd⇒Ord : ⦃ _ : Eq A ⦄ → Ord A
  _<=_ ⦃ DecOrd⇒Ord ⦄ x y with x ≤? y
  ... | yes _ = true
  ... | no  _ = false
  _<?_ ⦃ DecOrd⇒Ord ⦄ x y with x ≤? y | x /= y
  ... | yes _ | true = true
  ... |     _ | _    = false
open DecOrd ⦃...⦄ public
