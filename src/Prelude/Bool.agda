{-# OPTIONS --safe --without-K  #-}

module Prelude.Bool where

open import Prelude.Core
open import Prelude.Decidable

open import Data.Bool as B public
  hiding (Bool; true; false; _≟_; decSetoid; not; if_then_else_)
  --hiding (Bool; true; false; _≟_; decSetoid; _≤_; _<_; _≤?_; _<?_; not; if_then_else_)

instance
  BoolDecEq : DecEq Bool
  BoolDecEq = record { _≟_ = B._≟_ }

  BoolEq : Eq Bool
  BoolEq = DecEq⇒Eq
{-
  BoolPOrd : POrd Bool
  BoolPOrd = record { _≤_ = B._≤_ ; _<_ = B._<_ }

  BoolDecPOrd : DecOrd Bool
  BoolDecPOrd = record { _≤?_ = B._≤?_ }

  BoolOrd : Ord Bool
  BoolOrd = DecOrd⇒Ord
-}
