{-# OPTIONS --safe --without-K  #-}

module Prelude.Bool where

open import Prelude.Base
import Data.Bool as B

--open module Bool = B public
--  hiding (Bool; true; false; _≟_; decSetoid; _≤_; _<_; _≤?_)

instance
  BoolDecEq : DecEq Bool
  BoolDecEq = record { _≟_ = B._≟_ }

  BoolPOrd : POrd Bool
  BoolPOrd = record { _≤_ = B._≤_ ; _<_ = B._<_ }

  BoolDecPOrd : DecOrd Bool
  BoolDecPOrd = record { _≤?_ = B._≤?_ }
