{-# OPTIONS --safe --without-K  #-}

module Prelude.String where

open import Prelude.Base

import Data.String as S

instance
  String-DecEq : DecEq String
  String-DecEq = record { _≟_ = S._≟_ }
