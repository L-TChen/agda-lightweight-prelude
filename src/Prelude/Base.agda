module Prelude.Base where

open import Level    public
  hiding (zero)
  renaming (_⊔_ to ℓ-max)
open import Function public

variable
  ℓ ℓ′  : Level
  A B C D : Set ℓ
