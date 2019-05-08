module Prelude.IO where

open import Prelude.Base
open import Prelude.Instance

open import IO.Primitive as IO public
  hiding (_>>=_; return)

instance
  IOMonad : Monad {ℓ} IO
  return ⦃ IOMonad ⦄ = IO.return
  _>>=_  ⦃ IOMonad ⦄ = IO._>>=_
