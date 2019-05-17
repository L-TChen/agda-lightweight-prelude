module Prelude.IO where

open import Prelude.Base

open import IO.Primitive as IO public
  hiding (_>>=_; return)

instance
  IOMonad : Monad IO
  return ⦃ IOMonad ⦄ = IO.return
  _>>=_  ⦃ IOMonad ⦄ = IO._>>=_
