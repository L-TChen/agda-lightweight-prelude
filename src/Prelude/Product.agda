module Prelude.Product where

open import Prelude.Base
open import Prelude.Instance

open import Data.Product as Product public
  hiding (map; zip; map₁; map₂; swap)

instance
  ×-Bifunc : Bifunctor {ℓ} {ℓ′} _×_
  bimap {{×-Bifunc}} f g = Product.map f g

  ×-SymBifunc : SymBifunctor {ℓ} _×_
  swap {{×-SymBifunc}}   = Product.swap
