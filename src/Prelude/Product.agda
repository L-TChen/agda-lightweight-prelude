module Prelude.Product where

open import Prelude.Base

import Data.Product as P
open module Product = P public
  hiding (_,_; swap; Σ; map₁; map₂; map; zip)

instance
  ×-Bifunc : Bifunctor _×_
  bimap {{×-Bifunc}} f g = P.map f g

  ×-SymBifunc : SymBifunctor _×_
  swap {{×-SymBifunc}}   = P.swap

  ×-Show : {P : A → Set ℓ} ⦃ _ : Show A ⦄ ⦃ _ : ∀ {x} → Show (P x) ⦄ → Show (Σ A P)
  ×-Show = record { show = λ { (a , b) → "( " ++ show a ++ " , " ++ show b ++ " )" } }
