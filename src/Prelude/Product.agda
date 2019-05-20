{-# OPTIONS --safe --without-K  #-}


module Prelude.Product where

open import Prelude.Core

open import Data.Product as P public
  hiding (swap; map; map₂; map₁; zip)

instance
  ×-Bifunc : Bifunctor P._×_
  bimap {{×-Bifunc}} f g = P.map f g

  ×-SymBifunc : SymBifunctor P._×_
  swap {{×-SymBifunc}}   = P.swap

  ×-Show : {P : A → Set ℓ} ⦃ _ : Show A ⦄ ⦃ _ : ∀ {x} → Show (P x) ⦄ → Show (Σ A P)
  ×-Show = record { show = λ { (a , b) → "( " ++ show a ++ " , " ++ show b ++ " )" } }
