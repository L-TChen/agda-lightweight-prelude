module Prelude.Sum where

open import Prelude.Base
open import Prelude.Instance

open import Data.Sum as Sum public
  hiding (map; map₁; map₂; swap)

instance
  +-Bifunc : Bifunctor {ℓ} {ℓ′} _⊎_
  +-Bifunc = record { bimap = Sum.map }

  +-SymBifunc : SymBifunctor {ℓ} _⊎_
  +-SymBifunc = record { swap = Sum.swap }

  E+Monad : {E : Set ℓ} → Monad {ℓ} (E ⊎_)
  E+Monad = record { return = inj₂ ; _>>=_ = λ { (inj₁ e) f → inj₁ e ; (inj₂ a) f → f a } }
  
  MonadExcept : ∀ {E : Set ℓ} → MonadError E (E ⊎_)
  MonadExcept = record
    { throw      = inj₁
    ; try_catch_ = λ
      { (inj₁ e) f → f e
      ; (inj₂ a) _ → inj₂ a }
    }
