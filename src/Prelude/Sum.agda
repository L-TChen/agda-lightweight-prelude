module Prelude.Sum where

open import Prelude.Core

import Data.Sum
open module Sum = Data.Sum public
  hiding (map; map₁; map₂; swap)

MonadE+Monad : {F : Fun} ⦃ _ : Monad F ⦄ {E : Set} → Monad (F ∘ (E ⊎_))
return ⦃ MonadE+Monad ⦄ a    = return $ inj₂ a
_>>=_  ⦃ MonadE+Monad ⦄ ma f = do
  inj₂ a ← ma where (inj₁ e) → return $ inj₁ e
  f a

instance
  +-Bifunc : Bifunctor _⊎_
  +-Bifunc = record { bimap = Sum.map }

  +-SymBifunc : SymBifunctor _⊎_
  +-SymBifunc = record { swap = Sum.swap }

  E+Monad : {E : Set} → Monad (E ⊎_)
  E+Monad = record { return = inj₂ ; _>>=_ = λ { (inj₁ e) f → inj₁ e ; (inj₂ a) f → f a } }
  
  MonadExcept : {E : Set} → MonadError E (E ⊎_)
  MonadExcept = record
    { throw      = inj₁
    ; try_catch_ = λ
      { (inj₁ e) f → f e
      ; (inj₂ a) _ → inj₂ a }
    }
