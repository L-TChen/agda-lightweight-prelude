{-# OPTIONS --overlapping-instances --safe --without-K #-}

module Prelude.Maybe where

open import Prelude.Base

import Data.Maybe as M
import Data.Maybe.Properties as Mₚ

instance
  MaybeMonad : Monad Maybe
  MaybeMonad = record
    { return = M.just
    ; _>>=_  = M._>>=_ }

  MaybeApplicative : Applicative Maybe
  MaybeApplicative = monad⇒applicative

  MaybeAlternative : Alternative Maybe
  MaybeAlternative = record { azero = nothing ; _<|>_ = M._<∣>_ }

  MaybeFoldable : Foldable Maybe
  MaybeFoldable = record { foldr = λ { f z nothing → z ; f z (just a) → f a z } }
  
  MaybeTraversable : Traversable Maybe
  MaybeTraversable = record { traverse = helper }
    where
      helper : {F : ∀ {ℓ} → Set ℓ → Set ℓ} ⦃ _ : Applicative F ⦄ → (A → F B) → Maybe A → F (Maybe B)
      helper f (just x) = just <$> f x
      helper f nothing  = pure nothing

  MaybeMonadErr : MonadError ⊤ Maybe
  MaybeMonadErr = record { throw = λ _ → nothing ; try_catch_ = λ { nothing f → f tt ; x _ → x } }

  MaybeDecEq : ⦃ _ : DecEq A ⦄ → DecEq (Maybe A)
  MaybeDecEq = record { _≟_ = Mₚ.≡-dec _≟_ }

