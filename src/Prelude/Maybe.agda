{-# OPTIONS --safe --without-K #-}

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
  foldr ⦃ MaybeFoldable ⦄ f z (just x) = f x z
  foldr ⦃ MaybeFoldable ⦄ f z nothing = z

  MaybeFunctor : Functor Maybe
  MaybeFunctor = MaybeApplicative .functor
  
  MaybeTraversable : Traversable Maybe
  traverse ⦃ MaybeTraversable ⦄ f (just x) = just <$> f x
  traverse ⦃ MaybeTraversable ⦄ f nothing  = pure nothing

  MaybeMonadErr : MonadError ⊤ Maybe
  MaybeMonadErr = record { throw = λ _ → nothing ; try_catch_ = λ { nothing f → f tt ; x _ → x } }

  MaybeDecEq : ⦃ _ : DecEq A ⦄ → DecEq (Maybe A)
  MaybeDecEq = record { _≟_ = Mₚ.≡-dec _≟_ }
