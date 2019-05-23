{-# OPTIONS --safe --without-K #-}

module Prelude.Maybe where

open import Prelude.Core
open import Prelude.Decidable

open import Data.Maybe as M  public
  using (Maybe; nothing; just; maybe)
import Data.Maybe as M
import Data.Maybe.Properties as Mₚ

instance
  MaybeMonad : Monad Maybe
  return ⦃ MaybeMonad ⦄ = just
  _>>=_ ⦃ MaybeMonad ⦄ (just x) f = f x
  _>>=_ ⦃ MaybeMonad ⦄ nothing f  = nothing

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
