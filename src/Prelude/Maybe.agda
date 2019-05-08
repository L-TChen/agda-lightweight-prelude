module Prelude.Maybe where

open import Prelude.Base
open import Prelude.Instance

open import Data.Maybe as M hiding (map)
import Data.Maybe.Properties as Mₚ

instance
  MaybeFunctor : Functor {ℓ} Maybe
  MaybeFunctor = record { _<$>_ = M.map }

  MaybeMonad : Monad {ℓ} Maybe
  MaybeMonad = record
    { return = just
    ; _>>=_  = M._>>=_ }

  MaybeAlternative : Alternative {ℓ} Maybe
  MaybeAlternative = record { empty = nothing ; _<|>_ = M._<∣>_ }

  MaybeDecEq : ⦃ _ : DecEq A ⦄ → DecEq (Maybe A)
  MaybeDecEq = record { _≟_ = Mₚ.≡-dec _≟_ }
