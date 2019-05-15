{-# OPTIONS --overlapping-instances #-}

module Prelude.Maybe where

open import Prelude.Base
open import Prelude.Instance

open import Data.Maybe as Maybe public
  hiding (map; _>>=_; align; alignWith; ap; fromMaybe; zip; zipWith)
import Data.Maybe.Properties as Maybeₚ



instance
  MaybeMonad : Monad {ℓ} Maybe
  MaybeMonad = record
    { return = just
    ; _>>=_  = Maybe._>>=_ }

  MaybeAlternative : Alternative {ℓ} Maybe
  MaybeAlternative = record { azero = nothing ; _<|>_ = Maybe._<∣>_ }

  MaybeFoldable : Foldable {ℓ} Maybe
  MaybeFoldable = record { foldr = λ { f z nothing → z ; f z (just a) → f a z } }
  
  MaybeTraversable : Traversable {ℓ} Maybe
  MaybeTraversable {ℓ} = record { traverse = helper }
    where
      helper : {F : Set ℓ → Set ℓ} ⦃ _ : Applicative F ⦄ → (A → F B) → Maybe A → F (Maybe B)
      helper ⦃ apF ⦄ f (just x) = just <$> f x
      helper ⦃ apF ⦄ f nothing  = pure nothing
  
  MaybeDecEq : ⦃ _ : DecEq A ⦄ → DecEq (Maybe A)
  MaybeDecEq = record { _≟_ = Maybeₚ.≡-dec _≟_ }
