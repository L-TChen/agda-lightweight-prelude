{-# OPTIONS --safe --without-K  #-}

module Prelude.List where

open import Prelude.Core
open import Prelude.Decidable

open import Data.Maybe
  using (Maybe; nothing; just)
open import Data.List as L public
  hiding (List; []; _∷_; foldr; map; [_]; _++_; length; replicate; zip; zipWith)
import Data.List.Properties as Lₚ

infixl 20 _!!_

_!!_ : List A → ℕ → Maybe A
[]       !! _       = nothing
(x ∷ xs) !! zero    = just x
(x ∷ xs) !! (suc n) = xs !! n

instance
{-
  ListMonad : Monad L.List
  ListMonad = record
    { return = L.[_]
    ; _>>=_ = λ xs f → L.concat $ L.map f xs 
    }

  ListApplicative : Applicative List
  ListApplicative = monad⇒applicative
-}
  ListAlternative : Alternative L.List
  ListAlternative = record
    { azero = []
    ; _<|>_ = L._++_
    }
{-
  ListFoldable : Foldable L.List
  ListFoldable = record { foldr = L.foldr }

  ListTraversable : Traversable L.List
  ListTraversable = record
    { traverse = λ f → L.foldr (λ x ys → ⦇ _∷_ (f x) ys ⦈) (pure []) }
-}
  ListShow : ⦃ _ : Show A ⦄ → Show (List A)
  ListShow = record { show = L.foldr (λ x xs → show x ++ " ∷ " ++ xs) " []" }

  ListDecEq : ⦃ _ : DecEq A ⦄ → DecEq (L.List A)
  ListDecEq ⦃ record { _≟_ = _≟_ } ⦄ = record { _≟_ = Lₚ.≡-dec _≟_ }
