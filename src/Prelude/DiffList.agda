{-# OPTIONS --safe --without-K  #-}

module Prelude.DiffList where

open import Prelude.Base

open import Data.DifferenceList as D
  using (DiffList)

instance
  DiffListMonad : Monad DiffList
  DiffListMonad = record
    { return = D.[_]
    ; _>>=_ = λ xs f → D.concat $ D.map f xs }

  DListApplicative : Applicative DiffList
  DListApplicative = monad⇒applicative
  
  DListAlternative : Alternative DiffList
  DListAlternative = record
    { azero = D.[]
    ; _<|>_ = D._++_ }

  DListSequence : {A : Set ℓ} → Sequence (DiffList A)
  DListSequence {A = A} = record
    { zeroIdx = tt
    ; unitIdx = tt
    ; addIdx = λ _ _ → tt
    ; carrier = A
    ; [_] = D.[_]
    ; empty = D.[]
    ; _++_ = D._++_
    ; length = length ∘ D.toList
    ; fromList = λ xs → _ , D.fromList xs
    ; toList = λ { (_ , xs) → D.toList xs }
    }
