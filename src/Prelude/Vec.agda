{-# OPTIONS --safe --without-K  #-}

module Prelude.Vec where

open import Prelude.Core

import Data.List as L
open import Data.Vec as V public
  using (Vec; []; _∷_)

diag : Vec (Vec A n) n -> Vec A n
diag []               = []
diag ((x ∷ xs) ∷ xss) = x ∷ diag (V.map V.tail xss)

instance
  VecMonad : Monad (λ A → Vec A n)
  VecMonad = record
    { return = V.replicate
    ; _>>=_  = λ ma f → diag (V.map f ma)
    }

  VecApplicative : Applicative (λ A → Vec A n)
  VecApplicative = monad⇒applicative 
  
  VecFoldable : Foldable (λ A → Vec A n)
  VecFoldable {n = zero}  = record { foldr = λ { f z []       → z } }
  VecFoldable {n = suc n} = record { foldr = λ { f z (x ∷ xs) → f x (foldr f z xs) } }

  VecFunctor : Functor (λ A → Vec A n)
  VecFunctor = VecApplicative .functor

  VecTraversable : Traversable (λ A → Vec A n)
  VecTraversable {n = zero}  = record { traverse = λ { _ []       → pure [] } }
  VecTraversable {n = suc n} = record { traverse = λ { f (x ∷ xs) → ⦇ _∷_ (f x) (traverse f xs) ⦈} } 

  private
    ℕ-+-monoid : Monoid ℕ _+_
    ℕ-+-monoid = record { ε = 0 }
    
  VecAlternative : MAlternative λ n A → Vec A n
  VecAlternative = record { empty = [] ; _<|>_ = V._++_ }
  
  VecSequence : ISequence (Vec A)
  VecSequence {A = A} = record
    { zeroIdx  = 0
    ; unitIdx  = 1
    ; addIdx   =  _+_
    ; carrier  = A
    ; [_]      = V.[_]
    ; emptySeq = []
    ; _++_     = V._++_
    ; length   = λ {n} xs → n
    ; fromList = λ xs → L.length xs , V.fromList xs 
    ; toList   = λ { (n , xs) → V.toList xs }
    }
