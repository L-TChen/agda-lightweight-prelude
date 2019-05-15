module Prelude.Reflection where

open import Prelude.Base
open import Prelude.Instance

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Reflection as Reflection public
  hiding (return; _>>_; _>>=_; _≟_) 

infixl 1 _>>=TC_

_>>=TC_ = bindTC

instance
  TCM : Monad {ℓ} TC
  TCM = record
    { return = Reflection.return
    ; _>>=_  = Reflection.bindTC }

  TCAlter : Alternative {ℓ} TC
  TCAlter = record
    { azero = typeError []
    ; _<|>_ = catchTC
    }
  
  TCEMonad : {E : Set} → Monad {ℓ} $ TC ∘ (E ⊎_)
  TCEMonad = record
    { return = λ a → inj₂ <$> return a
    ; _>>=_  = λ ma f → do
      (inj₂ a) ← ma 
        where (inj₁ e) → return $ inj₁ e
      f a }
  
  TCEError : {E : Set} → MonadError {ℓ₁ = ℓ} E $ TC ∘ (E ⊎_)
  TCEError = record
    { throw      = return ∘ inj₁
    ; try_catch_ = λ ma handler → do
      inj₁ e ← ma
        where inj₂ a → return a
      handler e } 
  
  NameIsDecEq : DecEq Name
  NameIsDecEq = record { _≟_ = _≟-Name_ }
  
  TermIsDecEq : DecEq Term
  TermIsDecEq = record { _≟_ = Reflection._≟_ }

  LitIsDecEq : DecEq Literal
  LitIsDecEq = record { _≟_ = _≟-Lit_ }

  VisibilityShow : Show Visibility
  VisibilityShow = record
    { show = λ
      { visible → "Explicit"
      ; hidden  → "Implicit"
      ; instance′ → "Instance" } }

  RelevanceShow : Show Relevance
  RelevanceShow = record
    { show = λ
      { relevant   → "relevant"
      ; irrelevant → "irrelevant" } }
      
  ArgInfoShow : Show Arg-info
  ArgInfoShow = record { show = λ { (arg-info v r) → show v +++ " " +++ show r +++ " arg" } }
