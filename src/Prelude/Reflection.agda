module Prelude.Reflection where

open import Prelude.Base
open import Prelude.Instance

open import Agda.Builtin.List
open import Agda.Builtin.Unit using (⊤)
open import Reflection public
  hiding (return; _>>_; _>>=_; _≟_; bindTC) 

instance
  TCM : Monad {ℓ} TC
  TCM = record { return = Reflection.return ; _>>=_ = Reflection.bindTC }

  TCAlter : Alternative {ℓ} TC
  TCAlter = record
    { empty = typeError List.[]
    ; _<|>_ = catchTC
    }

  TermIsDecEq : DecEq Term
  TermIsDecEq = record { _≟_ = Reflection._≟_ }

  LitIsDecEq : DecEq Literal
  LitIsDecEq = record { _≟_ = _≟-Lit_ }
