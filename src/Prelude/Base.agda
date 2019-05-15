module Prelude.Base where


  
open import Agda.Builtin.Unit          public
open import Agda.Builtin.Nat           public
  using (suc; zero; _+_) renaming (Nat to ℕ)
open import Agda.Builtin.Equality      public
open import Agda.Builtin.Sigma         public
  hiding (module Σ)
open import Agda.Builtin.List          public
open import Agda.Builtin.Bool          public
open import Agda.Builtin.Word          public
open import Agda.Builtin.String        public

_+++_ : String → String → String
_+++_ = primStringAppend
infixr 5 _+++_

open import Level                      public
  using (Level; _⊔_; Lift; lower; lift)
  renaming (suc to lsuc; zero to lzero)
open import Data.Empty                 public
open import Function                   public
open import Relation.Nullary           public
open import Relation.Nullary.Decidable public
  hiding (map)
  
variable
  ℓ ℓ′ ℓ₁ ℓ₂ ℓ₃ : Level
  A B C D : Set ℓ
  n m l   : ℕ
