module Prelude.Base where

open import Agda.Builtin.Unit          public
open import Agda.Builtin.Nat           public
  using () renaming (Nat to ℕ)
open import Agda.Builtin.Equality      public
open import Agda.Builtin.Sigma         public
  hiding (module Σ)
open import Agda.Builtin.List          public
  using (List; []; _∷_)
open import Agda.Builtin.Bool          public
open import Agda.Primitive as Prim     public
  using    (Level; _⊔_; lsuc; lzero)
  
open import Function                   public
open import Relation.Nullary           public
open import Relation.Nullary.Decidable public
  hiding (map)
  
variable
  ℓ ℓ′ ℓ₁ ℓ₂ ℓ₃ : Level
  A B C D : Set ℓ
  n m l   : ℕ
