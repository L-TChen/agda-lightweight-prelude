module Prelude.Relation where

open import Relation.Nullary                      public
open import Relation.Nullary.Decidable            public hiding (map)
open import Relation.Binary                       public
  renaming (_⇒_ to _⊆_)
open import Relation.Binary.PropositionalEquality public hiding ([_])
