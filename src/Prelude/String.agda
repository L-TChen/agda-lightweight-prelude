module Prelude.String where

open import Prelude.Base
open import Prelude.Instance

open import Data.Char as Char     public
  using (Char)
open import Data.String as String public
  hiding (_≟_; _++_; _<_; length; fromList; toList; _==_; concat; replicate)
open import Agda.Builtin.List as L

instance
  String-DecEq : DecEq String
  String-DecEq = record { _≟_ = String._≟_ }

  String-++-Monoid : Monoid String
  String-++-Monoid = record { ε = "" ; _∙_ = String._++_ }

  StringListLike : ListLike String
  StringListLike = record
    { base = Char
    ; singleton = String.fromList ∘ (_∷ L.[])
    ; empty   = ""
    ; _++_ = String._++_
    ; length = String.length
    ; fromList = String.fromList
    ; toList   = String.toList }
