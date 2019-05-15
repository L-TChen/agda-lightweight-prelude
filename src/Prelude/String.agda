module Prelude.String where

open import Prelude.Base
open import Prelude.Instance

open import Data.Char   as Char     public
  using (Char)
open import Data.String as String public
  hiding (_≟_; _++_; _<_; _<?_; length; fromList; toList; _==_; concat; replicate; show)
import Data.List as L

instance
  StringShow : Show String
  StringShow = record { show = String.show }

  String-DecEq : DecEq String
  String-DecEq = record { _≟_ = String._≟_ }

  StringListLike : ListLike (λ _ → String)
  StringListLike = record
    { base = Char
    ; singleton = String.fromList ∘ (_∷ L.[])
    ; empty   = ""
    ; _++_ = String._++_
    ; length = String.length
    ; fromList = λ xs → L.length xs , primStringFromList xs -- String.fromList
    ; toList   = λ { (_ , xs) → String.toList xs} -- String.toList
    }
