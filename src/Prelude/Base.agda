{-# OPTIONS --safe --without-K  #-}

module Prelude.Base where

open import Agda.Primitive             public

open import Agda.Builtin.Unit          public
open import Agda.Builtin.Nat as Nat    public
  using (suc; zero; _+_) renaming (Nat to ℕ)
open import Agda.Builtin.Equality      public
open import Agda.Builtin.Sigma         public
  hiding (module Σ)
open import Agda.Builtin.List          public
open import Agda.Builtin.Bool          public
open import Agda.Builtin.String as S   public
open import Agda.Builtin.Char as C     public
  using (Char)
  renaming
  ( primIsLower    to isLower
  ; primIsDigit    to isDigit
  ; primIsAlpha    to isAlpha
  ; primIsSpace    to isSpace
  ; primIsAscii    to isAscii
  ; primIsLatin1   to isLatin1
  ; primIsPrint    to isPrint
  ; primIsHexDigit to isHexDigit
  ; primToUpper to toUpper
  ; primToLower to toLower
  )
  
open import Data.Empty                 public
open import Data.Sum as Sum            public
  hiding (map; map₁; map₂; swap)
open import Data.Maybe                 public
  using (Maybe; nothing; just)
import Data.List as L
  using (length)

open import Function                   public
open import Relation.Nullary           public
--open import Relation.Nullary.Decidable public
--  hiding (map)
  
variable
  ℓ ℓ′ ℓ₁ ℓ₂ ℓ₃ : Level
  A B C D : Set ℓ
  n m l   : ℕ

infixl 20 _!!_
_!!_ : List A → ℕ → Maybe A
[]       !! _       = nothing
(x ∷ xs) !! zero    = just x
(x ∷ xs) !! (suc n) = xs !! n

------------------------------------------------------------------------
-- Type classes: Enum, Eq, Ord, Show, 
record Eq (A : Set ℓ) : Set (lsuc ℓ) where
  infix 6 _==_ _/=_
  field
    _==_ : A → A → Bool
    
  _/=_ : A → A → Bool
  x /= y with x == y
  ... | true  = false
  ... | false = true
open Eq ⦃...⦄ public

instance
  StringE : Eq String
  StringE = record { _==_ = primStringEquality }

  NatE   : Eq ℕ
  NatE = record { _==_ = Nat._==_ }

record Enum (A : Set ℓ) : Set (lsuc ℓ) where
  field
    toEnum    : ℕ → A
    fromEnum  : A → ℕ
  toℕ   = fromEnum
  fromℕ = toEnum
open Enum ⦃...⦄ public

instance
  CharE : Enum Char
  CharE = record { toEnum = C.primNatToChar ; fromEnum = C.primCharToNat }

  ℕEnum : Enum ℕ
  ℕEnum = record { toEnum = id ; fromEnum = id }

record Ord (A : Set ℓ) : Set (lsuc ℓ) where
  infix 6 _<=_
  field
    _<=_ : A → A → Bool
    overlap ⦃ eq ⦄ : Eq A
open Ord ⦃...⦄ public

instance
  NatOrd : Ord ℕ
  NatOrd = record { _<=_ = leq }
    where
      leq : ℕ → ℕ → Bool
      leq x y with x Nat.< y | x Nat.== y
      ... | true  | _ = true
      ... | false | true  = true
      ... | false | false = false
  
record Show (A : Set ℓ) : Set (lsuc ℓ) where
  field
    show : A → String
open Show ⦃...⦄ public

instance
  charS   : Show Char
  charS   = record { show = primShowChar } 
  stringS : Show String
  stringS = record { show = primShowString }
------------------------------------------------------------------------
--

record Monoid (M : Set ℓ) (_∙_ : M → M → M) : Set (lsuc ℓ) where
  field
    ε   : M
open Monoid ⦃...⦄ public

instance
  ⊤-monoid : Monoid ⊤ (λ _ _ → tt)
  ⊤-monoid = record { ε = tt }
    
record ISequence {A : Set} (Seq : A → Set ℓ) : Set (lsuc ℓ) where
  infixr 5 _++_
  field
    zeroIdx  : A
    unitIdx  : A
    addIdx   : A → A → A 
    carrier  : Set ℓ
    [_]      : carrier → Seq unitIdx
    empty    : Seq zeroIdx
    _++_     : ∀ {n m} → Seq n → Seq m → Seq (addIdx n m)
    length   : ∀ {n} → Seq n → ℕ 
    fromList : List carrier → Σ A Seq
    toList   : Σ A Seq → List carrier
open ISequence ⦃...⦄ public
  hiding (zeroIdx; unitIdx; addIdx)

Sequence : Set ℓ → Set (lsuc ℓ)
Sequence Seq = ISequence {A = ⊤} λ _ → Seq

instance
  listSeq : Sequence (List A)
  listSeq {A = A} = record
    { carrier  = A
    ; [_]      = _∷ []
    ; empty    = []
    ; _++_     = append
    ; length   = L.length
    ; fromList = λ xs → _ , xs
    ; toList   = snd
    }
    where
      append : List A → List A → List A
      append []       ys = ys
      append (x ∷ xs) ys = x ∷ append xs ys
 
  stringSeq : Sequence String
  stringSeq = record
    { carrier = Char
    ; [_] = primStringFromList ∘ (_∷ [])
    ; empty = ""
    ; _++_ = primStringAppend
    ; length = λ xs → L.length (primStringToList xs)
    ; fromList = λ xs → (_ , primStringFromList xs)
    ; toList   = primStringToList ∘ snd
    }
------------------------------------------------------------------------
-- Propositional Partial order
record POrd (A : Set ℓ) : Set (lsuc ℓ) where
  infix 6 _≤_
  infix 6 _<_
  field
    _≤_ : A → A → Set
    _<_ : A → A → Set

  _≥_ = flip _≤_
  _>_ = flip _<_ 
open POrd ⦃...⦄ public

record DecEq (A : Set ℓ) : Set (lsuc ℓ) where
  field
    _≟_ : (x y : A) → Dec (x ≡ y)
    
--  instance
--    DecEq⇒Eq : Eq A
--    DecEq⇒Eq = record { _==_ = λ x y → ⌊ x ≟ y ⌋ }
open DecEq ⦃...⦄ public

record DecOrd (A : Set ℓ) : Set (lsuc ℓ) where
  field
    ⦃ pord ⦄ : POrd A
    _≤?_ : (x y : A) → Dec (x ≤ y)

  _≥?_ = flip _≤?_
open DecOrd ⦃...⦄ public

------------------------------------------------------------------------
-- Functor, Bifunctor, indexed applicative functor / monad

Fun : Setω
Fun = ∀ {ℓ} → Set ℓ → Set ℓ
    
IFun : Set ℓ′ → Setω
IFun I = ∀ {ℓ} → I → I → Set ℓ → Set ℓ

private
  variable
    F T   : Fun
    I     : Set ℓ
    IF IT : IFun I
    i j k : I

record Functor (T : Fun) : Setω where
  infixl 6 _<$>_
  field
    _<$>_ : (A → B) → T A → T B
  map = _<$>_
open Functor ⦃...⦄ public
  
record Bifunctor (T : ∀ {ℓ₁ ℓ₂} → Set ℓ₁ → Set ℓ₂ → Set (ℓ₁ ⊔ ℓ₂)) : Setω where
  field
    bimap : (A → C) → (B → D) → T A B → T C D

  map₁ : (A → C) → T A B → T C B
  map₁ f = bimap f id

  map₂ : (B → D) → T A B → T A D
  map₂ g = bimap id g 
open Bifunctor ⦃...⦄ public

record SymBifunctor (T : ∀ {ℓ₁ ℓ₂} → Set ℓ₁ → Set ℓ₂ → Set (ℓ₁ ⊔ ℓ₂)) : Setω where
  field
    swap : T A B → T B A 
    overlap ⦃ bifunc ⦄ : Bifunctor T
open SymBifunctor ⦃...⦄ public

instance
  +-Bifunc : Bifunctor _⊎_
  +-Bifunc = record { bimap = Sum.map }

  +-SymBifunc : SymBifunctor _⊎_
  +-SymBifunc = record { swap = Sum.swap }
  
record IApplicative (F : IFun I) : Setω where
  infixl 4 _<*>_
  field
    pure  : A → F i i A
    _<*>_ : F i j (A → B) → F j k A → F i k B
    instance overlap ⦃ functor ⦄ : Functor (F i j)
    
  zipWith : (A → B → C) → F i j A → F j k B → F i k C
  zipWith f x y = ⦇ f x y ⦈

  zip : F i j A → F j k B → F i k (Σ A λ _ → B)
  zip = zipWith _,_

  when : Bool → F i i ⊤ → F i i ⊤
  when false s = pure tt
  when true  s = s
open IApplicative ⦃...⦄ public

Applicative : Fun → Setω
Applicative F = IApplicative {I = ⊤} λ _ _ → F

record IMonad (M : IFun I) : Setω where
  infixl 1 _>>=_ _>>_ _>=>_
  infixr 1 _=<<_ _<=<_
  field
    return : A → M i i A
    _>>=_  : M i j A → (A → M j k B) → M i k B
  
  _=<<_ : (A → M j k B) → M i j A → M i k B
  f =<< c = c >>= f
  
  _>>_ : M i j A → M j k B → M i k B
  ma >> mb = ma >>= λ _ → mb

  _>=>_ : (A → M i j B) → (B → M j k C) → (A → M i k C)
  f >=> g = _=<<_ g ∘ f

  _<=<_ : (B → M j k C) → (A → M i j B) → (A → M i k C)
  g <=< f = f >=> g

  ap : M i j (A → B) → M j k A → M _ _ B
  ap mf ma = mf >>= λ f → ma >>= return ∘ f

  join : M i j (M j k A) → M i k A
  join ma = ma >>= id

open IMonad ⦃...⦄ public

monad⇒applicative : {M : IFun I} ⦃ _ : IMonad M ⦄ → IApplicative M
monad⇒applicative = record
  { pure    = return
  ; _<*>_   = ap
  ; functor = record { _<$>_ = λ f ma → ma >>= return ∘ f }
  }

Monad : Fun → Setω
Monad M = IMonad {I = ⊤} λ _ _ → M

instance
  E+Monad : {E : Set} → Monad (E ⊎_)
  E+Monad = record { return = inj₂ ; _>>=_ = λ { (inj₁ e) f → inj₁ e ; (inj₂ a) f → f a } }
  
record IMAlternative (F : C → IFun I) : Setω where
  infixr 3 _<|>_
  field
    _∙_ : C → C → C
    ⦃ applicative ⦄ : {c : C} → IApplicative (F c)
    ⦃ monoid ⦄      : Monoid C _∙_
    azero : F ε i j A
    _<|>_ : ∀ {x y} → F x i j A → F y i j A → F (x ∙ y) i j A
    
  guard : Bool → F ε i i ⊤
  guard true  = pure tt
  guard false = azero
open IMAlternative ⦃...⦄ public

MAlternative : (C → Fun) → Setω
MAlternative F = IMAlternative {I = ⊤} λ m _ _ → F m

IAlternative : IFun I → Setω
IAlternative F = IMAlternative {C = ⊤} λ _ → F

Alternative : Fun → Setω
Alternative F = IAlternative {I = ⊤} λ _ _ → F

mkAlternative : ⦃ _ : Applicative F ⦄
  → (∀ {ℓ} {A : Set ℓ} → F A) → (∀ {ℓ} {A : Set ℓ} → F A → F A → F A) → Alternative F
mkAlternative z f = record { _∙_ = λ _ _ → tt ; azero = z ; _<|>_ = f }

record IMonadPlus (M : IFun I) : Setω where
  field
    ⦃ alternative ⦄ : IAlternative M
    ⦃ monad       ⦄ : IMonad M
open IMonadPlus ⦃...⦄ public

MonadPlus : Fun → Setω
MonadPlus M = IMonadPlus {I = ⊤} λ _ _ → M

record IMonadError (E : Set) (M : IFun I) : Setω where
  infixl 4 try_catch_
  infix  4 try_finally_
  infix  5 _finally_
  field
    throw : E → M i j A
    try_catch_ : M i j A → (E → M j k A) → M i k A
    ⦃ monad ⦄ : IMonad M
    
  _finally_ : M i j A → M j k A → M i k A
  ma finally mb = try ma catch (λ _ → mb)

  try_finally_ : M i j A → M j k A → M i k A
  try ma finally mb = ma finally mb
open IMonadError ⦃...⦄ public

MonadError : (E : Set) → (M : Fun) → Setω
MonadError E M = IMonadError {I = ⊤} E λ _ _ → M

instance
  MonadExcept : {E : Set} → MonadError E (E ⊎_)
  MonadExcept = record
    { throw      = inj₁
    ; try_catch_ = λ
      { (inj₁ e) f → f e
      ; (inj₂ a) _ → inj₂ a }
    }
------------------------------------------------------------------------
-- Iterator idioms  

record Foldable (T : Fun) : Setω where
  field
    foldr : (A → B → B) → B → T A → B 

  foldMap : (_∙_ : C → C → C) ⦃ _ : Monoid C _∙_ ⦄ → (A → C) → T A → C
  foldMap _∙_ f = foldr (_∙_ ∘ f) ε

  asum : ⦃ _ : Alternative F ⦄ → T (F A) -> F A
  asum = foldr _<|>_ azero
open Foldable ⦃...⦄ public

record Traversable (T : Fun) : Setω where
  field
    traverse : ⦃ _ : Applicative F ⦄ → (A → F B) → T A → F (T B)
    ⦃ functor  ⦄ : Functor T
    ⦃ foldable ⦄ : Foldable T

  sequence : ⦃ _ : Applicative F ⦄ → T $ F A → F $ T A
  sequence = traverse id

  for : ⦃ _ : Applicative F ⦄ → T A → (A → F B) → F $ T B
  for = flip traverse
open Traversable ⦃...⦄ public
