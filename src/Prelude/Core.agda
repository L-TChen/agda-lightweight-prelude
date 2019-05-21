{-# OPTIONS --safe --without-K  #-}

module Prelude.Core where

open import Agda.Primitive             public
open import Agda.Builtin.Equality      public
open import Agda.Builtin.Strict
     renaming ( primForce to force
              ; primForceLemma to force-≡) public
open import Agda.Builtin.Unit          public
open import Agda.Builtin.Nat as Nat    public
  using (suc; zero; _+_) renaming (Nat to ℕ)
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
open import Agda.Builtin.Float as F    public
  using (Float)
open import Agda.Builtin.Word  as W    public
  using (Word64)
  
variable
  ℓ ℓ′ ℓ₁ ℓ₂ ℓ₃ : Level
  A B C D E : Set ℓ
  n m l   : ℕ

------------------------------------------------------------------------
-- Function combinators 

force′ : A → (A → B) → B
force′ = force

force′-≡ : (a : A) (f : A → B) → force′ a f ≡ f a
force′-≡ = force-≡

seq : A → B → B
seq a b = force a (λ _ → b)

seq-≡ : (a : A) (b : B) → seq a b ≡ b
seq-≡ a b = force-≡ a (λ _ → b)

------------------------------------------------------------------------
-- Some simple functions

id : A → A
id x = x

const : A → B → A
const x = λ _ → x

------------------------------------------------------------------------
-- Operations on dependent functions

-- These are functions whose output has a type that depends on the
-- value of the input to the function.

infixr 9 _∘_
infixl 8 _ˢ_
infixl 0 _|>_
infix  0 case_return_of_
infixr -1 _$_ _$!_

-- Composition

_∘_ : {A : Set ℓ₁} {B : A → Set ℓ₂} {C : {x : A} → B x → Set ℓ₃} →
      (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
      ((x : A) → C (g x))
f ∘ g = λ x → f (g x)

-- Flipping order of arguments

flip : ∀ {B : Set ℓ₂} {C : A → B → Set ℓ₃} →
       ((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)
flip f = λ y x → f x y

-- Application - note that _$_ is right associative, as in Haskell.
-- If you want a left associative infix application operator, use
-- Category.Functor._<$>_ from Category.Monad.Identity.IdentityMonad.

_$_ : ∀ {B : A → Set ℓ₂} →
      ((x : A) → B x) → ((x : A) → B x)
f $ x = f x

-- Strict (call-by-value) application

_$!_ : ∀ {A : Set ℓ₂} {B : A → Set ℓ₃} →
       ((x : A) → B x) → ((x : A) → B x)
_$!_ = flip force

-- Flipped application (aka pipe-forward)

_|>_ : ∀ {A : Set ℓ₁} {B : A → Set ℓ₂} →
       (a : A) → (∀ a → B a) → B a
_|>_ = flip _$_

-- The S combinator - written infix as in Conor McBride's paper
-- "Outrageous but Meaningful Coincidences: Dependent type-safe syntax
-- and evaluation".

_ˢ_ : ∀ {A : Set ℓ₁} {B : A → Set ℓ₂} {C : (x : A) → B x → Set ℓ₃} →
      ((x : A) (y : B x) → C x y) →
      (g : (x : A) → B x) →
      ((x : A) → C x (g x))
f ˢ g = λ x → f x (g x)

-- Case expressions (to be used with pattern-matching lambdas, see
-- README.Case).

case_return_of_ : ∀ {A : Set ℓ₁} (x : A) (B : A → Set ℓ₂) →
                  ((x : A) → B x) → B x
case x return B of f = f x

------------------------------------------------------------------------
-- Non-dependent versions of dependent operations

-- Any of the above operations for dependent functions will also work
-- for non-dependent functions but sometimes Agda has difficulty
-- inferring the non-dependency. Primed (′ = \prime) versions of the
-- operations are therefore provided below that sometimes have better
-- inference properties.

infixr 9 _∘′_
infixl 0 _|>′_
infix  0 case_of_
infixr -1 _$′_ _$!′_

-- Composition

_∘′_ : (B → C) → (A → B) → (A → C)
f ∘′ g = _∘_ f g

-- Application

_$′_ : (A → B) → (A → B)
_$′_ = _$_

-- Strict (call-by-value) application

_$!′_ : (A → B) → (A → B)
_$!′_ = _$!_

-- Flipped application (aka pipe-forward)

_|>′_ : A → (A → B) → B
_|>′_ = _|>_

-- Case expressions (to be used with pattern-matching lambdas, see
-- README.Case).

case_of_ : A → (A → B) → B
case x of f = case x return _ of f

------------------------------------------------------------------------
-- Operations that are only defined for non-dependent functions

infixr 0 _-[_]-_
infixl 1 _on_
infixl 1 _⟨_⟩_
infixl 0 _∋_

-- Binary application

_⟨_⟩_ : A → (A → B → C) → B → C
x ⟨ f ⟩ y = f x y

-- Composition of a binary function with a unary function

_on_ : (B → B → C) → (A → B) → (A → A → C)
_*_ on f = λ x y → f x * f y

-- Composition of three binary functions

_-[_]-_ : (A → B → C) → (C → D → E) → (A → B → D) → (A → B → E)
f -[ _*_ ]- g = λ x y → f x y * g x y

-- In Agda you cannot annotate every subexpression with a type
-- signature. This function can be used instead.

_∋_ : (A : Set ℓ) → A → A
A ∋ x = x

-- Conversely it is sometimes useful to be able to extract the
-- type of a given expression.

typeOf : A → Set _
typeOf {A = A} _ = A
------------------------------------------------------------------------ Common types 

data ⊥ : Set where

⊥-elim : ⊥ → A
⊥-elim ()

infixr 4 _,′_
infixr 2 _×_

_×_ : ∀ (A : Set ℓ₁) (B : Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
A × B = Σ A λ _ → B

_,′_ : A → B → A × B
_,′_ = _,_

------------------------------------------------------------------------
-- Basic Bool functions

not : Bool → Bool
not false = true
not true  = false

infixr 6 _&&_
infixr 6 _||_
infix  0 if_then_else_
_&&_ : Bool → Bool → Bool
_&&_ false false = false
_&&_ false true  = false
_&&_ true false  = false
_&&_ true true   = true

_||_ : Bool → Bool → Bool
_||_ false false = false
_||_ false true  = true
_||_ true false  = true
_||_ true true   = true

if_then_else_ : Bool → A → A → A
if false then a else b = b
if true  then a else b = a
------------------------------------------------------------------------
-- Basic list functions.
-- All of them should have been supplied by agda-stdlib, so keep them private.

private
  module L where
    foldr : (A → B → B) → B → List A → B
    foldr f z []       = z
    foldr f z (x ∷ xs) = f x (foldr f z xs)
    
    length : List A → ℕ
    length = foldr (λ _ → suc) 0

    fmap : (A → B) → List A → List B
    fmap f = foldr (λ x → f x ∷_) []

    _++_ : List A → List A → List A
    []       ++ ys = ys
    (x ∷ xs) ++ ys = x ∷ xs ++ ys
    
    concat : List (List A) → List A
    concat = foldr _++_ []

    concatMap : (A → List B) → List A → List B
    concatMap f = concat ∘ fmap f

------------------------------------------------------------------------
-- Type classes: Enum, Eq, Ord, Show, 
record Eq (A : Set ℓ) : Set (lsuc ℓ) where
  infix 8 _==_ _/=_
  field
    _==_ : A → A → Bool
    
  _/=_ : A → A → Bool
  x /= y = not $ x == y
open Eq ⦃...⦄ public

instance
  NatE   : Eq ℕ
  NatE = record { _==_ = Nat._==_ }
  
  CharEq   : Eq Char
  _==_ ⦃ CharEq ⦄ = C.primCharEquality
  
  StringE : Eq String
  _==_ ⦃ StringE ⦄ = primStringEquality

  FloatE : Eq Float
  _==_ ⦃ FloatE ⦄ = F.primFloatEquality

  WordEq : Eq Word64
  _==_ ⦃ WordEq ⦄ x y = W.primWord64ToNat x == W.primWord64ToNat y

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
  infix 5 _<=_
  infix 5 _<?_
  field
    _<=_ : A → A → Bool
    _<?_ : A → A → Bool 
    overlap ⦃ eq ⦄ : Eq A
open Ord ⦃...⦄ public

leqOrd : ⦃ _ : Eq A ⦄ → (A → A → Bool) → Ord A
_<=_ ⦃ leqOrd _<=_ ⦄ = _<=_
_<?_ ⦃ leqOrd _<=_ ⦄ x y = (x <= y) && (x /= y) 

lessOrd : ⦃ _ : Eq A ⦄ → (A → A → Bool) → Ord A
_<=_ ⦃ lessOrd _<?_ ⦄ x y = x <? y || (x == y)
_<?_ ⦃ lessOrd _<?_ ⦄ = _<?_

instance
  NatOrd : Ord ℕ
  NatOrd = lessOrd Nat._<_
  
record Show (A : Set ℓ) : Set (lsuc ℓ) where
  field
    show : A → String
open Show ⦃...⦄ public

instance
  charS   : Show Char
  show ⦃ charS ⦄ = primShowChar
  stringS : Show String
  show ⦃ stringS ⦄ = primShowString

  floatS : Show Float
  show ⦃ floatS ⦄ = F.primShowFloat

------------------------------------------------------------------------
--

record Monoid (M : Set ℓ) (_∙_ : M → M → M) : Set (lsuc ℓ) where
  field
    ε   : M
open Monoid ⦃...⦄ public

instance
  ⊤-monoid : Monoid ⊤ (λ _ _ → tt)
  ε ⦃ ⊤-monoid ⦄ = tt

  &&-monoid : Monoid Bool _&&_
  ε ⦃ &&-monoid ⦄ = true

  ||-monoid : Monoid Bool _||_
  ε ⦃ ||-monoid ⦄ = false
    
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
    ; _++_     = L._++_
    ; length   = L.length
    ; fromList = λ xs → _ , xs
    ; toList   = snd
    }
    
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

instance
  listFunc : Functor List
  _<$>_ ⦃ listFunc ⦄ = L.fmap
  
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

record IApplicative (F : IFun I) : Setω where
  infixl 4 _<*>_
  field
    pure  : A → F i i A
    _<*>_ : F i j (A → B) → F j k A → F i k B
    overlap ⦃ functor ⦄ : Functor (F i j)
    
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
  infixl 1 _>>=_ _>>_ _>=>_ _>>_
  infixr 1 _=<<_ _<=<_
  field
    return : A → M i i A
    _>>=_  : M i j A → (A → M j k B) → M i k B

  _=<<_ : (A → M j k B) → M i j A → M i k B
  f =<< c = c >>= f
  
  _>>_ : M i j A → M j k B → M i k B
  ma >> mb = ma >>= λ _ → mb

  _<<_ : M j k B → M i j A → M i k B
  mb << ma = ma >> mb
  
  _>=>_ : (A → M i j B) → (B → M j k C) → (A → M i k C)
  f >=> g = _=<<_ g ∘ f

  _<=<_ : (B → M j k C) → (A → M i j B) → (A → M i k C)
  g <=< f = f >=> g

  infixr 0 caseM_of_
  caseM_of_ = _>>=_
  
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
  MonadList : Monad List
  return ⦃ MonadList ⦄      = _∷ []
  _>>=_  ⦃ MonadList ⦄ xs f = L.concatMap f xs

  ApplicativeList : Applicative List
  ApplicativeList = monad⇒applicative 

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
  infixl 6 try_catch_
  infix  6 try_finally_
  infix  7 _finally_
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

record IMonadFail (M : IFun I) : Setω where
  field
    ⦃ monad ⦄ : IMonad M
    fail      : {A : Set ℓ} → String → M i j A 
open IMonadFail ⦃...⦄ public

MonadFail : (M : Fun) → Setω
MonadFail M = IMonadFail {I = ⊤} λ _ _ → M
------------------------------------------------------------------------
-- Iterator idioms  

record Foldable (T : Fun) : Setω where
  field
    foldr : (A → B → B) → B → T A → B 

  foldMap : (_∙_ : C → C → C) ⦃ _ : Monoid C _∙_ ⦄ → (A → C) → T A → C
  foldMap _∙_ f = foldr (_∙_ ∘ f) ε

  asum : ⦃ _ : Alternative F ⦄ → T (F A) -> F A
  asum = foldr _<|>_ azero

  and or : T Bool → Bool
  and = foldMap _&&_ id
  or  = foldMap _||_ id

  all any : (A → Bool) → T A → Bool
  all f = foldMap _&&_ f
  any f = foldMap _||_ f
open Foldable ⦃...⦄ public

instance
  ListFoldable : Foldable List
  foldr ⦃ ListFoldable ⦄ = L.foldr

record Traversable (T : Fun) : Setω where
  field
    traverse : ⦃ _ : Applicative F ⦄ → (A → F B) → T A → F (T B)
    ⦃ functor  ⦄ : Functor T

  sequence : ⦃ _ : Applicative F ⦄ → T $ F A → F $ T A
  sequence = traverse id

  for : ⦃ _ : Applicative F ⦄ → T A → (A → F B) → F $ T B
  for = flip traverse
open Traversable ⦃...⦄ public

instance
  ListTraversable : Traversable List
  traverse ⦃ ListTraversable ⦄ f = L.foldr (λ x ys → ⦇ _∷_ (f x) ys ⦈) (pure [])
