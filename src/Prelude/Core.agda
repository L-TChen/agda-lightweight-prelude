{-# OPTIONS --safe --without-K  #-}

module Prelude.Core where

open import Agda.Primitive             public
open import Agda.Builtin.Equality      public
open import Agda.Builtin.Strict
     renaming ( primForce to force
              ; primForceLemma to force-≡) public
open import Agda.Builtin.Unit          public
open import Agda.Builtin.Nat as Nat    public
  using (suc; zero; _+_; _*_)
  renaming (Nat to ℕ; _-_ to _∸_)
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
  A B C D E     : Set ℓ
  n m l         : ℕ

------------------------------------------------------------------------
-- Function combinators

force′ : A → (A → B) → B
force′ = force
{-
force′-≡ : (a : A) (f : A → B) → force′ a f ≡ f a
force′-≡ = force-≡
-}
seq : A → B → B
seq a b = force a (λ _ → b)
{-
seq-≡ : (a : A) (b : B) → seq a b ≡ b
seq-≡ a b = force-≡ a (λ _ → b)
-}
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

_∘_ : {B : A → Set ℓ₂} {C : {x : A} → B x → Set ℓ₃} →
      (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
      ((x : A) → C (g x))
f ∘ g = λ x → f (g x)

-- Flipping order of arguments

flip : {C : A → B → Set ℓ} →
       ((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)
flip f = λ y x → f x y

-- Application - note that _$_ is right associative, as in Haskell.
-- If you want a left associative infix application operator, use
-- Category.Functor._<$>_ from Category.Monad.Identity.IdentityMonad.

_$_ : ∀ {B : A → Set ℓ} →
      ((x : A) → B x) → ((x : A) → B x)
f $ x = f x

-- Strict (call-by-value) application

_$!_ : ∀ {B : A → Set ℓ} →
       ((x : A) → B x) → ((x : A) → B x)
_$!_ = flip force

-- Flipped application (aka pipe-forward)

_|>_ : ∀ {B : A → Set ℓ} →
       (a : A) → (∀ a → B a) → B a
_|>_ = flip _$_

-- The S combinator - written infix as in Conor McBride's paper
-- "Outrageous but Meaningful Coincidences: Dependent type-safe syntax
-- and evaluation".

_ˢ_ : ∀ {B : A → Set ℓ₂} {C : (x : A) → B x → Set ℓ₃} →
      ((x : A) (y : B x) → C x y) →
      (g : (x : A) → B x) →
      ((x : A) → C x (g x))
f ˢ g = λ x → f x (g x)

-- Case expressions (to be used with pattern-matching lambdas, see
-- README.Case).

case_return_of_ : (x : A) (B : A → Set ℓ₂) → ((x : A) → B x) → B x
case x return B of f = f x

------------------------------------------------------------------------
-- Non-dependent versions of dependent operations

-- Any of the above operations for dependent functions will also work
-- for non-dependent functions but sometimes Agda has difficulty
-- inferring the non-dependency. Primed (′ = \prime) versions of the
-- operations are therefore provided below that sometimes have better
-- inference properties.
{-
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
-}
-- Case expressions (to be used with pattern-matching lambdas, see
-- README.Case).

case_of_ : A → (A → B) → B
case x of f = case x return _ of f

-- Curry and uncurry
curry : {B : A → Set ℓ₁} {C : Σ A B → Set ℓ₂} →
        ((p : Σ A B) → C p) →
        ((x : A) → (y : B x) → C (x , y))
curry f x y = f (x , y)

uncurry : {B : A → Set ℓ₁} {C : Σ A B → Set ℓ₂} →
          ((x : A) → (y : B x) → C (x , y)) →
          ((p : Σ A B) → C p)
uncurry f (x , y) = f x y

------------------------------------------------------------------------
-- Operations that are only defined for non-dependent functions

infixr 0 _-[_]-_
infixl 1 _on_
infixl 1 _⟨_⟩_

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
{-
typeOf : A → Set _
typeOf {A = A} _ = A
-}

------------------------------------------------------------------------
-- Common types

data ⊥ : Set where

⊥-elim : ⊥ → A
⊥-elim ()

infixr 4 _,′_
infixr 2 _×_

_×_ : ∀ (A : Set ℓ₁) (B : Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
A × B = Σ A λ _ → B

_,′_ : A → B → A × B
_,′_ = _,_

data Maybe (A : Set ℓ) : Set ℓ where
  just    : (x : A) → Maybe A
  nothing : Maybe A

infixr 1 _⊎_

data _⊎_ (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  inj₁ : (x : A) → A ⊎ B
  inj₂ : (y : B) → A ⊎ B

infix 4 _≢_
_≢_ : A → A → Set _
x ≢ y = x ≡ y → ⊥

cong : ∀ (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

sym : {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl eq = eq

subst : {x y : A} → (P : A → Set ℓ) → x ≡ y → P x → P y
subst P refl p = p

module ≡-Reasoning {A : Set ℓ} where
  infix  3 _∎
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_ _≡˘⟨_⟩_
  infix  1 begin_

  begin_ : {x y : A} → x ≡ y → x ≡ y
  begin_ x≡y = x≡y

  _≡⟨⟩_ : (x {y} : A) → x ≡ y → x ≡ y
  _ ≡⟨⟩ x≡y = x≡y

  _≡⟨_⟩_ : (x {y z} : A) → x ≡ y → y ≡ z → x ≡ z
  _ ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

  _≡˘⟨_⟩_ : (x {y z} : A) → y ≡ x → y ≡ z → x ≡ z
  _ ≡˘⟨ y≡x ⟩ y≡z = trans (sym y≡x) y≡z

  _∎ : ∀ (x : A) → x ≡ x
  _∎ _ = refl
---------------------------------------------------------------------
-- Bool functions

infixr 6 _&&_
infixr 5 _||_ _xor_
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

not : Bool → Bool
not false = true
not true  = false

_xor_ : Bool → Bool → Bool
true  xor b = not b
false xor b = b

if_then_else_ : Bool → A → A → A
if false then a else b = b
if true  then a else b = a
------------------------------------------------------------------------
-- Basic nat functions.

max min : ℕ → ℕ → ℕ
max zero zero       = zero
max zero m@(suc _)  = m
max n@(suc _) zero  = n
max (suc n) (suc m) = suc (max n m)

min zero zero       = zero
min zero m@(suc _)  = m
min n@(suc _) zero  = n
min (suc n) (suc m) = suc (min n m)

------------------------------------------------------------------------
-- Basic list functions.

module L where
  foldr : (A → B → B) → B → List A → B
  foldr f z []       = z
  foldr f z (x ∷ xs) = f x (foldr f z xs)

  length : List A → ℕ
  length = foldr (λ _ → suc) 0

  map : (A → B) → List A → List B
  map f = foldr (λ x → f x ∷_) []

  _++_ : List A → List A → List A
  _++_ xs ys = foldr _∷_ ys xs

concat : List (List A) → List A
concat = L.foldr L._++_ []

concatMap : (A → List B) → List A → List B
concatMap f = concat ∘ L.map f

take : ℕ → List A → List A
take zero    xs       = []
take (suc n) []       = []
take (suc n) (x ∷ xs) = x ∷ take n xs

drop : ℕ → List A → List A
drop zero    xs       = xs
drop (suc n) []       = []
drop (suc n) (x ∷ xs) = drop n xs

revapp : List A → List A → List A
revapp [] ys       = ys
revapp (x ∷ xs) ys = revapp xs (x ∷ ys)

reverse : List A → List A
reverse xs = revapp xs []

infixl 20 _!!_

_!!_ : List A → ℕ → Maybe A
[]       !! _       = nothing
(x ∷ xs) !! zero    = just x
(x ∷ xs) !! (suc n) = xs !! n

------------------------------------------------------------------------
-- Vectors
infixr 5 _∷_

data Vec (A : Set ℓ) : ℕ → Set ℓ where
  []  : Vec A zero
  _∷_ : (x : A) (xs : Vec A n) → Vec A (suc n)

module V where
  map : (A → B) → Vec A n → Vec B n
  map f []       = []
  map f (x ∷ xs) = f x ∷ map f xs

  tail : Vec A (1 + n) → Vec A n
  tail (x ∷ xs) = xs

  replicate : A → Vec A n
  replicate {n = zero}  x = []
  replicate {n = suc n} x = x ∷ replicate x

  _++_ : Vec A n → Vec A m → Vec A (n + m)
  []       ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  fromList : (xs : List A) → Vec A (L.length xs)
  fromList []       = []
  fromList (x ∷ xs) = x ∷ fromList xs

  toList : Vec A n → List A
  toList []       = []
  toList (x ∷ xs) = x ∷ toList xs

diag : Vec (Vec A n) n -> Vec A n
diag []               = []
diag ((x ∷ xs) ∷ xss) = x ∷ diag (V.map V.tail xss)
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
  _==_ ⦃ NatE ⦄    = Nat._==_
  CharEq   : Eq Char
  _==_ ⦃ CharEq ⦄  = C.primCharEquality
  StringE : Eq String
  _==_ ⦃ StringE ⦄ = primStringEquality
  FloatE : Eq Float
  _==_ ⦃ FloatE ⦄  = F.primFloatEquality
  WordEq : Eq Word64
  _==_ ⦃ WordEq ⦄ x y = W.primWord64ToNat x == W.primWord64ToNat y
  BoolEq : Eq Bool
  _==_ ⦃ BoolEq ⦄ false false = true
  _==_ ⦃ BoolEq ⦄ true true   = true
  _==_ ⦃ BoolEq ⦄ _ _         = false
  ⊤-Eq : Eq ⊤
  _==_ ⦃ ⊤-Eq ⦄ _ _ = true
  MaybeEq : ⦃ _ : Eq A ⦄ → Eq (Maybe A)
  _==_ ⦃ MaybeEq ⦄ (just x) (just y) = x == y
  _==_ ⦃ MaybeEq ⦄ (just x) nothing  = false
  _==_ ⦃ MaybeEq ⦄ nothing (just y)  = false
  _==_ ⦃ MaybeEq ⦄ nothing nothing   = true

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

  ⊤-Ord : Ord ⊤
  ⊤-Ord = leqOrd λ _ _ → true

record Show (A : Set ℓ) : Set (lsuc ℓ) where
  field
    show : A → String
open Show ⦃...⦄ public

instance
  charS   : Show Char
  show ⦃ charS ⦄ = primShowChar
  stringS : Show String
  show ⦃ stringS ⦄ = primShowString
  floatS  : Show Float
  show ⦃ floatS ⦄ = F.primShowFloat
  natS    : Show ℕ
  show ⦃ natS ⦄  = S.primShowNat
  wordS   : Show Word64
  show ⦃ wordS ⦄ = S.primShowNat ∘ W.primWord64ToNat
  boolS : Show Bool
  show ⦃ boolS ⦄ false = "false"
  show ⦃ boolS ⦄ true  = "true"
  ListShow : ⦃ _ : Show A ⦄ → Show (List A)
  show ⦃ ListShow ⦄ =
    L.foldr (λ x xs → primStringAppend (show x) (primStringAppend " ∷ " xs)) "[]"

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

  ℕ-+-monoid : Monoid ℕ _+_
  ε ⦃ ℕ-+-monoid ⦄ = 0

record IxSequence {I : Set} (Seq : I → Set ℓ) : Set (lsuc ℓ) where
  infixr 5 _++_
  field
    zeroIdx  : I
    unitIdx  : I
    addIdx   : I → I → I
    carrier  : Set ℓ
    [_]      : carrier → Seq unitIdx
    emptySeq : Seq zeroIdx
    _++_     : ∀ {n m} → Seq n → Seq m → Seq (addIdx n m)
    length   : ∀ {n}   → Seq n → ℕ
    fromList : List carrier → Σ I Seq
    toList   : Σ I Seq → List carrier
open IxSequence ⦃...⦄ public
  hiding (zeroIdx; unitIdx; addIdx)

Sequence : Set ℓ → Set (lsuc ℓ)
Sequence Seq = IxSequence {I = ⊤} λ _ → Seq

instance
  listSeq : Sequence (List A)
  listSeq {A = A} = record
    { carrier  = A
    ; [_]      = _∷ []
    ; emptySeq = []
    ; _++_     = L._++_
    ; length   = L.length
    ; fromList = λ xs → _ , xs
    ; toList   = snd
    }

  stringSeq : Sequence String
  stringSeq = record
    { carrier  = Char
    ; [_]      = primStringFromList ∘ (_∷ [])
    ; emptySeq = ""
    ; _++_     = primStringAppend
    ; length   = λ xs → L.length (primStringToList xs)
    ; fromList = λ xs → (_ , primStringFromList xs)
    ; toList   = primStringToList ∘ snd
    }

  VecSequence : IxSequence (Vec A)
  VecSequence {A = A} = record
    { zeroIdx  = 0
    ; unitIdx  = 1
    ; addIdx   =  _+_
    ; carrier  = A
    ; [_]      = _∷ []
    ; emptySeq = []
    ; _++_     = V._++_
    ; length   = λ {n} xs → n
    ; fromList = λ xs → length xs , V.fromList xs
    ; toList   = λ { (n , xs) → V.toList xs }
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

IxFun : Set ℓ → Setω
IxFun I = ∀ {ℓ} → I → I → Set ℓ → Set ℓ

private
  variable
    F T M : Fun
    I     : Set ℓ
    IxF IxT IxM : IxFun I
    i j k : I

record Functor (T : Fun) : Setω where
  infixl 6 _<$>_
  field
    _<$>_ : (A → B) → T A → T B
  map = _<$>_
open Functor ⦃...⦄ public

{-# DISPLAY Functor._<$>_ = _<$>_ #-}

instance
  listFunc : Functor List
  _<$>_ ⦃ listFunc ⦄ = L.map

  maybeFunc : Functor Maybe
  _<$>_ ⦃ maybeFunc ⦄ f (just x) = just (f x)
  _<$>_ ⦃ maybeFunc ⦄ f nothing  = nothing

  VecFunctor : Functor (λ A → Vec A n)
  _<$>_ ⦃ VecFunctor ⦄ f []       = []
  _<$>_ ⦃ VecFunctor ⦄ f (x ∷ xs) = f x ∷ f <$> xs

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
    ⦃ bifunc ⦄ : Bifunctor T
open SymBifunctor ⦃...⦄ public

instance
  +-Bifunc : Bifunctor _⊎_
  bimap ⦃ +-Bifunc ⦄ f _ (inj₁ x) = inj₁ (f x)
  bimap ⦃ +-Bifunc ⦄ _ g (inj₂ y) = inj₂ (g y)

  +-SymBifunc : SymBifunctor _⊎_
  swap ⦃ +-SymBifunc ⦄ (inj₁ x) = inj₂ x
  swap ⦃ +-SymBifunc ⦄ (inj₂ y) = inj₁ y

  ×-Bifunc : Bifunctor _×_
  bimap ⦃ ×-Bifunc ⦄ f g (x , y) = f x , g y

  ×-SymBifunc : SymBifunctor _×_
  swap ⦃ ×-SymBifunc ⦄ (x , y) = y , x

record IxApplicative (F : IxFun I) : Setω where
  infixl 4 _<*>_ _*>_ _<*_
  field
    pure   : A → F i i A
    _<*>_  : F i j (A → B) → F j k A → F i k B

  Applicative⇒Functor : Functor (F i j)
  _<$>_ ⦃ Applicative⇒Functor ⦄ f ma = pure f <*> ma

  _*>_ : F i j A → F j k B → F i k B
  fa *> fb = ⦇ (flip const) fa fb ⦈

  _<*_ : F i j A → F j k B → F i k A
  fa <* fb = ⦇ const fa fb ⦈

  zipWith : (A → B → C) → F i j A → F j k B → F i k C
  zipWith f x y = ⦇ f x y ⦈

  zip : F i j A → F j k B → F i k (A × B)
  zip = zipWith _,_

  when : Bool → F i i ⊤ → F i i ⊤
  when false s = pure tt
  when true  s = s
open IxApplicative ⦃...⦄ public

{-# DISPLAY IxApplicative.pure  = pure  #-}
{-# DISPLAY IxApplicative._<*>_ = _<*>_ #-}
{-# DISPLAY IxApplicative._<*_  = _<*_ #-}
{-# DISPLAY IxApplicative._*>_  = _*>_ #-}
{-# DISPLAY IxApplicative.when  = when #-}

Applicative : Fun → Setω
Applicative F = IxApplicative {I = ⊤} λ _ _ → F

filterA : ⦃ _ : Applicative F ⦄ → (A → F Bool) → List A → F (List A)
filterA p []               = pure []
filterA {F = F} p (x ∷ xs) = let ys = filterA p xs in
  ⦇ if p x then map (x ∷_) ys else ys ⦈
  where
    instance _ = Applicative⇒Functor {F = λ _ _ → F}

record IxMAlternative (F : C → IxFun I) : Setω where
  infixr 3 _<|>_
  field
    _∙_ : C → C → C
    ⦃ applicative ⦄ : {c : C} → IxApplicative (F c)
    ⦃ monoid ⦄      : Monoid C _∙_
    empty : F ε i j A
    _<|>_ : ∀ {x y} → F x i j A → F y i j A → F (x ∙ y) i j A

  guard : Bool → F ε i j A → F ε i j A
  guard true  x = x
  guard false _ = empty
open IxMAlternative ⦃...⦄ public

{-# DISPLAY IxMAlternative._<|>_ = _<|>_ #-}
{-# DISPLAY IxMAlternative.empty = empty #-}
{-# DISPLAY IxMAlternative.guard = guard #-}

MAlternative : (C → Fun) → Setω
MAlternative F = IxMAlternative {I = ⊤} λ m _ _ → F m

IxAlternative : IxFun I → Setω
IxAlternative F = IxMAlternative {C = ⊤} λ _ → F

Alternative : Fun → Setω
Alternative F = MAlternative {C = ⊤} λ _ → F

mkAlternative : ⦃ _ : Applicative F ⦄
  → (∀ {ℓ} {A : Set ℓ} → F A) → (∀ {ℓ} {A : Set ℓ} → F A → F A → F A) → Alternative F
mkAlternative z f = record { _∙_ = λ _ _ → tt ; empty = z ; _<|>_ = f }

record IxMonad (M : IxFun I) : Setω where
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

  ap : M i j (A → B) → M j k A → M i k B
  ap mf ma = mf >>= λ f → ma >>= λ a → return (f a)

  join : M i j (M j k A) → M i k A
  join ma = ma >>= id

  bind : M i j A → (A → M j k B) → M i k B
  bind = _>>=_

  -- short-circut conditional
  ifM_then_else_ : M i j Bool → M j k A → M j k A → M i k A
  ifM mb then mx else my = caseM mb of λ where
    true  → mx
    false → my

  IxMonad⇒IxApplicative : IxApplicative M
  pure    ⦃ IxMonad⇒IxApplicative ⦄ = return
  _<*>_   ⦃ IxMonad⇒IxApplicative ⦄ = ap
open IxMonad ⦃...⦄ public

{-# DISPLAY IxMonad.return = return #-}
{-# DISPLAY IxMonad._>>=_  = _>>=_  #-}
{-# DISPLAY IxMonad.join   = join #-}
{-# DISPLAY IxMonad.ifM_then_else_  = ifM_then_else_ #-}

Monad : Fun → Setω
Monad M = IxMonad {I = ⊤} λ _ _ → M

Monad⇒Applicative : {M : Fun} ⦃ _ : Monad M ⦄ → Applicative M
Monad⇒Applicative {M} = IxMonad⇒IxApplicative {M = λ _ _ → M}

instance
  MonadList : Monad List
  return ⦃ MonadList ⦄      = _∷ []
  _>>=_  ⦃ MonadList ⦄ xs f = concatMap f xs

  ApplicativeList : Applicative List
  ApplicativeList = Monad⇒Applicative

  MaybeMonad : Monad Maybe
  return ⦃ MaybeMonad ⦄ = just
  _>>=_ ⦃ MaybeMonad ⦄ (just x) f = f x
  _>>=_ ⦃ MaybeMonad ⦄ nothing f  = nothing

  MaybeApplicative : Applicative Maybe
  MaybeApplicative = Monad⇒Applicative

  VecMonad : Monad (λ A → Vec A n)
  return ⦃ VecMonad ⦄      = V.replicate
  _>>=_  ⦃ VecMonad ⦄ ma f = diag (f <$> ma)

  VecApplicative : Applicative (λ A → Vec A n)
  VecApplicative = Monad⇒Applicative

  ListAlternative : Alternative List
  ListAlternative = mkAlternative [] L._++_

  MaybeAlternative : Alternative Maybe
  MaybeAlternative = mkAlternative nothing λ where
    nothing mb    → mb
    ma@(just _) _ → ma

  VecAlternative : MAlternative λ n A → Vec A n
  VecAlternative = record { _∙_ = _+_ ; empty = [] ; _<|>_ = V._++_ }

DContT : (I → Set) → (M : Fun) → IxFun I
DContT K M r₂ r₁ A = (A → M (K r₁)) → M (K r₂)

DContTIMonad : ⦃ _ : IxMonad IxM ⦄ {K : I → Set} → IxMonad (DContT K M)
return ⦃ DContTIMonad ⦄ a k    = k a
_>>=_  ⦃ DContTIMonad ⦄ c f k  = c (flip f k)

record IxMonadPlus (M : IxFun I) : Setω where
  field
    ⦃ alternative ⦄ : IxAlternative M
    ⦃ monad       ⦄ : IxMonad M
open IxMonadPlus ⦃...⦄ public

MonadPlus : Fun → Setω
MonadPlus M = IxMonadPlus {I = ⊤} λ _ _ → M

record IxMonadError (E : Set) (M : IxFun I) : Setω where
  infixl 6 try_catch_
  infix  6 try_finally_
  infix  7 _finally_
  field
    throw      : E → M i j A
    try_catch_ : M i j A → (E → M i j A) → M i j A
    ⦃ monad ⦄  : IxMonad M

  _finally_ : M i j A → M i j A → M i j A
  ma finally mb = try ma catch (λ _ → mb)

  try_finally_ : M i j A → M i j A → M i j A
  try ma finally mb = ma finally mb
open IxMonadError ⦃...⦄ public

MonadError : (E : Set) → (M : Fun) → Setω
MonadError E M = IxMonadError {I = ⊤} E λ _ _ → M

record IxMonadFail (S : Set ℓ) (M : IxFun I) : Setω where
  field
    ⦃ monad ⦄ : IxMonad M
    fail      : {A : Set ℓ} → S → M i j A
open IxMonadFail ⦃...⦄ public

MonadFail : Set ℓ → (M : Fun) → Setω
MonadFail S M = IxMonadFail {I = ⊤} S λ _ _ → M
------------------------------------------------------------------------
-- Iterator idioms

record Foldable (F : Fun) : Setω where
  field
    foldr : (A → B → B) → B → F A → B

  foldMap : (_∙_ : C → C → C) ⦃ _ : Monoid C _∙_ ⦄ → (A → C) → F A → C
  foldMap _∙_ f = foldr (_∙_ ∘ f) ε

  asum : ⦃ _ : Alternative T ⦄ → F (T A) -> T A
  asum = foldr _<|>_ empty

  asum′ : ⦃ _ : Alternative T ⦄ → T A → F (T A) → T A
  asum′ z = foldr _<|>_ z

  all any : (A → Bool) → F A → Bool
  all f = foldMap _&&_ f
  any f = foldMap _||_ f

  and or : F Bool → Bool
  and = all id
  or  = any id
open Foldable ⦃...⦄ public

instance
  ListFoldable : Foldable List
  foldr ⦃ ListFoldable ⦄ = L.foldr

  VecFoldable : Foldable (λ A → Vec A n)
  foldr ⦃ VecFoldable ⦄ f z []       = z
  foldr ⦃ VecFoldable ⦄ f z (x ∷ xs) = f x (foldr f z xs)

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
  MaybeTraversable : Traversable Maybe
  traverse ⦃ MaybeTraversable ⦄ f (just x) = pure just <*> f x
  traverse ⦃ MaybeTraversable ⦄ f nothing  = pure nothing

  ListTraversable : Traversable List
  traverse ⦃ ListTraversable ⦄ f = foldr (λ x ys → ⦇ f x ∷ ys ⦈) ⦇ [] ⦈

  VecTraversable : Traversable (λ A → Vec A n)
  traverse ⦃ VecTraversable ⦄ f []       = pure []
  traverse ⦃ VecTraversable ⦄ f (x ∷ xs) = ⦇ f x ∷ traverse f xs ⦈
