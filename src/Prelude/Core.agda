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

typeOf : A → Set _
typeOf {A = A} _ = A
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
  NatE = record { _==_ = Nat._==_ }
  CharEq   : Eq Char
  _==_ ⦃ CharEq ⦄ = C.primCharEquality
  StringE : Eq String
  _==_ ⦃ StringE ⦄ = primStringEquality
  FloatE : Eq Float
  _==_ ⦃ FloatE ⦄ = F.primFloatEquality
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
    
record ISequence {A : Set} (Seq : A → Set ℓ) : Set (lsuc ℓ) where
  infixr 5 _++_
  field
    zeroIdx  : A
    unitIdx  : A
    addIdx   : A → A → A 
    carrier  : Set ℓ
    [_]      : carrier → Seq unitIdx
    emptySeq : Seq zeroIdx
    _++_     : ∀ {n m} → Seq n → Seq m → Seq (addIdx n m)
    length   : ∀ {n}   → Seq n → ℕ
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
    
  VecSequence : ISequence (Vec A)
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
{-    
IFun : Set ℓ → Setω
IFun I = ∀ {ℓ} → I → I → Set ℓ → Set ℓ
-}
private
  variable
    F T   : Fun
    I     : Set ℓ
--    IF IT : IFun I
--    i j k : I

record Functor (T : Fun) : Setω where
  infixl 6 _<$>_
  field
    _<$>_ : (A → B) → T A → T B
  map = _<$>_
open Functor ⦃...⦄ public

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

record Applicative (F : Fun) : Setω where
  infixl 4 _<*>_
  field
    pure  : A → F A
    _<*>_ : F (A → B) → F A → F B
    ⦃ functor ⦄ : Functor F
    
  zipWith : (A → B → C) → F A → F B → F C
  zipWith f x y = ⦇ f x y ⦈

  zip : F A → F B → F (Σ A λ _ → B)
  zip = zipWith _,_

  when : Bool → F ⊤ → F ⊤
  when false s = pure tt
  when true  s = s
open Applicative ⦃...⦄ public
{-
Applicative : Fun → Setω
Applicative F = IApplicative {I = ⊤} λ _ _ → F
-}
filterA : ⦃ _ : Applicative F ⦄ → (A → F Bool) → List A → F (List A)
filterA p []       = pure []
filterA p (x ∷ xs) = let ys = filterA p xs in
  ⦇ if p x then map (x ∷_) ys else ys ⦈

record Monad (M : Fun) : Setω where
  infixl 1 _>>=_ _>>_ _>=>_ _>>_
  infixr 1 _=<<_ _<=<_
  field
    return : A → M A
    _>>=_  : M A → (A → M B) → M B
  
  _=<<_ : (A → M B) → M A → M B
  f =<< c = c >>= f
  
  _>>_ : M A → M B → M B
  ma >> mb = ma >>= λ _ → mb

  _<<_ : M B → M A → M B
  mb << ma = ma >> mb
  
  _>=>_ : (A → M B) → (B → M C) → (A → M C)
  f >=> g = _=<<_ g ∘ f

  _<=<_ : (B → M C) → (A → M B) → (A → M C)
  g <=< f = f >=> g

  infixr 0 caseM_of_
  caseM_of_ = _>>=_
  
  ap : M (A → B) → M A → M B
  ap mf ma = mf >>= λ f → ma >>= return ∘ f

  join : M (M A) → M A
  join ma = ma >>= id
open Monad ⦃...⦄ public

bind : (M : Fun) ⦃ _ : Monad M ⦄ → M A → (A → M B) → M B
bind M = _>>=_ {M = M}

monad⇒applicative : {M : Fun} ⦃ _ : Monad M ⦄ → Applicative M
pure    ⦃ monad⇒applicative ⦄ = return
_<*>_   ⦃ monad⇒applicative ⦄ = ap
functor ⦃ monad⇒applicative ⦄ = record { _<$>_ = λ f ma → ma >>= return ∘ f }

{-
Monad : Fun → Setω
Monad M = IMonad {I = ⊤} λ _ _ → M
-}
instance
  MonadList : Monad List
  return ⦃ MonadList ⦄      = _∷ []
  _>>=_  ⦃ MonadList ⦄ xs f = concatMap f xs

  ApplicativeList : Applicative List
  ApplicativeList = monad⇒applicative

  MaybeMonad : Monad Maybe
  return ⦃ MaybeMonad ⦄ = just
  _>>=_ ⦃ MaybeMonad ⦄ (just x) f = f x
  _>>=_ ⦃ MaybeMonad ⦄ nothing f  = nothing

  MaybeApplicative : Applicative Maybe
  MaybeApplicative = monad⇒applicative

  VecMonad : Monad (λ A → Vec A n)
  return ⦃ VecMonad ⦄      = V.replicate
  _>>=_  ⦃ VecMonad ⦄ ma f = diag (f <$> ma)

  VecApplicative : Applicative (λ A → Vec A n)
  VecApplicative = monad⇒applicative

record MAlternative (F : C → Fun) : Setω where
  infixr 3 _<|>_
  field
    _∙_ : C → C → C
    ⦃ applicative ⦄ : {c : C} → Applicative (F c)
    ⦃ monoid ⦄      : Monoid C _∙_
    empty : F ε A
    _<|>_ : ∀ {x y} → F x A → F y A → F (x ∙ y) A

  ⦇⦈ = empty
  
  guard : Bool → F ε ⊤
  guard true  = pure tt
  guard false = empty
open MAlternative ⦃...⦄ public
{-
MAlternative : (C → Fun) → Setω
MAlternative F = IMAlternative {I = ⊤} λ m _ _ → F m
-}
{-
IAlternative : IFun I → Setω
IAlternative F = IMAlternative {C = ⊤} λ _ → F
-}
Alternative : Fun → Setω
Alternative F = MAlternative {C = ⊤} λ _ → F

mkAlternative : ⦃ _ : Applicative F ⦄
  → (∀ {ℓ} {A : Set ℓ} → F A) → (∀ {ℓ} {A : Set ℓ} → F A → F A → F A) → Alternative F
mkAlternative z f = record { _∙_ = λ _ _ → tt ; empty = z ; _<|>_ = f }

instance
  ListAlternative : Alternative List
  ListAlternative = mkAlternative [] L._++_

  MaybeAlternative : Alternative Maybe
  MaybeAlternative = mkAlternative nothing λ where
    nothing mb    → mb
    ma@(just _) _ → ma

  VecAlternative : MAlternative λ n A → Vec A n
  VecAlternative = record { _∙_ = _+_ ; empty = [] ; _<|>_ = V._++_ }

record MonadPlus (M : Fun) : Setω where
  field
    ⦃ alternative ⦄ : Alternative M
    ⦃ monad       ⦄ : Monad M
open MonadPlus ⦃...⦄ public
{-
MonadPlus : Fun → Setω
MonadPlus M = IMonadPlus {I = ⊤} λ _ _ → M
-}
record MonadError (E : Set) (M : Fun) : Setω where
  infixl 6 try_catch_
  infix  6 try_finally_
  infix  7 _finally_
  field
    throw      : E → M A
    try_catch_ : M A → (E → M A) → M A
    ⦃ monad ⦄  : Monad M
    
  _finally_ : M A → M A → M A
  ma finally mb = try ma catch (λ _ → mb)

  try_finally_ : M A → M A → M A
  try ma finally mb = ma finally mb
open MonadError ⦃...⦄ public
{-
MonadError : (E : Set) → (M : Fun) → Setω
MonadError E M = IMonadError {I = ⊤} E λ _ _ → M
-}
instance
  E+Monad : {E : Set} → Monad (E ⊎_)
  return ⦃ E+Monad ⦄ = inj₂
  _>>=_  ⦃ E+Monad ⦄ = λ where
    (inj₁ e) f → inj₁ e
    (inj₂ a) f → f a 
  
  MonadExcept : {E : Set} → MonadError E (E ⊎_)
  throw ⦃ MonadExcept ⦄      = inj₁
  try_catch_ ⦃ MonadExcept ⦄ = λ where
    (inj₁ e) f → f e
    (inj₂ a) _ → inj₂ a
    
record MonadFail (M : Fun) : Setω where
  field
    ⦃ monad ⦄ : Monad M
    fail      : {A : Set ℓ} → String → M A 
open MonadFail ⦃...⦄ public
{-
MonadFail : (M : Fun) → Setω
MonadFail M = IMonadFail {I = ⊤} λ _ _ → M
-}
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
  ListTraversable : Traversable List
  traverse ⦃ ListTraversable ⦄ f = foldr (λ x ys → ⦇ f x ∷ ys ⦈) ⦇ [] ⦈

  MaybeTraversable : Traversable Maybe
  traverse ⦃ MaybeTraversable ⦄ f (just x) = just <$> f x
  traverse ⦃ MaybeTraversable ⦄ f nothing  = pure nothing

  VecTraversable : Traversable (λ A → Vec A n)
  traverse ⦃ VecTraversable ⦄ f []       = pure []
  traverse ⦃ VecTraversable ⦄ f (x ∷ xs) = ⦇ f x ∷ traverse f xs ⦈
