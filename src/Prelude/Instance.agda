{-# OPTIONS --overlapping-instances #-}

module Prelude.Instance where

open import Prelude.Base
open import Prelude.Instance.Algebra public
    
record Enum (A : Set ℓ) : Set (lsuc ℓ) where
  field
    succ pred : A → A
    toEnum    : A → ℕ
    fromEnum  : ℕ → A
open Enum ⦃...⦄ public

record Eq (A : Set ℓ) : Set (lsuc ℓ) where
  infix 6 _==_ _/=_
  field
    _==_ : A → A → Bool

  _/=_ : A → A → Bool
  x /= y with x == y
  ... | true  = false
  ... | false = true
open Eq ⦃...⦄ public

record Ord (A : Set ℓ) : Set (lsuc ℓ) where
  infix 6 _<=_
  field
    _<=_ : A → A → Bool
open Ord ⦃...⦄ public

record Show (A : Set ℓ) : Set (lsuc ℓ) where
  field
    show : A → String
open Show ⦃...⦄ public

record POrd (A : Set ℓ) : Set (lsuc ℓ) where
-- Propositional Partial order
  infix 6 _≤_
  infix 6 _<_
  field
    _≤_ : A → A → Set
    _<_ : A → A → Set
open POrd ⦃...⦄ public

record DecEq (A : Set ℓ) : Set (lsuc ℓ) where
  field
    _≟_ : (x y : A) → Dec (x ≡ y)
  instance
    DecEq⇒Eq : Eq A
    DecEq⇒Eq = record { _==_ = λ x y → ⌊ x ≟ y ⌋ }
open DecEq ⦃...⦄ public

record ListLike (LL : ℕ → Set ℓ) : Set (lsuc ℓ) where
  field
    base      : Set ℓ
    singleton : base → LL 1
    empty     : LL 0
    _++_      : LL n → LL m → LL (n + m)
    length    : LL n → ℕ
    fromList  : List base → Σ ℕ LL
    toList    : Σ ℕ LL → List base
  [_]         = singleton
open ListLike ⦃...⦄ public


-- Categorical

record Functor (T : Set ℓ₁ → Set ℓ₂) : Set (lsuc $ ℓ₁ ⊔ ℓ₂) where
  infixl 6 _<$>_
  field
    _<$>_ : (A → B) → T A → T B

  map = _<$>_
open Functor ⦃...⦄ public
  
record Bifunctor (T : Set ℓ₁ → Set ℓ₂ → Set ℓ₃)
  : Set (lsuc ℓ₁ ⊔ lsuc ℓ₂ ⊔ ℓ₃) where
  field
    bimap : (A → C) → (B → D) → T A B → T C D

  map₁ : (A → C) → T A B → T C B
  map₁ f = bimap f id

  map₂ : (B → D) → T A B → T A D
  map₂ g = bimap id g 
open Bifunctor ⦃...⦄ public

record SymBifunctor (T : Set ℓ → Set ℓ → Set ℓ′) : Set (lsuc ℓ ⊔ ℓ′) where
  field
    swap : T A B → T B A 
    ⦃ bifunc ⦄ : Bifunctor T
open SymBifunctor ⦃...⦄ public

------------------------------------------------------------------------
-- Indexed applicative functor / monad

private
  variable
    I : Set ℓ
    i j k : I
    
IFun : Set ℓ → (ℓ₁ ℓ₂ : Level) → Set _
IFun I ℓ₁ ℓ₂ = I → I → Set ℓ₁ → Set ℓ₂

record IApplicative {I : Set ℓ} (F : IFun I ℓ₁ ℓ₂ ) : Set (ℓ ⊔ lsuc (ℓ₁ ⊔ ℓ₂)) where
  infixl 4 _<*>_
  field
    pure  : A → F i i A
    _<*>_ : F i j (A → B) → F j k A → F i k B
    instance overlap ⦃ functor ⦄ : ∀ {i j} → Functor (F i j)
{-
  filterA : (A → F i j ? → List A → F (List A)
  filterA p []               = pure []
  filterA {A = A} p (x ∷ xs) = ⦇ go (p x) (filterA p xs) ⦈
    where
      go : Lift ℓ Bool → List A → List A
      go = (if_then (x ∷_) else id) ∘ lower
-}
  zipWith : (A → B → C) → F i j A → F j k B → F i k C
  zipWith f x y = ⦇ f x y ⦈

  zip : F i j A → F j k B → F i k (Σ A λ _ → B)
  zip = zipWith _,_
  
open IApplicative ⦃...⦄ public

Applicative : (Set ℓ₁ → Set ℓ₂) → Set (lsuc (ℓ₁ ⊔ ℓ₂))
Applicative F = IApplicative {I = ⊤} λ _ _ → F

record IMonad {I : Set ℓ} (M : IFun I ℓ₁ ℓ₂) : Set (ℓ ⊔ lsuc (ℓ₁ ⊔ ℓ₂)) where
  infixl 2 _>>=_ _>>_ _>=>_
  infixr 2 _=<<_ _<=<_
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

  instance
    monad⇒applicative : IApplicative M
    monad⇒applicative = record
      { pure    = return
      ; _<*>_   = ap
      ; functor = record { _<$>_ = λ f ma → ma >>= λ a → return $ f a }
      }
open IMonad ⦃...⦄ public

Monad : (M : Set ℓ₁ → Set ℓ₂) → Set (lsuc $ ℓ₁ ⊔ ℓ₂)
Monad M = IMonad {I = ⊤} λ _ _ → M

record IAlternative (M : Set ℓ′) {I : Set ℓ} (F : M → IFun I ℓ₁ ℓ₂)
  : Set (ℓ ⊔ lsuc (ℓ′ ⊔ ℓ₁ ⊔ ℓ₂)) where
  infixr 3 _<|>_
  field
    ⦃ monoid ⦄ : Monoid M
    ⦃ applicative ⦄ : ∀ {m} → IApplicative $ F m
    azero : F ε i j A
    _<|>_ : ∀ {x y} → F x i j A → F y i j A → F (x ∙ y) i j A
open IAlternative ⦃...⦄ public

MAlternative : (M : Set ℓ′) → (M → Set ℓ₁ → Set ℓ₂) → Set (lsuc $ ℓ′ ⊔ ℓ₁ ⊔ ℓ₂)
MAlternative M F = IAlternative M {I = ⊤} λ m _ _ → (F m)

Alternative : (Set ℓ₁ → Set ℓ₂) → Set (lsuc $ ℓ₁ ⊔ ℓ₂)
Alternative F = IAlternative ⊤ {I = ⊤} λ _ _ _ → F

record IMonadPlus (N : Set ℓ′) {I : Set ℓ} (M : N → IFun I ℓ₁ ℓ₂)
  : Set (ℓ ⊔ lsuc (ℓ′ ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    ⦃ alternative ⦄ : IAlternative N M
    ⦃ monad       ⦄ : ∀ {n} → IMonad (M n)
open IMonadPlus ⦃...⦄ public

MonadPlus : (Set ℓ₁ → Set ℓ₂) → Set (lsuc $ ℓ₁ ⊔ ℓ₂)
MonadPlus M = IMonadPlus ⊤ {I = ⊤} λ _ _ _ → M

record IMonadError (E : Set ℓ′) {I : Set ℓ} (M : IFun I ℓ₁ ℓ₂)
  : Set (ℓ′ ⊔ ℓ ⊔ lsuc (ℓ₁ ⊔ ℓ₂))  where
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

MonadError : (E : Set ℓ′) → (M : Set ℓ₁ → Set ℓ₂) → Set (ℓ′ ⊔ lsuc (ℓ₁ ⊔ ℓ₂))
MonadError E M = IMonadError E {I = ⊤} λ _ _ → M

record Foldable (T : Set ℓ → Set ℓ′) : Set (lsuc ℓ ⊔ ℓ′) where
  field
    foldr : {A B : Set ℓ} → (A → B → B) → B → T A → B 

  foldMap : ∀ {M : Set ℓ} ⦃ _ : Monoid M ⦄ {A} → (A → M) → T A → M
  foldMap ⦃ m ⦄ f = foldr (_∙_ ∘ f) ε

  asum : ∀ {F} ⦃ _ : Alternative F ⦄ → T (F A) -> F A
  asum = foldr _<|>_ azero
open Foldable ⦃...⦄ public

record Traversable (T : Set ℓ → Set ℓ) : Set (lsuc $ ℓ) where
  field
    traverse : ∀ {F} ⦃ _ : Applicative F ⦄ → (A → F B) → T A → F (T B)
    ⦃ functor ⦄  : Functor T
    ⦃ foldable ⦄ : Foldable T

  private
    variable F : Set ℓ → Set ℓ

  sequence : ⦃ _ : Applicative F ⦄ → T $ F A → F $ T A
  sequence = traverse id

  for : ∀ ⦃ _ : Applicative F ⦄ → T A → (A → F B) → F $ T B
  for = flip traverse

open Traversable ⦃...⦄ public
