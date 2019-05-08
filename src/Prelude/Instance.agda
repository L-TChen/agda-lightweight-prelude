{-# OPTIONS --overlapping-instances #-}

module Prelude.Instance where

open import Prelude.Base
open import Prelude.Instance.Algebra public

open import Agda.Builtin.Nat
  using () renaming (Nat to ℕ)
open import Agda.Builtin.Equality

open import Relation.Nullary
open import Relation.Binary using (Decidable)
open import Data.List as List using (List)
open import Data.Bool as Bool using (Bool)

record Enum (A : Set ℓ) : Set (suc ℓ) where
  field
    succ pred : A → A
    toEnum    : A → ℕ
    fromEnum  : ℕ → A
open Enum ⦃...⦄ public

record Eq (A : Set ℓ) : Set (suc ℓ) where
  infix 4 _==_ _/=_
  field
    _==_ : A → A → Bool

  _/=_ : A → A → Bool
  x /= y = Bool.not $ x == y
open Eq ⦃...⦄ public

record DecEq (A : Set ℓ) : Set (suc ℓ) where
  field
    _≟_ : Decidable {A = A} (_≡_)

  open import Relation.Nullary.Decidable using (⌊_⌋)
  
  instance
    DecEq⇒Eq : Eq A
    DecEq⇒Eq = record { _==_ = λ x y → ⌊ x ≟ y ⌋ }
open DecEq ⦃...⦄ public

record ListLike (LL : Set ℓ) : Set (suc ℓ) where
  field
    base      : Set ℓ
    singleton : base → LL
    empty     : LL
    _++_      : LL → LL → LL
    length    : LL → ℕ
    fromList  : List base → LL
    toList    : LL → List base
--    ⦃ isMonoid ⦄ : IsMonoid _++_ []
  replicate : ℕ → base → LL
  replicate n = fromList ∘ List.replicate n
  
  [_]         = singleton
open ListLike ⦃...⦄ public

-- Categorical 
record Functor (T : Set ℓ → Set ℓ) : Set (suc ℓ) where
  infixl 6 _<$>_
  field
    _<$>_ : (A → B) → T A → T B

  map = _<$>_
open Functor ⦃...⦄ public

record Bifunctor (T : Set ℓ → Set ℓ′ → Set (ℓ-max ℓ ℓ′))
  : Set (suc $ ℓ-max ℓ ℓ′) where
  field
    bimap : (A → C) → (B → D) → T A B → T C D

  map₁ : (A → C) → T A B → T C B
  map₁ f = bimap f id

  map₂ : (B → D) → T A B → T A D
  map₂ g = bimap id g 
open Bifunctor ⦃...⦄ public

record SymBifunctor (T : Set ℓ → Set ℓ → Set ℓ) : Set (suc ℓ) where
  field
    swap : T A B → T B A 
    ⦃ bifunc ⦄ : Bifunctor T
open SymBifunctor ⦃...⦄ public

record Applicative (F : Set ℓ → Set ℓ) : Set (suc ℓ) where
  infixl 4 _<*>_
  field
    pure    : A → F A
    _<*>_   : F (A → B) → F A → F B
    instance overlap {{functor}} : Functor F
open Applicative ⦃...⦄ public

record Monad (M : Set ℓ → Set ℓ) : Set (suc ℓ) where
  infixl 1 _>>=_ _>>_ _>=>_
  infixr 1 _=<<_ _<=<_

  field
    return : A → M A
    _>>=_  : M A → (A → M B) → M B

  _>>_ : M A → M B → M B
  ma >> mb = ma >>= λ _ → mb

  _=<<_ : (A → M B) → M A → M B
  f =<< c = c >>= f

  _>=>_ : (A → M B) → (B → M C) → (A → M C)
  f >=> g = _=<<_ g ∘ f

  _<=<_ : (B → M C) → (A → M B) → (A → M C)
  g <=< f = f >=> g

  ap : M (A → B) → M A → M B
  ap mf ma = do
    f ← mf
    a ← ma
    return $ f a

  join : M (M A) → M A
  join m = m >>= id

  instance
    monad⇒applicative : Applicative M
    monad⇒applicative = record
      { pure    = return
      ; _<*>_   = ap
      ; functor = record { _<$>_ = λ f ma → ma >>= λ a → return $ f a }
      }
open Monad ⦃...⦄ public

record Alternative (F : Set ℓ → Set ℓ) : Set (suc ℓ) where
  field
    empty : F A
    _<|>_ : F A → F A → F A
    overlap {{super}} : Applicative F
open Alternative ⦃...⦄ public

record MonadPlus (M : Set ℓ → Set ℓ) : Set (suc ℓ) where
  field
    overlap {{alter}} : Alternative M
    overlap {{monad}} : Monad M
open MonadPlus ⦃...⦄ public

record MonadError (E : Set ℓ) (M : Set ℓ → Set ℓ) : Set (suc ℓ) where
  field
    throwError : E → M A
    catchError : M A → (E → M A) → M A
    overlap ⦃ monad ⦄ : Monad M
open MonadError ⦃...⦄ public

record Foldable (T : Set ℓ → Set ℓ) : Set (suc ℓ) where
  field
    foldr    : {A B : Set ℓ} → (A → B → B) → B → T A → B 

  foldMap : ∀ {M : Set ℓ} ⦃ _ : Monoid M ⦄ {A} → (A → M) → T A → M
  foldMap ⦃ m ⦄ f = foldr (_∙_ m ∘ f) ε -- foldr (_∙_ ∘ f) ε
open Foldable ⦃...⦄ public

record Traversable (T : Set ℓ → Set ℓ) : Set (suc ℓ) where
  field
    traverse : ∀ {F} ⦃ _ : Applicative F ⦄ → (A → F B) → T A → F (T B)
    overlap {{super}} : Functor T
    overlap {{suppr}} : Foldable T

  sequence : ∀ {F} ⦃ _ : Applicative F ⦄ → T $ F A → F $ T A
  sequence = traverse id

  for : ∀ {F} ⦃ _ : Applicative F ⦄ → T A → (A → F B) → F $ T B
  for = flip traverse
open Traversable ⦃...⦄ public
