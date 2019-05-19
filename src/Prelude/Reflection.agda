{-# OPTIONS --without-K --safe #-}

module Prelude.Reflection where

open import Prelude.Base

import Agda.Builtin.Reflection as Builtin
open module TC = Builtin public
  renaming ( left-assoc  to assocˡ
           ; right-assoc to assocʳ
           ; primQNameFixity to getFixity
           ; arg-info to argInfo
           ; agda-sort to sort
           ; record-type to record′
           ; data-cons   to constructor′
           ; prim-fun    to primitive′ )

Names Clauses : Set
Names   = List Name
Clauses = List Clause

Args : (A : Set) → Set
Args A = List (Arg A)

visibility : ArgInfo → Visibility
visibility (argInfo v _) = v

relevance : ArgInfo → Relevance
relevance (argInfo _ r) = r

-- Pattern synonyms for more compact presentation
pattern vArg ty            = arg (argInfo visible relevant)   ty
pattern hArg ty            = arg (argInfo hidden relevant)    ty
pattern iArg ty            = arg (argInfo instance′ relevant) ty
pattern vLam s t           = lam visible   (abs s t)
pattern hLam s t           = lam hidden    (abs s t)
pattern iLam s t           = lam instance′ (abs s t)
pattern Π[_∶_]_  s a ty    = pi a (abs s ty)
pattern vΠ[_∶_]_ s a ty    = Π[ s ∶ (vArg a) ] ty
pattern hΠ[_∶_]_ s a ty    = Π[ s ∶ (hArg a) ] ty
pattern iΠ[_∶_]_ s a ty    = Π[ s ∶ (iArg a) ] ty

------------------------------------------------------------------------
-- Type checking monad

-- Type errors

newMeta : Type → TC Term
newMeta = checkType unknown

instance
  NameEq : Eq Name
  _==_ ⦃ NameEq ⦄ = Builtin.primQNameEquality

  NameShow : Show Name
  show ⦃ NameShow ⦄ = Builtin.primShowQName

  MetaEq : Eq Meta
  _==_ ⦃ MetaEq ⦄ = Builtin.primMetaEquality

  MetaShow : Show Meta
  show ⦃ MetaShow ⦄ = Builtin.primShowMeta

  LitShow : Show Literal
  show ⦃ LitShow ⦄ (nat n)    = show n
  show ⦃ LitShow ⦄ (word64 n) = show n
  show ⦃ LitShow ⦄ (float x)  = show x
  show ⦃ LitShow ⦄ (char c)   = show c
  show ⦃ LitShow ⦄ (string s) = show s
  show ⦃ LitShow ⦄ (name x)   = show x
  show ⦃ LitShow ⦄ (meta x)   = show x

  TCM : Monad TC
  TCM = record
    { return = returnTC
    ; _>>=_  = bindTC }

  TCA : Applicative TC
  TCA = monad⇒applicative ⦃ TCM ⦄
      
  TCFunctor : Functor TC
  TCFunctor = TCA .functor

  TCAlter : Alternative TC
  TCAlter = record
    { azero = typeError []
    ; _<|>_ = catchTC
    }
  
  TCEMonad : {E : Set} → Monad (TC ∘ (E ⊎_))
  TCEMonad = record
    { return = return ∘ inj₂
    ; _>>=_  = λ ma f → do
      (inj₂ a) ← ma  where (inj₁ e) → return $ inj₁ e
      f a
    }
  
  TCEError : {E : Set} → MonadError E (TC ∘ (E ⊎_))
  TCEError = record
    { throw      = return ∘ inj₁
    ; try_catch_ = λ ma handler → do
      inj₁ e ← ma
        where inj₂ a → return a
      handler e } 
  
  VisibilityShow : Show Visibility
  VisibilityShow = record
    { show = λ
      { visible → "Explicit"
      ; hidden  → "Implicit"
      ; instance′ → "Instance" } }

  RelevanceShow : Show Relevance
  RelevanceShow = record
    { show = λ
      { relevant   → "relevant"
      ; irrelevant → "irrelevant" } }
      
  ArgInfoShow : Show ArgInfo
  ArgInfoShow = record { show = λ { (argInfo v r) → show v ++ " " ++ show r ++ " arg" } }

  FunctorArg : Functor Arg 
  _<$>_ ⦃ FunctorArg ⦄ f (arg i x) = arg i (f x)

  FunctorAbs : Functor Abs
  _<$>_ ⦃ FunctorAbs ⦄ f (abs s t) = abs s (f t)

  TraversableArg : Traversable Arg
  traverse {{TraversableArg}} f (arg i x) = ⦇ (arg i) (f x) ⦈
