module Prelude.Reflection where

open import Prelude.Base

import Reflection
open module TC = Reflection
  hiding (returnTC; return; _>>_; _>>=_; _≟_) public

instance
  TCM : Monad TC
  TCM = record
    { return = TC.return
    ; _>>=_  = TC.bindTC }

  TCA : Applicative TC
  TCA = monad⇒applicative

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
  
  NameIsDecEq : DecEq Name
  NameIsDecEq = record { _≟_ = _≟-Name_ }
  
  TermIsDecEq : DecEq Term
  TermIsDecEq = record { _≟_ = TC._≟_ }

  LitIsDecEq : DecEq Literal
  LitIsDecEq = record { _≟_ = _≟-Lit_ }

  MetaShow : Show Meta
  MetaShow = record { show = showMeta }
  
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
      
  ArgInfoShow : Show Arg-info
  ArgInfoShow = record { show = λ { (arg-info v r) → show v ++ " " ++ show r ++ " arg" } }

  NameShow : Show Name
  NameShow = record { show = showName }

pattern var₀ x         = var x []
pattern var₁ x a       = var x (vArg a ∷ [])
pattern var₂ x a b     = var x (vArg a ∷ vArg b ∷ [])
pattern var₃ x a b c   = var x (vArg a ∷ vArg b ∷ vArg c ∷ [])
pattern var₄ x a b c d = var x (vArg a ∷ vArg b ∷ vArg c ∷ vArg d ∷ [])

pattern con₀ c         = con c []
pattern con₁ c x       = con c (vArg x ∷ [])
pattern con₂ c x y     = con c (vArg x ∷ vArg y ∷ [])
pattern con₃ c x y z   = con c (vArg x ∷ vArg y ∷ vArg z ∷ [])
pattern con₄ c x y z u = con c (vArg x ∷ vArg y ∷ vArg z ∷ vArg u ∷ [])

pattern def₀ f         = def f []
pattern def₁ f x       = def f (vArg x ∷ [])
pattern def₂ f x y     = def f (vArg x ∷ vArg y ∷ [])
pattern def₃ f x y z   = def f (vArg x ∷ vArg y ∷ vArg z ∷ [])
pattern def₄ f x y z u = def f (vArg x ∷ vArg y ∷ vArg z ∷ vArg u ∷ [])
pattern _↦_ ps t = clause ps t
infix 8 _↦_

pattern sortSet t = sort (set t)
pattern sortLit i = sort (lit i)

Script     = Term → TC ⊤
Types      = List Type
Metas      = List Meta
Terms      = List Term
ErrorParts = List ErrorPart

macro
  runTC : {A : Set ℓ} → TC A → Script
  runTC t _ = t >> return tt

arity : Term → ℕ
arity (Π[ _ ∶ _ ] b) = 1 + arity b
arity _              = 0

body : Arg Term → Term
body (arg i x) = x

newMeta' : Type → TC Meta
newMeta' t = do
  meta m [] ← checkType unknown t
    where _ → typeError (strErr "not a meta variable" ∷ [])
  return m

module Syntax where
  record Rec {A B C : Set} : Set where
    field
      Pvar : ℕ → Args A → A
      Pcon : Name → Args A → A
      Pdef : Name → Args A → A
      Plam : Visibility → Abs A → A
      Ppat-lam : List B → Args A → A
      Ppi      : Arg A → Abs A → A
      Psort : C → A
      PsortSet : A → C
      PsortLit : ℕ → C
      PsortUnknown : C
      Plit  : Literal → A
      Pmeta : Meta → Args A → A
      Punknown : A
      Pclause : Args Pattern → A → B
      PabsClause : Args Pattern → B -- where
    mutual
      recArg : Arg Term → Arg A
      recArg (arg i x) = arg i (recTerm x)

      recArgs : Args Term → List (Arg A)
      recArgs [] = []
      recArgs (t ∷ ts) = recArg t ∷ recArgs ts

      recAbs : Abs Term → Abs A
      recAbs (abs s t) = abs s (recTerm t)

      recClause : Clause → B
      recClause (clause ps t)      = Pclause ps (recTerm t)
      recClause (absurd-clause ps) = PabsClause ps

      recClauses : Clauses → List B
      recClauses [] = []
      recClauses (c ∷ cs) = recClause c ∷ recClauses cs

      recSort : Sort → C
      recSort (set t) = PsortSet (recTerm t)
      recSort (lit n) = PsortLit n
      recSort unknown = PsortUnknown

      recTerm : Term → A
      recTerm (var x args) = Pvar x (recArgs args)
      recTerm (con c args) = Pcon c (recArgs args)
      recTerm (def f args) = Pdef f (recArgs args)
      recTerm (lam v t) = Plam v (recAbs t)
      recTerm (pat-lam cs args) = Ppat-lam (recClauses cs) (recArgs args)
      recTerm (pi a b) = Ppi (recArg a) (recAbs b)
      recTerm (sort s) = Psort (recSort s)
      recTerm (lit l) = Plit l
      recTerm (meta x args) = Pmeta x (recArgs args)
      recTerm unknown = Punknown
  open Rec public
    using (recTerm; recSort; recClauses)
    
  idRec : Rec
  idRec = record
    { Pvar = var ; Pcon = con ; Pdef = def ; Plam = lam ; Ppat-lam = pat-lam ; Ppi = pi
    ; Psort = sort ; PsortSet = set ; PsortLit = lit ; PsortUnknown = unknown
    ; Plit = lit ; Pmeta = meta ; Punknown = unknown
    ; Pclause = clause
    ; PabsClause = absurd-clause
    }
  weakRec : ℕ → Rec
  weakRec n = record idRec { Pvar = λ x args → var (n + x) args }

  varToMetaRec : Metas → Rec
  varToMetaRec metaCxt = record idRec { Pvar = metaOrVar }
    where
      metaOrVar : ℕ → Args Term → Term
      metaOrVar n args with metaCxt !! n
      ... | nothing = var n args
      ... | just x  = meta x args
    
  weaken : ℕ → Term → Term
  weaken = recTerm ∘ weakRec

  varsToMetas : List Meta → Term → Term
  varsToMetas = recTerm ∘ varToMetaRec
open Syntax public
