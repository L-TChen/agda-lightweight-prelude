--{-# OPTIONS --safe --without-K  #-}

module Prelude where

open import Prelude.Base       public

open import Prelude.Product    public
open import Prelude.Maybe      public

open import Prelude.String     public
open import Prelude.Unit       public
open import Prelude.Bool       public
open import Prelude.List       public
open import Prelude.DiffList   public
open import Prelude.Vec        public
open import Prelude.Nat        public

-- unsafe modules 
open import Prelude.Reflection public
open import Prelude.IO         public
