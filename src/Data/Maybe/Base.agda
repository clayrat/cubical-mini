{-# OPTIONS --safe #-}
module Data.Maybe.Base where

open import Foundations.Base

open import Data.Bool.Base using (Bool; false; true; not)
open import Data.Empty.Base using ()
open import Data.Unit.Base  using ()

open import Agda.Builtin.Maybe public

private variable
  ℓ ℓ′ : Level
  A B C : Type ℓ

rec : B → (A → B) → Maybe A → B
rec b f (just x) = f x
rec b _ nothing  = b

elim : {A : Type ℓ} (B : Maybe A → Type ℓ′)
       (b : B nothing)
       (f : Π[ a ꞉ A ] B (just a))
     → (mx : Maybe A) → B mx
elim B b f nothing  = b
elim B n f (just x) = f x

from-just : A → Maybe A → A
from-just def (just x) = x
from-just def nothing  = def

is-just? : Maybe A → Bool
is-just? (just _) = true
is-just? nothing  = false

is-nothing? : Maybe A → Bool
is-nothing? = not ∘ is-just?
