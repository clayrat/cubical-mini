{-# OPTIONS --safe #-}
module Data.Bool.Base where

open import Foundations.Base

open import Data.Empty.Base using (⊥)
open import Data.Unit.Base  using (⊤)

open import Agda.Builtin.Bool public

private variable
  ℓ : Level
  A : Type ℓ

elim : {P : Bool → Type ℓ} (t : P true) (f : P false) (b : Bool) → P b
elim _ f false = f
elim t _ true  = t

rec : A → A → Bool → A
rec = elim

not : Bool → Bool
not true = false
not false = true

infixr 5 _or_ _xor_
_or_ : Bool → Bool → Bool
false or x = x
true  or _ = true

infixr 6 _and_ _implies_ _equals_
_and_ : Bool → Bool → Bool
false and _ = false
true  and x = x

_xor_ : Bool → Bool → Bool
false xor x = x
true  xor x = not x

_equals_ : Bool → Bool → Bool
false equals y = not y
true  equals y = y

_implies_ : Bool → Bool → Bool
true implies false = false
_    implies _     = true

infixr 5 _⊕_
_⊕_ = _xor_
{-# WARNING_ON_USAGE _⊕_ "Use `_xor_` instead" #-}

infix 0 if_then_else_
if_then_else_ : Bool → A → A → A
if false then _  else fa = fa
if true  then tr else _  = tr
-- if b then tr else fa = rec tr fa b
-- TODO Use `rec` and noinline? otherwise it looks bad in goals

is-true : Bool → Type
is-true b = if b then ⊤ else ⊥

is-trueₚ : Bool → Type
is-trueₚ b = b ＝ true

is-falseₚ : Bool → Type
is-falseₚ b = b ＝ false

⟦_⟧ᵇ = is-true
{-# WARNING_ON_USAGE ⟦_⟧ᵇ "Use `is-true`" #-}
