{-# OPTIONS --safe #-}
module Data.Nat.Base where

open import Foundations.Base

open import Data.Bool.Base using (Bool; false; true; not)

open import Agda.Builtin.Nat public
  using
    ( zero
    ; suc
    ; _+_
    ; _==_
    ; div-helper
    ; mod-helper )
  renaming
    ( Nat to ℕ
    ; _-_ to _∸_
    ; _*_ to _·_
    ; _<_ to infix 3 _<?_ )

private variable
  ℓ : Level
  A : Type ℓ

elim : (P : ℕ → Type ℓ)
     → P 0
     → ({n : ℕ} → P n → P (suc n))
     → (n : ℕ) → P n
elim P pz ps zero    = pz
elim P pz ps (suc n) = elim (P ∘ suc) (ps pz) ps n

rec : A → (A → A) → ℕ → A
rec z s = elim _ z s

infixr 8 _^_
_^_ : ℕ → ℕ → ℕ
x ^ zero  = 1
x ^ suc y = x · (x ^ y)

pred : ℕ → ℕ
pred zero    = zero
pred (suc n) = n

is-zero? : ℕ → Bool
is-zero? 0       = true
is-zero? (suc _) = false

is-positive? : ℕ → Bool
is-positive? = not ∘ is-zero?

iter : ℕ → (A → A) → A → A
iter zero    f = id
iter (suc n) f = f ∘ iter n f
