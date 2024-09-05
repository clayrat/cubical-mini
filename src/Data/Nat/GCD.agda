{-# OPTIONS --safe #-}
module Data.Nat.GCD where

open import Foundations.Base

open import Data.Sum
open import Data.Nat.Base
open import Data.Nat.Order.Inductive
open import Data.Nat.Properties
open import Data.Nat.DivMod
open import Data.Nat.DivMod.Inductive
open import Data.Wellfounded

gcd′ : (m n : ℕ) → Acc _<_ m → n < m → ℕ
gcd′ m    zero    _        _   = m
gcd′ m n@(suc _) (acc rec) n<m = gcd′ n (m % n) (rec n n<m) (m%n<n m n (s≤s z≤))

gcd : ℕ → ℕ → ℕ
gcd m n with ≤-split m n
... | inl      m<n  = gcd′ n m (<-wf n) m<n
... | inr (inl n<m) = gcd′ m n (<-wf m) n<m
... | inr (inr _)   = m
