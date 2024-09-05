{-# OPTIONS --safe #-}
module Data.Nat.DivMod.Inductive where

open import Foundations.Base
open import Data.Nat.Base renaming (div-helper to divₕ; mod-helper to modₕ)
open import Data.Nat.DivMod
open import Data.Nat.Order.Inductive
open import Data.Nat.Order.Inductive.Conversion
open import Data.Nat.Properties

-- order

a[modₕ]n<n : ∀ acc d n → modₕ acc (acc + n) d n ≤ acc + n
a[modₕ]n<n acc zero    n       = ≤-trans (≤-+-l acc n) $ subst (_≤ acc + n) (+-comm acc n) ≤-refl
a[modₕ]n<n acc (suc d) zero    = a[modₕ]n<n zero d (acc + 0)
a[modₕ]n<n acc (suc d) (suc n) =
  subst (λ q → modₕ (suc acc) q d n ≤ q) (sym (+-suc-r acc n)) $
  a[modₕ]n<n (suc acc) d n

opaque
  unfolding _%_
  m%n<n : ∀ m n → 0 < n → m % n < n
  m%n<n m  zero   ()
  m%n<n m (suc n) _ = s≤s (a[modₕ]n<n 0 m n)

  m≤n⇒m%n≡m : ∀ m n → m ≤ n → m % suc n ＝ m
  m≤n⇒m%n≡m m n m≤n =
    ap (modₕ 0 n m) (+∸=id m n m≤n ⁻¹) ∙ a≤n⇒a[modₕ]n≡a 0 n m (n ∸ m)

m<n⇒m%n≡m : ∀ m n → m < n → m % n ＝ m
m<n⇒m%n≡m m (suc n) m<n = m≤n⇒m%n≡m m n (≤-peel m<n)

opaque
  unfolding _/_
  m/n*n≤m : ∀ m n → (m / n) · n ≤ m
  m/n*n≤m m    zero   = z≤
  m/n*n≤m m n@(suc _) =
    ≤-trans (≤-+-r _ _) $
    =→≤ $ +-comm (m / n · n) (m % n) ∙ sym (m≡m%n+[m/n]*n m n)

