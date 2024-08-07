{-# OPTIONS --safe #-}
module Data.Nat.Order.Inductive.Decidability where

open import Meta.Prelude

open import Data.Bool.Base
open import Data.Dec.Base
open import Data.Empty.Base
open import Data.Nat.Order.Inductive.Base
open import Data.Reflects.Base as R
open import Data.Sum.Base

private variable m n k : ℕ

≤-reflects : (m n : ℕ) → Reflects⁰ (m ≤ n) (m ≤ᵇ n)
≤-reflects 0        _      = ofʸ z≤
≤-reflects (suc _)  0      = ofⁿ λ ()
≤-reflects (suc m) (suc n) with m ≤ᵇ n | recall (m ≤ᵇ_) n
... | false | ⟪ p ⟫ = ofⁿ λ where
  (s≤s m≤n) → false-reflects (≤-reflects m n) (subst is-true (ap not p ⁻¹) tt) m≤n
... | true  | ⟪ p ⟫ = ofʸ (s≤s (true-reflects (≤-reflects m n) (subst is-true (p ⁻¹) _)))

<-reflects : (m n : ℕ) → Reflects⁰ (m < n) (m <ᵇ n)
<-reflects  m       zero   = ofⁿ ≮z
<-reflects  zero   (suc n) = ofʸ (s≤ʰs z≤ʰ)
<-reflects (suc m) (suc n) = R.dmap s<s (λ ¬m<n → ¬m<n ∘ <-peel) (<-reflects m n)

instance
  Dec-≤ : {m n : ℕ} → Dec (m ≤ n)
  Dec-≤ {m} {n} .does  = m ≤ᵇ n
  Dec-≤ {m} {n} .proof = ≤-reflects m n
  {-# OVERLAPPING Dec-≤ #-}

≤-split : (m n : ℕ) → (m < n) ⊎ (n < m) ⊎ (m ＝ n)
≤-split m n with Dec-≤ {suc m} {n}
≤-split m n | yes m<n = inl m<n
≤-split m n | no m≥n with Dec-≤ {suc n} {m}
≤-split m n | no m≥n | yes n<m = inr (inl n<m)
≤-split m n | no m≥n | no n≥m  = inr (inr (go m n m≥n n≥m)) where
  go : ∀ m n → ¬ (suc m ≤ n) → ¬ (suc n ≤ m) → m ＝ n
  go 0       0       _ _ = refl
  go 0       (suc _) p _ = absurd $ p (s≤ʰs z≤ʰ)
  go (suc _) 0       _ q = absurd $ q (s≤ʰs z≤ʰ)
  go (suc m) (suc n) p q = ap suc (go m n (p ∘ s≤ʰs) (q ∘ s≤ʰs))
