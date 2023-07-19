{-# OPTIONS --safe #-}
module Data.Nat.Order.Inductive where

open import Foundations.Base
open import Foundations.Prim.Equiv
open import Foundations.Equiv.Base

open import Meta.Search.HLevel

open import Data.Dec.Base
open import Data.Empty.Base
open import Data.Sum.Base
open import Data.Unit.Base

open import Data.Nat.Base
open import Data.Nat.Properties

private variable
  m n k : ℕ

data _≤_ : ℕ → ℕ → Type where
  instance
    z≤ : 0 ≤ n
  s≤s : m ≤ n → suc m ≤ suc n

instance
  s≤s′ : ⦃ p : m ≤ n ⦄ → suc m ≤ suc n
  s≤s′ ⦃ p ⦄ = s≤s p

Positive : ℕ → Type
Positive zero    = ⊥
Positive (suc _) = ⊤

_<_ : ℕ → ℕ → Type
m < n = suc m ≤ n
infix 3 _<_ _≤_

_≥_ : ℕ → ℕ → Type
m ≥ n = n ≤ m

_>_ : ℕ → ℕ → Type
m > n = n < m

-- Properties of order

≤-refl : n ≤ n
≤-refl {(zero)} = z≤
≤-refl {suc n}  = s≤s ≤-refl

≤-trans : m ≤ n → n ≤ k → m ≤ k
≤-trans z≤      z≤      = z≤
≤-trans z≤      (s≤s q) = z≤
≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)

≤-antisym : m ≤ n → n ≤ m → m ＝ n
≤-antisym z≤      z≤      = refl
≤-antisym (s≤s p) (s≤s q) = ap suc (≤-antisym p q)

opaque
  unfolding is-of-hlevel
  ≤-is-prop : is-prop (m ≤ n)
  ≤-is-prop z≤      z≤      = refl
  ≤-is-prop (s≤s p) (s≤s q) = ap s≤s (≤-is-prop p q)

instance
  ≤-is-of-hlevel : is-of-hlevel (suc k) (m ≤ n)
  ≤-is-of-hlevel = is-prop→is-of-hlevel-suc ≤-is-prop

≤-peel : suc m ≤ suc n → m ≤ n
≤-peel (s≤s p) = p

≤-peel-unpeel : (p : suc m ≤ suc n) → s≤s (≤-peel p) ＝ p
≤-peel-unpeel (s≤s _) = refl

≤-suc-r : m ≤ n → m ≤ suc n
≤-suc-r z≤      = z≤
≤-suc-r (s≤s p) = s≤s (≤-suc-r p)

≤-ascend : n ≤ suc n
≤-ascend = ≤-suc-r ≤-refl

<-weaken : (x y : ℕ) → x < y → x ≤ y
<-weaken x (suc y) (s≤s prf) = ≤-suc-r prf

<-trans : {x y z : ℕ} → x < y → y < z → x < z
<-trans xy yz = ≤-trans xy (<-weaken _ _ yz)

≤-+-l : (x y : ℕ) → x ≤ y + x
≤-+-l zero    y = z≤
≤-+-l (suc x) y = subst id (sym (ap (λ q → suc x ≤ q) (+-sucr y x))) (s≤s (≤-+-l x y))

≤-weak-+l : (x y z : ℕ) → x ≤ z → x ≤ y + z
≤-weak-+l x  zero   z prf = prf
≤-weak-+l x (suc y) z prf = ≤-suc-r (≤-weak-+l x y z prf)

≤-subst : {a b c d : ℕ} → a ＝ b → c ＝ d → a ≤ c → b ≤ d
≤-subst {a} {b} {c} {d} ab cd = subst id (ap₂ (_≤_) ab cd)

≤-+l-≃ : {x y z : ℕ} → (y ≤ z) ≃ (x + y ≤ x + z)
≤-+l-≃ {x} {y} {z} = prop-extₑ! (ff x y z) (gg x y z)
  where
  ff : (a b c : ℕ) → b ≤ c → a + b ≤ a + c
  ff zero    b c prf = prf
  ff (suc a) b c prf = s≤s (ff a b c prf)

  gg : (a b c : ℕ) → a + b ≤ a + c → b ≤ c
  gg  zero   b c prf = prf
  gg (suc a) b c prf = gg a b c (≤-peel prf)

≤-+r-≃ : {x y z : ℕ} → (x ≤ y) ≃ (x + z ≤ y + z)
≤-+r-≃ {x} {y} {z} =
  (≤-+l-≃ {x = z} {y = x} {z = y})
  ∙ₑ prop-extₑ! (≤-subst (+-comm z x) (+-comm z y)) (≤-subst (+-comm x z) (+-comm y z))

≤-cong-+ : (m n p q : ℕ) → m ≤ p → n ≤ q → m + n ≤ p + q
≤-cong-+ zero    n  p      q prf1 prf2 = ≤-weak-+l n p q prf2
≤-cong-+ (suc m) n (suc p) q prf1 prf2 = s≤s (≤-cong-+ m n p q (≤-peel prf1) prf2)

<-+l-≃ : {x y z : ℕ} → (y < z) ≃ (x + y < x + z)
<-+l-≃ {x} {y} {z} =
  ≤-+l-≃ {x = x} {y = suc y} {z = z}
  ∙ₑ prop-extₑ! (≤-subst (+-sucr x y) refl) (≤-subst (sym (+-sucr x y)) refl)

<-+r-≃ : {x y z : ℕ} → (x < y) ≃ (x + z < y + z)
<-+r-≃ {x} = ≤-+r-≃ {x = suc x}

≤-·l : (a b c : ℕ) → b ≤ c → a · b ≤ a · c
≤-·l  zero   b c prf = z≤
≤-·l (suc a) b c prf = ≤-cong-+ b (a · b) c (a · c) prf (≤-·l a b c prf)

≤-dec : (m n : ℕ) → Dec (m ≤ n)
≤-dec zero zero = yes z≤
≤-dec zero (suc y) = yes z≤
≤-dec (suc x) zero = no λ { () }
≤-dec (suc x) (suc y) with ≤-dec x y
... | yes x≤y = yes (s≤s x≤y)
... | no ¬x≤y = no (λ { (s≤s x≤y) → ¬x≤y x≤y })

¬sucn≤n : ¬ (suc n ≤ n)
¬sucn≤n {(suc n)} (s≤s ord) = ¬sucn≤n ord

¬sucn≤0 : ¬ (suc n ≤ 0)
¬sucn≤0 {(suc n)} = λ ()

≤-split : (m n : ℕ) → (m < n) ⊎ (n < m) ⊎ (m ＝ n)
≤-split m n with ≤-dec (suc m) n
≤-split m n | yes m<n = inl m<n
≤-split m n | no m≥n with ≤-dec (suc n) m
≤-split m n | no m≥n | yes n<m = inr (inl n<m)
≤-split m n | no m≥n | no n≥m  = inr (inr (go m n m≥n n≥m)) where
  go : ∀ m n → ¬ (suc m ≤ n) → ¬ (suc n ≤ m) → m ＝ n
  go zero zero p q          = refl
  go zero (suc zero) p q    = absurd (p (s≤s z≤))
  go zero (suc (suc n)) p q = absurd (p (s≤s z≤))
  go (suc zero) zero p q    = absurd (q (s≤s z≤))
  go (suc (suc m)) zero p q = absurd (q (s≤s z≤))
  go (suc m) (suc n) p q    = ap suc (go m n (λ { a → p (s≤s a) }) λ { a → q (s≤s a) })
