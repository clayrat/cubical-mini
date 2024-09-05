{-# OPTIONS --safe #-}
module Data.Nat.Order.Inductive.Base where

open import Foundations.Prelude

open import Meta.Variadic

open import Data.Bool.Base
open import Data.Empty.Base
open import Data.Nat.Base
  using (_<?_)
  public
open import Data.Nat.Path
open import Data.Nat.Properties
open import Data.Reflects.Base
open import Data.Sum.Base
open import Data.Wellfounded.Base

private variable m n k : ℕ

infix 3 _≤?_      _≥?_ _>?_
        _≰?_ _≮?_ _≱?_ _≯?_

_≤?_ _≥?_ _>?_ _≰?_ _≮?_ _≱?_ _≯?_ : ℕ → ℕ → Bool

m ≤? n =      m <? suc n
m ≥? n =      n ≤? m
m >? n =      n <? m
m ≰? n = not (m ≤? n)
m ≮? n = not (m <? n)
m ≱? n = not (m ≥? n)
m ≯? n = not (m >? n)

infix 3 _≤_ _<_ _≥_ _>_
        _≰_ _≮_ _≱_ _≯_

data _≤_ : ℕ → ℕ → Type where
  instance
    z≤ : 0 ≤ n
  s≤s : m ≤ n → suc m ≤ suc n

_<_ _≥_ _>_ _≰_ _≮_ _≱_ _≯_ : ℕ → ℕ → Type

m < n = suc m ≤ n
m ≥ n = n ≤ m
m > n = n < m
m ≰ n = ¬ m ≤ n
m ≮ n = ¬ m < n
m ≱ n = ¬ m ≥ n
m ≯ n = ¬ m > n


-- Properties of order

≤-trans : m ≤ n → n ≤ k → m ≤ k
≤-trans z≤      z≤      = z≤
≤-trans z≤      (s≤s q) = z≤
≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)

instance
  s≤s′ : ⦃ p : m ≤ n ⦄ → suc m ≤ suc n
  s≤s′ ⦃ p ⦄ = s≤s p

  ≤-refl : n ≤ n
  ≤-refl {(zero)} = z≤
  ≤-refl {suc n}  = s≤s ≤-refl
  {-# INCOHERENT ≤-refl #-}

  Refl-≤ : Refl _≤_
  Refl-≤ .refl = ≤-refl
  {-# OVERLAPPING Refl-≤ #-}

  Trans-≤ : Transʰ _≤_
  Trans-≤ ._∙_ = ≤-trans
  {-# OVERLAPPING Trans-≤ #-}

≤-antisym : m ≤ n → n ≤ m → m ＝ n
≤-antisym z≤      z≤      = refl
≤-antisym (s≤s p) (s≤s q) = ap suc (≤-antisym p q)

opaque
  ≤-is-prop : is-prop (m ≤ n)
  ≤-is-prop z≤      z≤      = refl
  ≤-is-prop (s≤s p) (s≤s q) = ap s≤s (≤-is-prop p q)

instance opaque
  H-Level-≤ : ⦃ k ≥ 1 ⦄ → H-Level k (m ≤ n)
  H-Level-≤ ⦃ s≤s _ ⦄ = hlevel-prop-instance ≤-is-prop
  {-# OVERLAPPING H-Level-≤ #-}

≤-peel : suc m ≤ suc n → m ≤ n
≤-peel (s≤s p) = p

≤-peel-unpeel : (p : suc m ≤ suc n) → s≤s (≤-peel p) ＝ p
≤-peel-unpeel (s≤s _) = refl

≤-suc-r : m ≤ n → m ≤ suc n
≤-suc-r z≤      = z≤
≤-suc-r (s≤s p) = s≤s (≤-suc-r p)

instance
  ≤-suc-r′ : ⦃ m≤n : m ≤ n ⦄ → m ≤ suc n
  ≤-suc-r′ ⦃ m≤n ⦄ = ≤-suc-r m≤n
  {-# INCOHERENT ≤-suc-r′ #-}

≤-ascend : n ≤ suc n
≤-ascend = ≤-suc-r ≤-refl

suc≰id : suc n ≰ n
suc≰id (s≤s p) = suc≰id p

instance
  Reflects-suc≰id : Reflects (suc n ≤ n) false
  Reflects-suc≰id = ofⁿ suc≰id
  {-# INCOHERENT Reflects-suc≰id #-}

  Reflects-s≰z : Reflects (suc n ≤ 0) false
  Reflects-s≰z = ofⁿ λ()
  {-# INCOHERENT Reflects-s≰z #-}

s≰z : suc n ≰ 0
s≰z = λ ()

≤-subst : {a b c d : ℕ} → a ＝ b → c ＝ d → a ≤ c → b ≤ d
≤-subst a=b c=d = transport $ ap² (_≤_) a=b c=d


-- Properties of strict order

<-irr : n ≮ n
<-irr (s≤s p) = <-irr p

s<s : m < n → suc m < suc n
s<s = s≤s

<-peel : suc m < suc n → m < n
<-peel = ≤-peel

<-weaken : (x y : ℕ) → x < y → x ≤ y
<-weaken x (suc y) (s≤s p) = ≤-suc-r p

<-trans : {x y z : ℕ} → x < y → y < z → x < z
<-trans x<y y<z = x<y ∙ <-weaken _ _ y<z

≤-<-trans : {x y z : ℕ} → x ≤ y → y < z → x < z
≤-<-trans xy yz = ≤-trans (s≤s xy) yz

<-≤-trans : {x y z : ℕ} → x < y → y ≤ z → x < z
<-≤-trans = ≤-trans

<-weaken-z : (x y : ℕ) → x < y → 0 < y
<-weaken-z x (suc y) (s≤s _) = s≤s z≤

<-asym : ∀[ _<_ ⇒ _≯_ ]
<-asym (s≤s p) (s≤s q) = <-asym p q

<-suc-r : m < n → m < suc n
<-suc-r = ≤-suc-r

<-suc-l : suc m < n → m < n
<-suc-l p = ≤-ascend ∙ p

<-ascend : n < suc n
<-ascend = refl

≮z : n ≮ 0
≮z = false!

z<s : 0 < suc n
z<s = s≤s z≤


-- well-foundedness

<-ind : ∀ {ℓ″} {P : ℕ → 𝒰 ℓ″}
      → (∀ x → (∀ y → y < x → P y) → P x)
      → ∀ x → P x
<-ind {P} ih x = go x (suc x) <-ascend
  where
  go : ∀ m n → m < n → P m
  go m (suc n) (s≤s le) = ih m λ y y<m → go y n (<-≤-trans y<m le)

<-wf : Wf _<_
<-wf = from-induction _<_ λ P → <-ind

-- Addition

≤-+-r : (x y : ℕ) → x ≤ x + y
≤-+-r  zero   y = z≤
≤-+-r (suc x) y = s≤s (≤-+-r x y)

≤-+-l : (x y : ℕ) → x ≤ y + x
≤-+-l x y = subst (x ≤_) (+-comm x y) (≤-+-r x y)

≤-weak-+l : (x y z : ℕ) → x ≤ z → x ≤ y + z
≤-weak-+l x  zero   z p = p
≤-weak-+l x (suc y) z p = ≤-suc-r (≤-weak-+l x y z p)

≤-cong-+ : (m n p q : ℕ) → m ≤ p → n ≤ q → m + n ≤ p + q
≤-cong-+ zero    n  p      q u v = ≤-weak-+l n p q v
≤-cong-+ (suc m) n (suc p) q u v = s≤s (≤-cong-+ m n p q (≤-peel u) v)


-- Subtraction

+∸=id : ∀ m n → m ≤ n → m + (n ∸ m) ＝ n
+∸=id .0        n        z≤              = refl
+∸=id .(suc m) .(suc n) (s≤s {m} {n} le) = ap suc (+∸=id m n le)

suc-pred : (n : ℕ) → n > 0 → n ＝ suc (pred n)
suc-pred (suc _) _ = refl

+-sub : (p q : ℕ) → q ≤ p → p ∸ q + q ＝ p
+-sub  p       zero   qp = +-zero-r p
+-sub (suc p) (suc q) qp = +-suc-r _ _ ∙ ap suc (+-sub p q (≤-peel qp))

≤-sub-lr : (p q r : ℕ) → p ≤ q + r → p ∸ r ≤ q
≤-sub-lr  p      q  zero   pqr = subst (λ x → p ≤ x) (+-zero-r q) pqr
≤-sub-lr  zero   q (suc r) pqr = z≤
≤-sub-lr (suc p) q (suc r) pqr = ≤-sub-lr p q r (≤-peel (subst (λ x → suc p ≤ x) (+-suc-r q r) pqr))

<-sub-lr : (p q r : ℕ) → 0 < q → p < q + r → p ∸ r < q
<-sub-lr p (suc q) r _ pqr = s≤s (≤-sub-lr p q r (≤-peel pqr))


-- Multiplication

≤-·l : (a b c : ℕ) → b ≤ c → a · b ≤ a · c
≤-·l  zero   b c p = z≤
≤-·l (suc a) b c p = ≤-cong-+ b (a · b) c (a · c) p (≤-·l a b c p)

·-inj-r : (x y z : ℕ) → 0 < z → x · z ＝ y · z → x ＝ y
·-inj-r zero y .(suc z) (s≤s {n = z} _) H with (·-zero y (suc z) (sym H))
... | inl prf = sym prf
... | inr prf = false! prf
·-inj-r (suc x) zero .(suc z) (s≤s {n = z} prf) H = false! H
·-inj-r (suc x) (suc y) .(suc z) (s≤s {n = z} prf) H =
  ap suc $ ·-inj-r x y (suc z) (s≤s prf) (+-inj-l z (x · suc z) (y · suc z) (suc-inj H))

·-inj-l : (x y z : ℕ) → 0 < x → x · y ＝ x · z → y ＝ z
·-inj-l x y z 0<x p = ·-inj-r _ _ _ 0<x (·-comm y x ∙ p ∙ ·-comm x z)

z<· : (m n : ℕ) → (0 < m · n) → (0 < m) × (0 < n)
z<· (suc m) zero    0<mn = false! $ subst (0 <_) (·-absorb-r m) 0<mn
z<· (suc _) (suc _) _    = s≤s z≤ , s≤s z≤
