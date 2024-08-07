{-# OPTIONS --safe #-}
module Data.Nat.Order.Base where

open import Meta.Prelude

open import Logic.Decidability

open import Data.Dec.Base as Dec
open import Data.Empty.Base as ⊥
open import Data.Reflects.Base as Reflects
open import Data.Empty.Properties
open import Data.Sum.Base
open import Data.Sum.Path
open import Data.Wellfounded.Base

open import Data.Bool.Base
open import Data.Nat.Base
open import Data.Nat.Order.Inductive.Base
  using ( _≤ᵇ_ ; _<ᵇ_ ; _≥ᵇ_ ; _>ᵇ_
        ; _≰ᵇ_ ; _≮ᵇ_ ; _≱ᵇ_ ; _≯ᵇ_
        )
open import Data.Nat.Path
open import Data.Nat.Properties
open import Data.Nat.Solver

private variable
  m n k : ℕ

infix 3 _≤_ _<_ _≥_ _>_
        _≰_ _≮_ _≱_ _≯_

opaque
  _≤_ _<_ : Corr _ (ℕ , ℕ) 0ℓ

  m ≤ n = Σ[ k ꞉ ℕ ] (m + k ＝ n)
  m < n = suc m ≤ n

_≥_ _>_ _≰_ _≮_ _≱_ _≯_ : Corr _ (ℕ , ℕ) 0ℓ

m ≥ n =   n ≤ m
m > n =   n < m
m ≰ n = ¬ m ≤ n
m ≮ n = ¬ m < n
m ≱ n = ¬ m ≥ n
m ≯ n = ¬ m > n


opaque
  unfolding _≤_

  ≤-is-prop : is-prop (m ≤ n)
  ≤-is-prop (_ , p) (_ , q) = Σ-prop-path! (+-inj-l _ _ _ (p ∙ q ⁻¹))

  <-is-prop : is-prop (m < n)
  <-is-prop = ≤-is-prop

instance opaque
  H-Level-≤ : ⦃ k ≥ʰ 1 ⦄ → H-Level k (m ≤ n)
  H-Level-≤ ⦃ s≤ʰs _ ⦄ = hlevel-prop-instance ≤-is-prop
  {-# INCOHERENT H-Level-≤ #-}

  H-Level-< : ⦃ k ≥ʰ 1 ⦄ → H-Level k (m < n)
  H-Level-< ⦃ s≤ʰs _ ⦄ = hlevel-prop-instance <-is-prop
  {-# INCOHERENT H-Level-< #-}

-- Properties of order

opaque
  unfolding _≤_

  z≤ : 0 ≤ n
  z≤ = _ , refl

  s≤s : m ≤ n → suc m ≤ suc n
  s≤s = second (ap suc)

  ≤-peel : suc m ≤ suc n → m ≤ n
  ≤-peel = second suc-inj

  ≤-peel-unpeel : (p : suc m ≤ suc n) → s≤s (≤-peel p) ＝ p
  ≤-peel-unpeel (_ , _) = refl ,ₚ prop!

  ≤-refl : n ≤ n
  ≤-refl = 0 , nat!

  ≤-trans : m ≤ n → n ≤ k → m ≤ k
  ≤-trans {k} (δ₁ , p) (δ₂ , q)
    = δ₁ + δ₂
    , nat! ∙ subst (λ φ → φ + δ₂ ＝ k) (symₚ p) q

  ≤-antisym : m ≤ n → n ≤ m → m ＝ n
  ≤-antisym (0      , p) (_      , _) = sym (+-zero-r _) ∙ p
  ≤-antisym (suc _  , _) (0      , q) = sym q ∙ +-zero-r _
  ≤-antisym {m} (suc δ₁ , p) (suc δ₂ , q) = ⊥.rec $ suc≠zero {m = δ₁ + suc δ₂} $ +-inj-l m _ 0 $
       +-assoc m (suc δ₁) (suc δ₂) ∙ subst (λ φ → φ + suc δ₂ ＝ m) (sym p) q ∙ nat!

  ≤-suc-r : m ≤ n → m ≤ suc n
  ≤-suc-r = bimap suc λ p → nat! ∙ ap suc p

  ≤-ascend : n ≤ suc n
  ≤-ascend = 1 , nat!

  suc≰id : suc n ≰ n
  suc≰id (k , p) = id≠plus-suc {m = k} (sym p ∙ nat!)

  s≰z : suc n ≰ 0
  s≰z = suc≠zero ∘ snd

  ≤-subst : {a b c d : ℕ} → a ＝ b → c ＝ d → a ≤ c → b ≤ d
  ≤-subst a=b c=d = second $ subst² (λ u v → u + _ ＝ v) a=b c=d

=→≤ : m ＝ n → m ≤ n
=→≤ {m} {n} e = subst (m ≤_) e ≤-refl

≤≃≤+l : (n ≤ k) ≃ (m + n ≤ m + k)
≤≃≤+l {n} {k} {m} = prop-extₑ! (ff m n k) (gg m n k)
  where
  ff : (a b c : ℕ) → b ≤ c → a + b ≤ a + c
  ff zero    b c p = p
  ff (suc a) b c p = s≤s (ff a b c p)

  gg : (a b c : ℕ) → a + b ≤ a + c → b ≤ c
  gg  zero   b c p = p
  gg (suc a) b c p = gg a b c (≤-peel p)

≤≃≤+r : (n ≤ k) ≃ (n + m ≤ k + m)
≤≃≤+r {n} {k} {m} = ≤≃≤+l ∙ subst (λ q → q ≤ m + k ≃ n + m ≤ k + m) (+-comm n m)
                             (subst (λ q → n + m ≤ q ≃ n + m ≤ k + m) (+-comm k m) refl)

-- Properties of strict order

opaque
  unfolding _<_

  <-irr : n ≮ n
  <-irr = (λ p → id≠plus-suc (sym p ∙ nat!)) ∘ snd

  s<s : m < n → suc m < suc n
  s<s = s≤s

  <-peel : suc m < suc n → m < n
  <-peel = ≤-peel

  <-weaken : (x y : ℕ) → x < y → x ≤ y
  <-weaken x y (δ , p) = suc δ , nat! ∙ p

  <-trans : m < n → n < k → m < k
  <-trans (δ₁ , p) (δ₂ , q)
    = suc (δ₁ + δ₂)
    , nat! ∙ subst (λ φ → suc (φ + δ₂) ＝ _) (symₚ p) q

  <-asym : ∀[ _<_ ⇒ _≯_ ]
  <-asym {x = m} {x = n} (δ₁ , p) (δ₂ , q) = id≠plus-suc {n = n} {m = 1 + δ₂ + δ₁}
    (subst (λ φ → suc (φ + δ₁) ＝ n) (symₚ q) p ⁻¹ ∙ nat!)

  <-suc-r : m < n → m < suc n
  <-suc-r = ≤-suc-r

  <-suc-l : suc m < n → m < n
  <-suc-l (δ , p) = suc δ , nat! ∙ p

  <-ascend : n < suc n
  <-ascend = 0 , +-zero-r _

  ≮z : n ≮ 0
  ≮z = s≰z

  z<s : 0 < suc n
  z<s = _ , refl

opaque
  unfolding _≤_ _<_
  <≃<+l : (n < k) ≃ (m + n < m + k)
  <≃<+l {n} {k} {m} = ≤≃≤+l {n = suc n}
                    ∙ subst (λ q → q ≤ m + k ≃ m + n < m + k) (+-suc-r m n ⁻¹) refl

  <≃<+r : (n < k) ≃ (n + m < k + m)
  <≃<+r {n} = ≤≃≤+r {n = suc n}

  ≤-<-trans : {x y z : ℕ} → x ≤ y → y < z → x < z
  ≤-<-trans p = ≤-trans (s≤s p)

-- Conversion

opaque
  unfolding _<_
  <→≤ : ∀[ _<_ ⇒ _≤_ ]
  <→≤ = bimap suc (nat! ∙_)

  <→≠ : ∀[ _<_ ⇒ _≠_ ]
  <→≠ m<n m=n = <-irr (subst (_ <_) (sym m=n) m<n)

  ≤→≯ : ∀[ _≤_ ⇒ _≯_ ]
  ≤→≯ {x = m} {x = n} (δ₁ , p) (δ₂ , q) = id≠plus-suc {m} {δ₁ + δ₂} $
    subst (λ φ → suc (φ + δ₂) ＝ m) (symₚ p) q ⁻¹ ∙ nat!

  ≤→<⊎= : ∀[ _≤_ ⇒ _<_ ⊎ _＝_ ]
  ≤→<⊎= (0     , p) = inr $ nat! ∙ p
  ≤→<⊎= (suc δ , p) = inl $ δ , nat! ∙ p

  <⊎=→≤ : ∀[ _<_ ⊎ _＝_ ⇒ _≤_ ]
  <⊎=→≤ (inl m<n) = <→≤ m<n
  <⊎=→≤ (inr m=n) = subst (_≤ _) (sym m=n) ≤-refl

<→≱ : ∀[ _<_ ⇒ _≱_ ]
<→≱ m<n m≥n = ≤→≯ m≥n m<n

≯→≤ : ∀[ _≯_ ⇒ _≤_ ]
≯→≤ {0}     {_}     _ = z≤
≯→≤ {suc _} {0}     f = ⊥.rec $ f z<s
≯→≤ {suc _} {suc _} f = s≤s $ ≯→≤ (f ∘ s<s)

≱→< : ∀[ _≱_ ⇒ _<_ ]
≱→< {_}     {0}     f = ⊥.rec $ f z≤
≱→< {0}     {suc _} _ = z<s
≱→< {suc m} {suc n} f = s<s $ ≱→< (f ∘ s≤s)

opaque
  unfolding _<_
  <≃suc≤ : (suc m ≤ n) ≃ (m < n)
  <≃suc≤ = refl

  ≤≃<suc : (m ≤ n) ≃ (m < suc n)
  ≤≃<suc = Σ-ap-snd λ x → s＝s≃

≤≃≯ : (m ≤ n) ≃ (m ≯ n)
≤≃≯ = prop-extₑ! ≤→≯ ≯→≤

<≃≱ : (m < n) ≃ (m ≱ n)
<≃≱ = prop-extₑ! <→≱ ≱→<

≤≃<⊎= : (m ≤ n) ≃ ((m < n) ⊎ (m ＝ n))
≤≃<⊎= = prop-extₑ (hlevel 1) (disjoint-⊎-is-prop! (<→≠ $ₜ²_)) ≤→<⊎= <⊎=→≤


-- Decidability

<-reflects : Reflects _<_ _<ᵇ_
<-reflects _       0       = ofⁿ ≮z
<-reflects 0       (suc _) = ofʸ z<s
<-reflects (suc m) (suc n) =
  Reflects.dmap s<s (_∘ <-peel) $ <-reflects m n

<-dec : Decidable _<_
<-dec = reflects→decidable {2} {P = _<_} <-reflects

≤-reflects : Reflects _≤_ _≤ᵇ_
≤-reflects 0       _       = ofʸ z≤
≤-reflects (suc _) 0       = ofⁿ s≰z
≤-reflects (suc m) (suc n) =
  Reflects.dmap s≤s (_∘ ≤-peel) $ ≤-reflects m n

≤-dec : Decidable _≤_
≤-dec = reflects→decidable {2} {P = _≤_} ≤-reflects

-- TODO use trichotomy
≤-split : Π[ _<_ ⊎ _>_ ⊎ _＝_ ]
≤-split m n with <-dec {m} {n}
... | yes m<n = inl m<n
... | no  m≮n with <-dec {n} {m}
... | yes n<m = inr $ inl n<m
... | no  n≮m = inr $ inr $ ≤-antisym (≤≃≯ ⁻¹ $ n≮m) (≤≃≯ ⁻¹ $ m≮n)

-- well-foundedness

opaque
  unfolding _<_
  <-ind : ∀ {ℓ″} {P : ℕ → 𝒰 ℓ″}
        → (∀ x → (∀ y → y < x → P y) → P x)
        → ∀ x → P x
  <-ind {P} ih x = go x (suc x) <-ascend
    where
    go : ∀ m n → m < n → P m
    go m  zero   m<n     = ⊥.rec $ ≮z m<n
    go m (suc n) (q , e) = ih m λ y y<m → go y n (≤-trans y<m (q , suc-inj e))

<-wf : Wf _<_
<-wf = from-induction _<_ λ P → <-ind

-- addition

opaque
  unfolding _≤_
  ≤-+-r : m ≤ m + n
  ≤-+-r {m} {n} = n , refl

≤-+-l : m ≤ n + m
≤-+-l {m} {n} = subst (m ≤_) (+-comm m n) ≤-+-r

opaque
  unfolding _<_
  <-+-lr : m < suc n + m
  <-+-lr {m} {n} = n , ap suc (+-comm m n)

≤-+ : ∀ {m n p q} → m ≤ p → n ≤ q → m + n ≤ p + q
≤-+ m≤p n≤q = ≤-trans (≤≃≤+r .fst m≤p) (≤≃≤+l .fst n≤q)

-- subtraction

m+[n∸m] : ∀ m n → m ≤ n → m + (n ∸ m) ＝ n
m+[n∸m]  zero    n      m≤n = refl
m+[n∸m] (suc m)  zero   m≤n = absurd (s≰z m≤n)
m+[n∸m] (suc m) (suc n) m≤n = ap suc (m+[n∸m] m n (≤-peel m≤n))

[n∸m]+m : ∀ m n → m ≤ n → (n ∸ m) + m ＝ n
[n∸m]+m m n m≤n = +-comm (n ∸ m) m ∙ m+[n∸m] m n m≤n

m+[n∸p]＝m+n∸p : ∀ m n p → p ≤ n → m + (n ∸ p) ＝ m + n ∸ p
m+[n∸p]＝m+n∸p m n p p≤n =
    sym (+-cancel-∸-r (m + (n ∸ p)) p)
  ∙ ap (_∸ p) (sym (+-assoc m (n ∸ p) p))
  ∙ ap (λ q → m + q ∸ p) (+-comm (n ∸ p) p ∙ m+[n∸m] p n p≤n)

m∸n+p＝m+p∸n : ∀ m n p → n ≤ m → m ∸ n + p ＝ m + p ∸ n
m∸n+p＝m+p∸n m n p n≤m = +-comm (m ∸ n) p
                      ∙ m+[n∸p]＝m+n∸p p m n n≤m
                      ∙ ap (_∸ n) (+-comm p m)

m∸[n∸p]＝m+p∸n : ∀ m n p → p ≤ n → m ∸ (n ∸ p) ＝ m + p ∸ n
m∸[n∸p]＝m+p∸n m n p p≤n = sym (∸-cancel-+-r m p (n ∸ p)) ∙ ap ((m + p) ∸_) ([n∸m]+m p n p≤n)

m∸[n∸p]＝m∸n+p : ∀ m n p → p ≤ n → n ≤ m → m ∸ (n ∸ p) ＝ m ∸ n + p
m∸[n∸p]＝m∸n+p m n p p≤n n≤m = m∸[n∸p]＝m+p∸n m n p p≤n ∙ sym (m∸n+p＝m+p∸n m n p n≤m)

suc-∸ : ∀ m n → m ≤ n → suc (n ∸ m) ＝ (suc n) ∸ m
suc-∸ m n = m+[n∸p]＝m+n∸p 1 n m

∸=0→≤ : m ∸ n ＝ 0 → m ≤ n
∸=0→≤ {m = zero}              _ = z≤
∸=0→≤ {m = suc m} {n = zero}  e = absurd (suc≠zero e)
∸=0→≤ {m = suc m} {n = suc n} e = s≤s (∸=0→≤ {m} {n} e)

opaque
  unfolding _≤_
  ≤→∸=0 : m ≤ n → m ∸ n ＝ 0
  ≤→∸=0 {m} (k , e) = ap (m ∸_) (sym e) ∙ ∸-+-assoc m m k ∙ ap (_∸ k) (∸-cancel m) ∙ ∸-zero-l k

∸=0≃≤ : (m ∸ n ＝ 0) ≃ (m ≤ n)
∸=0≃≤ = prop-extₑ! ∸=0→≤ ≤→∸=0

∸≤≃≤+ : ∀ {m n p} → (m ∸ n ≤ p) ≃ (m ≤ n + p)
∸≤≃≤+ {m} {n} {p} = ∸=0≃≤ ⁻¹ ∙ whisker-path-lₑ (sym (∸-+-assoc n m p)) ∙ ∸=0≃≤

≤-∸-l-≃ : ∀ {m n p} → (m ∸ n ≤ p) ≃ (m ∸ p ≤ n)
≤-∸-l-≃ {m} {n} {p} = ∸≤≃≤+ ∙ subst (λ q → m ≤ n + p ≃ m ≤ q) (+-comm n p) refl ∙ ∸≤≃≤+ ⁻¹

<-∸-r-≃ : ∀ {m n p} → (n < p ∸ m) ≃ (m + n < p)
<-∸-r-≃ {m} {n} {p} = <≃≱ ∙ ¬-≃ (∸≤≃≤+ .fst) ((∸≤≃≤+ ⁻¹) .fst) ∙ <≃≱ ⁻¹

≤-∸-r-≃ : ∀ {m n p} → 0 < n → (n ≤ p ∸ m) ≃ (m + n ≤ p)
≤-∸-r-≃     {n = zero}      n>0 = absurd (≮z n>0)
≤-∸-r-≃ {m} {n = suc n} {p} n>0 = <≃suc≤ ∙ <-∸-r-≃ ∙ <≃suc≤ ⁻¹
                                ∙ subst (λ q → q ≤ p ≃ m + suc n ≤ p) (+-suc-r m n) refl

<-∸-l-≃ : ∀ {m n p} → 0 < p → (m ∸ n < p) ≃ (m < n + p)
<-∸-l-≃         {p = zero}  p>0 = absurd (≮z p>0)
<-∸-l-≃ {m} {n} {p = suc p} p>0 = <≃suc≤ ⁻¹ ∙ ≤≃≤+l {m = 1} ⁻¹ ∙ ∸≤≃≤+ {m} {n} ∙ ≤≃≤+l
                                ∙ subst (λ q → suc m ≤ q ≃ suc m ≤ n + suc p) (+-suc-r n p) refl ∙ <≃suc≤

opaque
  unfolding _≤_
  ≤→Σ : ∀ m n → m ≤ n → Σ[ k ꞉ ℕ ] (m + k ＝ n)
  ≤→Σ m n = id
