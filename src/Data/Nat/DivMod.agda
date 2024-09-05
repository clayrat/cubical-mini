{-# OPTIONS --safe #-}
module Data.Nat.DivMod where

open import Foundations.Base
open import Foundations.Equiv
open import Foundations.HLevel
open import Meta.Marker
open import Data.Nat.Base renaming (div-helper to divₕ; mod-helper to modₕ)
open import Data.Nat.Path
open import Data.Nat.Order.Base
open import Data.Empty.Base
open import Data.Sum.Base
open import Data.Nat.Properties
open import Data.Reflects.Base

infix 4 _∣_
infixl 7 _/_
infixl 7 _%_

-- division (rounding down)

opaque
  _/_ : ℕ → ℕ → ℕ
  m /  zero   = 0
  m / (suc n) = divₕ 0 n m n

-- modulo

opaque
  _%_ : ℕ → ℕ → ℕ
  m %  zero   = m
  m % (suc n) = modₕ 0 n m n

-- divisibility

record _∣_ (m n : ℕ) : 𝒰 where
  constructor divides
  field quot  : ℕ
        proof : n ＝ quot · m

-- helper properties
-- TODO: move

div-mod-lemma : ∀ am ad d n
              → am + ad · suc (am + n) + d ＝ modₕ am (am + n) d n + divₕ ad (am + n) d n · suc (am + n)
div-mod-lemma am ad  zero    n      = +-zero-r (am + ad · suc (am + n))
div-mod-lemma am ad (suc d)  zero   =
    ap (λ q → am + ad · suc q + suc d) (+-zero-r am)
  ∙ +-suc-r (am + ad · suc am) d
  ∙ div-mod-lemma 0 (suc ad) d am
  ∙ ap (λ q → modₕ 0 q d q + divₕ (suc ad) q d q · suc q) (sym $ +-zero-r am)
div-mod-lemma am ad (suc d) (suc n) =
    ap (λ q → am + ad · suc q + suc d) (+-suc-r am n)
  ∙ +-suc-r (am + ad · suc (suc (am + n))) d
  ∙ div-mod-lemma (suc am) ad d n
  ∙ ap (λ q → modₕ (suc am) q d n + divₕ ad q d n · suc q) (sym $ +-suc-r am n)

modₕ-skipTo0 : ∀ acc n a b → modₕ acc n (b + a) a ＝ modₕ (a + acc) n b 0
modₕ-skipTo0 acc n  zero   b = ap (λ q → modₕ acc n q 0) (+-zero-r b)
modₕ-skipTo0 acc n (suc a) b =
    ap (λ q → modₕ acc n q (suc a)) (+-suc-r b a)
  ∙ modₕ-skipTo0 (suc acc) n a b
  ∙ ap (λ q → modₕ q n b 0) (+-suc-r a acc)

n[modₕ]n≡0 : ∀ acc v → modₕ acc (acc + v) (suc v) v ＝ 0
n[modₕ]n≡0 acc v = modₕ-skipTo0 acc (acc + v) v 1

a≤n⇒a[modₕ]n≡a : ∀ acc n a b → modₕ acc n a (a + b) ＝ acc + a
a≤n⇒a[modₕ]n≡a acc n  zero   b = sym (+-zero-r acc)
a≤n⇒a[modₕ]n≡a acc n (suc a) b = a≤n⇒a[modₕ]n≡a (suc acc) n a b ∙ sym (+-suc-r acc a)

modₕ-idem : ∀ acc a n → modₕ 0 (acc + n) (modₕ acc (acc + n) a n) (acc + n) ＝ modₕ acc (acc + n) a n
modₕ-idem acc  zero    n      = a≤n⇒a[modₕ]n≡a zero (acc + n) acc n
modₕ-idem acc (suc a)  zero   =
    ap (λ q → modₕ 0 q (modₕ 0 q a q) q) (+-zero-r acc)
  ∙ modₕ-idem 0 a acc
  ∙ ap (λ q → modₕ 0 q a q) (+-zero-r acc ⁻¹)
modₕ-idem acc (suc a) (suc n) =
    ap (λ q → modₕ 0 q (modₕ (suc acc) q a n) q) (+-suc-r acc n)
  ∙ modₕ-idem (suc acc) a n
  ∙ ap (λ q → modₕ (suc acc) q a n) (+-suc-r acc n ⁻¹)

a+n[modₕ]n≡a[modₕ]n : ∀ acc a n → modₕ acc (acc + n) (acc + a + suc n) n ＝ modₕ acc (acc + n) a n
a+n[modₕ]n≡a[modₕ]n acc  zero    n      =
  modₕ acc (acc + n) (⌜ acc + 0 ⌝ + suc n) n
   =⟨ ap! (+-zero-r acc) ⟩
  modₕ acc (acc + n) ⌜ acc + suc n ⌝ n
   =⟨ ap! (+-suc-r acc n) ⟩
  modₕ acc (acc + n) (suc (acc + n)) n
   =⟨ modₕ-skipTo0 acc (acc + n) n (suc acc) ⟩
  modₕ (acc + n) (acc + n) (suc acc) 0
   =⟨⟩
  modₕ 0 (acc + n) acc (acc + n)
   =⟨ a≤n⇒a[modₕ]n≡a 0 (acc + n) acc n ⟩
  acc
   ∎
a+n[modₕ]n≡a[modₕ]n acc (suc a)  zero   =
  modₕ acc ⌜ acc + 0 ⌝ (acc + suc a + 1) 0
    =⟨ ap! (+-zero-r acc) ⟩
  modₕ acc acc ⌜ acc + suc a + 1 ⌝ 0
    =⟨ ap! (+-comm (acc + suc a) 1) ⟩
  modₕ acc acc (1 + (acc + suc a)) 0
    =⟨⟩
  modₕ 0 acc ⌜ acc + suc a ⌝ acc
    =⟨ ap! (+-suc-r acc a ∙ ap suc (+-comm acc a) ∙ (+-suc-r a acc) ⁻¹) ⟩
  modₕ 0 acc (a + suc acc) acc
    =⟨ a+n[modₕ]n≡a[modₕ]n 0 a acc ⟩
  modₕ 0 acc a acc
    =⟨ ap (λ q → modₕ 0 q a q) (+-zero-r acc) ⁻¹ ⟩
  modₕ 0 (acc + 0) a (acc + 0)
    ∎
a+n[modₕ]n≡a[modₕ]n acc (suc a) (suc n) =
  modₕ acc ⌜ acc + suc n ⌝ (acc + suc a + suc (suc n)) (suc n)
    =⟨ ap! (+-suc-r acc n) ⟩
  mod₁ (acc + suc a + (2 + n)) (suc n)
    =⟨ ap (λ v → mod₁ (v + suc (suc n)) (suc n)) (+-suc-r acc a) ⟩
  mod₁ (suc acc + a + (2 + n)) (suc n)
    =⟨⟩
  mod₂ ⌜ acc + a + (2 + n) ⌝   n
    =⟨ ap! (+-suc-r (acc + a) (1 + n)) ⟩
  mod₂ (suc acc + a + suc n)   n
    =⟨ a+n[modₕ]n≡a[modₕ]n (suc acc) a n ⟩
  modₕ (suc acc) ⌜ suc acc + n ⌝ a n
    =⟨ ap! (+-suc-r acc n ⁻¹) ⟩
  modₕ (suc acc) (acc + suc n) a n
    ∎
  where
  mod₁ = modₕ acc       (suc acc + n)
  mod₂ = modₕ (suc acc) (suc acc + n)


-- properties

opaque
  unfolding _/_ _%_
  0-div-0 : ∀ n → 0 / n ＝ 0
  0-div-0  zero   = refl
  0-div-0 (suc n) = refl

  0-mod-0 : ∀ n → 0 % n ＝ 0
  0-mod-0  zero   = refl
  0-mod-0 (suc n) = refl

  m≡m%n+[m/n]*n : ∀ m n → m ＝ m % n + (m / n) · n
  m≡m%n+[m/n]*n m  zero   = sym $ +-zero-r m
  m≡m%n+[m/n]*n m (suc n) = div-mod-lemma 0 0 m n

  m%n≡m∸m/n*n : ∀ m n → m % n ＝ m ∸ (m / n) · n
  m%n≡m∸m/n*n m n =
    m % n
      =⟨ +-cancel-∸-r (m % n) ((m / n) · n ) ⟨
    m % n + m / n · n ∸ m / n · n
      =⟨ ap (_∸ m / n · n) (m≡m%n+[m/n]*n m n) ⟨
    m ∸ (m / n) · n
      ∎

  [m/n]*n＝ : ∀ m n → (m / n) · n ＝ m ∸ m % n
  [m/n]*n＝ m n = sym (+-cancel-∸-r (m / n · n) (m % n))
                ∙ ap (_∸ m % n) (+-comm (m / n · n) (m % n) ∙ sym (m≡m%n+[m/n]*n m n))

  n%n＝0 : ∀ n → n % n ＝ 0
  n%n＝0  zero   = refl
  n%n＝0 (suc n) = n[modₕ]n≡0 0 n

  m%n%n≡m%n : ∀ m n → m % n % n ＝ m % n
  m%n%n≡m%n m  zero     = refl
  m%n%n≡m%n m (suc n-1) = modₕ-idem 0 m n-1

  [m+n]%n≡m%n : ∀ m n → (m + n) % n ＝ m % n
  [m+n]%n≡m%n m  zero       = +-zero-r m
  [m+n]%n≡m%n m n@(suc n-1) = a+n[modₕ]n≡a[modₕ]n 0 m n-1

  [m+kn]%n≡m%n : ∀ m k n → (m + k · n) % n ＝ m % n
  [m+kn]%n≡m%n m  k         zero     = ap (m +_) (·-absorb-r k) ∙ +-zero-r m
  [m+kn]%n≡m%n m  zero   n@(suc n-1) = ap (_% n) (+-zero-r m)
  [m+kn]%n≡m%n m (suc k) n@(suc n-1) =
    (m + (n + k · n)) % n
      =⟨ ap (_% n) (+-assoc m n (k · n)) ⟩
    (m + n + k · n)   % n
      =⟨ [m+kn]%n≡m%n (m + n) k n ⟩
    (m + n)           % n
      =⟨ [m+n]%n≡m%n m n ⟩
    m                 % n
      ∎

  [kn]%n≡0 : ∀ m d → (m · d) % d ＝ 0
  [kn]%n≡0 m d = [m+kn]%n≡m%n 0 m d ∙ 0-mod-0 d

  %-distribˡ-+ : ∀ m n d → (m + n) % d ＝ ((m % d) + (n % d)) % d
  %-distribˡ-+ m n    zero     = refl
  %-distribˡ-+ m n d@(suc d-1) =
    (⌜ m ⌝ + n) % d
      =⟨ ap! (m≡m%n+[m/n]*n m d) ⟩
    ⌜ m % d + (m / d) · d + n ⌝ % d
      =⟨ ap! (+-assoc-comm (m % d) ((m / d) · d) n) ⟩
    (m % d + n + ((m / d) · d)) % d
      =⟨ [m+kn]%n≡m%n (m % d + n) (m / d) d ⟩
    (m % d + ⌜ n ⌝) % d
      =⟨ ap! (m≡m%n+[m/n]*n n d) ⟩
    ⌜ m % d + (n % d + (n / d) · d) ⌝ % d
      =⟨ ap! (+-assoc (m % d) (n % d) ((n / d) · d)) ⟩
    (m % d + n % d + (n / d) · d) % d
      =⟨ [m+kn]%n≡m%n (m % d + n % d) (n / d) d ⟩
    (m % d + n % d) % d
      ∎

∣-is-prop : ∀ m n → m ≠ 0 → is-prop (m ∣ n)
∣-is-prop m n m≠0 = go
  where
  go : (p q : m ∣ n) → p ＝ q
  go (divides q₁ prf₁) (divides q₂ prf₂) =
    ap² divides
      ([ id , (λ m=0 → absurd (m≠0 m=0)) ]ᵤ (·-cancel-r q₁ q₂ m (sym prf₁ ∙ prf₂)))
      (to-pathᴾ (hlevel 2 n _ _ prf₂))

¬0∣suc : ∀ n → ¬ (0 ∣ suc n)
¬0∣suc n (divides q pf) = absurd (false! (pf ∙ ·-absorb-r q))

∣→≤ : ∀ m n → n ≠ 0 → m ∣ n → m ≤ n
∣→≤ m    zero     n≠0  mn                  = absurd (n≠0 refl)
∣→≤ m   (suc n)   n≠0 (divides  zero   pf) = absurd (false! pf)
∣→≤ m n@(suc n-1) n≠0 (divides (suc q) pf) = ≤-trans ≤-+-r (subst (_≤ n) pf ≤-refl)

∣-refl : ∀ n → n ∣ n
∣-refl n = divides 1 (sym $ ·-id-l n)

∣-trans : ∀ m n p → m ∣ n → n ∣ p → m ∣ p
∣-trans m n p (divides qm prfm) (divides qn prfn) =
  divides (qn · qm) (prfn ∙ ap (qn ·_) prfm ∙ ·-assoc qn qm m)

∣-antisym : ∀ m n → m ∣ n → n ∣ m → m ＝ n
∣-antisym  zero    n     (divides q prf) n∣m = sym (prf ∙ ·-absorb-r q)
∣-antisym (suc m)  zero   m∣n            n∣m = absurd (¬0∣suc m n∣m)
∣-antisym (suc m) (suc n) m∣n            n∣m =
  ≤-antisym (∣→≤ (suc m) (suc n) false! m∣n) (∣→≤ (suc n) (suc m) false! n∣m)

_∣0 : ∀ n → n ∣ 0
n ∣0 = divides 0 refl

%=0→∣ : ∀ m d → m % d ＝ 0 → d ∣ m
%=0→∣ m d e ._∣_.quot  = m / d
%=0→∣ m d e ._∣_.proof = m≡m%n+[m/n]*n m d ∙ ap (_+ m / d · d) e

∣→%=0 : ∀ m d → d ∣ m → m % d ＝ 0
∣→%=0 m d (divides q pf) = ap (_% d) pf ∙ [kn]%n≡0 q d

∣n∣m%n⇒∣m : ∀ {m n d} → d ∣ n → d ∣ m % n → d ∣ m
∣n∣m%n⇒∣m {m} {n} {d} (divides q prf) (divides qm prfm) =
  divides (qm + (m / n) · q)
    (m
      =⟨ m≡m%n+[m/n]*n m n ⟩
     ⌜ m % n ⌝ + m / n · n
      =⟨ ap! prfm ⟩
     qm · d + m / n · ⌜ n ⌝
      =⟨ ap! prf ⟩
     qm · d + ⌜ m / n · (q · d) ⌝
      =⟨ ap! (·-assoc (m / n) q d) ⟩
     qm · d + m / n · q · d
      =⟨ ·-distrib-+-r qm (m / n · q) d ⟨
    (qm + m / n · q) · d
      ∎)

%-presˡ-∣ : ∀ {m n d} → d ∣ m → d ∣ n → d ∣ m % n
%-presˡ-∣ {m} {n} {d} (divides qm prfm) (divides qn prfn) =
  divides (qm ∸ m / n · qn)
    (m % n
       =⟨ m%n≡m∸m/n*n m n ⟩
     m ∸ m / n · ⌜ n ⌝
       =⟨ ap! prfn ⟩
     m ∸ ⌜ m / n · (qn · d) ⌝
       =⟨ ap! (·-assoc (m / n) qn d) ⟩
     ⌜ m ⌝ ∸ m / n · qn · d
       =⟨ ap! prfm ⟩
     qm · d ∸ m / n · qn · d
       =⟨ ·-distrib-∸-r qm (m / n · qn) d ⟨
     (qm ∸ m / n · qn) · d
       ∎)
