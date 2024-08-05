{-# OPTIONS --safe #-}
-- open import Cat.Functor.Subcategory
open import Categories.Prelude

-- open import Data.Fin.Base hiding (_≤_)

open import Order.Diagram.Meet
--open import Order.Diagram.Glb
open import Order.Diagram.Top
open import Order.Base

-- import Cat.Reasoning

import Order.Diagram.Meet.Reasoning as Meets
import Order.Reasoning

module Order.Semilattice.Meet where

record is-meet-semilattice {o ℓ} (P : Poset o ℓ) : Type (o ⊔ ℓ) where
  field
    _∩_     : ⌞ P ⌟ → ⌞ P ⌟ → ⌞ P ⌟
    ∩-meets : ∀ x y → is-meet P x y (x ∩ y)
    has-top : Top P

  infixr 25 _∩_

  open Order.Reasoning P
  open Meets ∩-meets public
  open Top has-top using (top; !) public

abstract
  is-meet-semilattice-is-prop
    : ∀ {o ℓ} {P : Poset o ℓ}
    → is-prop (is-meet-semilattice P)
  is-meet-semilattice-is-prop {P = P} p q = path where
    open Order.Diagram.Top P using (H-Level-Top)
    open is-meet-semilattice
    module p = is-meet-semilattice p
    module q = is-meet-semilattice q

    meetp : ∀ x y → x p.∩ y ＝ x q.∩ y
    meetp x y = meet-unique (p.∩-meets x y) (q.∩-meets x y)

    path : p ＝ q
    path i ._∩_ x y     = meetp x y i
    path i .∩-meets x y = is-prop→pathᴾ (λ i → hlevel {A = is-meet P x y (meetp x y i)} 1) (p.∩-meets x y) (q.∩-meets x y) i
    path i .has-top     = hlevel {A = Top P} 1 p.has-top q.has-top i

private variable
  o ℓ o' ℓ' : Level
  P Q R : Poset o ℓ

instance
  H-Level-is-meet-semilattice : ∀ {n} → H-Level (suc n) (is-meet-semilattice P)
  H-Level-is-meet-semilattice = hlevel-basic-instance 1 is-meet-semilattice-is-prop

record
  is-meet-slat-hom
    {P : Poset o ℓ} {Q : Poset o' ℓ'} (f : Monotone P Q)
    (P-slat : is-meet-semilattice P) (Q-slat : is-meet-semilattice Q)
    : Type (o ⊔ ℓ')
  where

  no-eta-equality
  private
    module P = Poset P
    module Pₗ = is-meet-semilattice P-slat
    module Q = Order.Reasoning Q
    module Qₗ = is-meet-semilattice Q-slat
    open is-meet

  field
    ∩-≤   : ∀ x y → (f # x) Qₗ.∩ (f # y) Q.≤ f # (x Pₗ.∩ y)
    top-≤ : Qₗ.top Q.≤ f # Pₗ.top

  pres-∩ : ∀ x y → f # (x Pₗ.∩ y) ＝ f # x Qₗ.∩ f # y
  pres-∩ x y =
    Q.≤-antisym
      (Qₗ.∩-universal (f # (x Pₗ.∩ y))
        (f .pres-≤ Pₗ.∩≤l)
        (f .pres-≤ Pₗ.∩≤r))
      (∩-≤ x y)

  pres-top : f # Pₗ.top ＝ Qₗ.top
  pres-top = Q.≤-antisym Qₗ.! top-≤

  pres-meets
    : ∀ {x y m}
    → is-meet P x y m
    → is-meet Q (f # x) (f # y) (f # m)
  pres-meets meet .is-meet.meet≤l = f .pres-≤ (meet .meet≤l)
  pres-meets meet .is-meet.meet≤r = f .pres-≤ (meet .meet≤r)
  pres-meets {x = x} {y = y} {m = m} meet .is-meet.greatest ub ub≤fx ub≤fy =
    ub                   Q.≤⟨ Qₗ.∩-universal ub ub≤fx ub≤fy ⟩
    (f # x) Qₗ.∩ (f # y) Q.≤⟨ ∩-≤ x y ⟩
    f # (x Pₗ.∩ y)       Q.≤⟨ f .pres-≤ (meet .greatest (x Pₗ.∩ y) Pₗ.∩≤l Pₗ.∩≤r) ⟩
    f # m                ∎

  pres-tops
    : ∀ {t}
    → is-top P t
    → is-top Q (f # t)
  pres-tops {t = t} t-top x =
    x          Q.≤⟨ Qₗ.! ⟩
    Qₗ.top     Q.≤⟨ top-≤ ⟩
    f # Pₗ.top Q.≤⟨ f .pres-≤ (t-top Pₗ.top) ⟩
    f # t      ∎

open is-meet-slat-hom

unquoteDecl H-Level-is-meet-slat-hom = declare-record-hlevel 1 H-Level-is-meet-slat-hom (quote is-meet-slat-hom)

{-
id-meet-slat-hom
  : ∀ (Pₗ : is-meet-semilattice P)
  → is-meet-slat-hom idₘ Pₗ Pₗ
id-meet-slat-hom {P = P} _ .∩-≤ _ _ = Poset.≤-refl P
id-meet-slat-hom {P = P} _ .top-≤ = Poset.≤-refl P

∘-meet-slat-hom
  : ∀ {Pₗ Qₗ Rₗ} {f : Monotone Q R} {g : Monotone P Q}
  → is-meet-slat-hom f Qₗ Rₗ
  → is-meet-slat-hom g Pₗ Qₗ
  → is-meet-slat-hom (f ∘ₘ g) Pₗ Rₗ
∘-meet-slat-hom {R = R} {f = f} {g = g} f-pres g-pres .∩-≤ x y =
  R .Poset.≤-trans (f-pres .∩-≤ (g # x) (g # y)) (f .pres-≤ (g-pres .∩-≤ x y))
∘-meet-slat-hom {R = R} {f = f} {g = g} f-pres g-pres .top-≤ =
  R .Poset.≤-trans (f-pres .top-≤) (f .pres-≤ (g-pres .top-≤))

Meet-slats-subcat : ∀ o ℓ → Subcat (Posets o ℓ) (o ⊔ ℓ) (o ⊔ ℓ)
Meet-slats-subcat o ℓ .Subcat.is-ob = is-meet-semilattice
Meet-slats-subcat o ℓ .Subcat.is-hom = is-meet-slat-hom
Meet-slats-subcat o ℓ .Subcat.is-hom-prop _ _ _ = hlevel 1
Meet-slats-subcat o ℓ .Subcat.is-hom-id = id-meet-slat-hom
Meet-slats-subcat o ℓ .Subcat.is-hom-∘ = ∘-meet-slat-hom

Meet-slats : ∀ o ℓ → Precategory (lsuc o ⊔ lsuc ℓ) (o ⊔ ℓ)
Meet-slats o ℓ = Subcategory (Meet-slats-subcat o ℓ)

module Meet-slats {o} {ℓ} = Cat.Reasoning (Meet-slats o ℓ)

Meet-semilattice : ∀ o ℓ → Type _
Meet-semilattice o ℓ = Meet-slats.Ob {o} {ℓ}
-}
