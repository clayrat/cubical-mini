{-# OPTIONS --safe #-}
module Order.Complemented where

open import Cat.Prelude
open import Order.Base
open import Order.Strict
open import Order.Total
open import Order.Trichotomous
open Variadics _

open import Data.Dec
open import Data.Sum

private variable
  ℓ : Level
  A : Type ℓ
  x y z : A

record ComplementedPoset o ℓ : 𝒰 (ℓsuc (o ⊔ ℓ)) where
  no-eta-equality
  infix 4.5 _≤_ _<_
  field
    Ob  : 𝒰 o
    _≤_ : Ob → Ob → 𝒰 ℓ
    _<_ : Ob → Ob → 𝒰 ℓ

    ≤-thin    : is-prop (x ≤ y)
    ≤-refl    : x ≤ x
    ≤-trans   : x ≤ y → y ≤ z → x ≤ z
    ≤-antisym : x ≤ y → y ≤ x → x ＝ y

    <-thin    : is-prop (x < y)
    <-irrefl  : ¬ (x < x)
    <-trans   : x < y → y < z → x < z

    ⦃ dec-≤ ⦄ : Dec (x ≤ y)
    ⦃ dec-< ⦄ : Dec (x < y)
    ⦃ has-discrete ⦄ : is-discrete Ob

    ≤≃≯ : (x ≤ y) ≃ (¬ y < x)
    <≃≱ : (x < y) ≃ (¬ y ≤ x)

  complemented→poset : Poset o ℓ
  complemented→poset .Poset.Ob = Ob
  complemented→poset .Poset._≤_ = _≤_
  complemented→poset .Poset.≤-thin = ≤-thin
  complemented→poset .Poset.≤-refl = ≤-refl
  complemented→poset .Poset.≤-trans = ≤-trans
  complemented→poset .Poset.≤-antisym = ≤-antisym

  complemented→strict : StrictPoset o ℓ
  complemented→strict .StrictPoset.Ob = Ob
  complemented→strict .StrictPoset._<_ = _<_
  complemented→strict .StrictPoset.<-thin = <-thin
  complemented→strict .StrictPoset.<-irrefl = <-irrefl
  complemented→strict .StrictPoset.<-trans = <-trans

  open Poset complemented→poset using (ob-is-set; _≰_; _≱_; =→≤)
  open StrictPoset complemented→strict using (<-asym; _≮_; _≯_; <→≠)

  ≤→≯ : ∀[ _≤_ ⇒ _≯_ ]
  ≤→≯ {_} {_} = ≤≃≯ $_

  ≯→≤ : ∀[ _≯_ ⇒ _≤_ ]
  ≯→≤ {_} {_} = ≤≃≯ ⁻¹ $_

  <→≱ : ∀[ _<_ ⇒ _≱_ ]
  <→≱ {_} {_} = <≃≱ $_

  ≱→< : ∀[ _≱_ ⇒ _<_ ]
  ≱→< {_} {_} = <≃≱ ⁻¹ $_

  <→≤ : ∀[ _<_ ⇒ _≤_ ]
  <→≤ {_} {_} = <-asym ∙ ≯→≤

  has-weak-total-order : is-weak-total-order complemented→poset
  has-weak-total-order .is-weak-total-order.from-≰ = <→≤ ∘ₜ ≱→<

  has-dec-total-order : is-decidable-total-order complemented→poset
  has-dec-total-order = weak-total-order→dec-total-order has-weak-total-order

  has-dec-strict-total-order : is-decidable-strict-total-order complemented→strict
  has-dec-strict-total-order = discrete+dec+connnex→dec-strict-total-order auto auto
    λ x≮y y≮x → ≤-antisym (≯→≤ y≮x) (≯→≤ x≮y)

  has-tri-order : is-trichotomous complemented→strict
  has-tri-order = dec-strict-total-order→tri-order has-dec-strict-total-order

  ≤→<⊎= : (x ≤ y) → (x < y) ⊎ (x ＝ y)
  ≤→<⊎= {x} {y} x≤y with dec-< {x} {y}
  ... | yes x<y = inl x<y
  ... | no  x≮y = inr (≤-antisym x≤y (≯→≤ x≮y))

  <⊎=→≤ : (x < y) ⊎ (x ＝ y) → x ≤ y
  <⊎=→≤ = [ <→≤ , =→≤ ]ᵤ

  ≤≃<⊎= : (x ≤ y) ≃ (x < y) ⊎ (x ＝ y)
  ≤≃<⊎= = prop-extₑ ≤-thin
    ((disjoint-⊎-is-prop <-thin (ob-is-set _ _) (<→≠ $ₜ²_)))
    ≤→<⊎= <⊎=→≤
