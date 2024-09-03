{-# OPTIONS --safe #-}
module Foundations.Notation.Unital.Outer where

open import Foundations.Prim.Kan
open import Foundations.Prim.Type
open import Agda.Builtin.Unit

open import Foundations.Notation.Reflexivity
open import Foundations.Notation.Transitivity

private variable
  ℓᵃ ℓᵇ ℓᶜ ℓ : Level
  A : 𝒰 ℓᵃ
  B : 𝒰 ℓᵇ
  C : 𝒰 ℓᶜ

module _
  {ℓᵃ ℓᵇ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {ℓl ℓr : Level}
  (L : A → A → 𝒰 ℓl) (R : A → B → 𝒰 ℓr) where

  Unitality-o : (r : Reflexivity L) (t : Transitivity L R R) → 𝒰 (ℓᵃ ⊔ ℓᵇ ⊔ ℓr)
  Unitality-o r t = {x : A} {y : B} (q : R x y) → t r q ＝ q

  record Unit-o ⦃ r : Refl L ⦄ ⦃ t : Trans L R R ⦄ : 𝒰 (ℓᵃ ⊔ ℓᵇ ⊔ ℓl ⊔ ℓr) where
    no-eta-equality
    field ∙-id-o : Unitality-o (r .refl) (t ._∙_)

open Unit-o ⦃ ... ⦄ public

Unit-oʰ : (R : A → A → 𝒰 ℓ) ⦃ r : Refl R ⦄ ⦃ t : Transʰ  R ⦄ → Type _
Unit-oʰ R = Unit-o R R


module _ {ℓᵃ} (A : 𝒰 ℓᵃ) where

  Unitality-lᵘ : (r : A) (t : A → A → A) → 𝒰 ℓᵃ
  Unitality-lᵘ r t = (x : A) → t r x ＝ x

  record Unit-lᵘ ⦃ r : Reflᵘ A ⦄ ⦃ t : Transᵘ A ⦄ : 𝒰 ℓᵃ where
    no-eta-equality
    field <>-id-l : Unitality-lᵘ (r .mempty) (t ._<>_)

open Unit-lᵘ ⦃ ... ⦄ public

instance
  Unit-lᵘ→Unit-o
    : ⦃ _ : Reflᵘ A ⦄ ⦃ _ : Transᵘ A ⦄ ⦃ _ : Unit-lᵘ A ⦄
    → Unit-o {A = ⊤} {B = ⊤} (λ _ _ → A) (λ _ _ → A)
  Unit-lᵘ→Unit-o .∙-id-o = <>-id-l
  {-# INCOHERENT Unit-lᵘ→Unit-o #-}
