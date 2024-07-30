{-# OPTIONS --safe #-}
module Combinatorics.Power.Decidable where

open import Meta.Prelude

open import Structures.n-Type

open import Logic.Decidability

open import Combinatorics.Power.Base

open import Data.Bool as Bool
open import Data.Dec as Dec
open import Data.Empty as ⊥
open import Data.Sum.Base
open import Data.Unit.Base
open import Data.Truncation.Propositional as ∥-∥₁


private variable
  ℓˣ ℓ : Level
  X : Type ℓˣ
  x y : X

is-complemented : {ℓ : Level} (A : ℙ X ℓ) → Type (level-of-type X ⊔ ℓsuc ℓ)
is-complemented {X} {ℓ} A =
  Σ[ A⁻¹ ꞉ ℙ X ℓ ] (_⊆_ ⦃ m₂ = Membership-pow {P = Prop ℓ} ⦄ (A ∩ A⁻¹) ⊥)
                × (_⊆_ ⦃ m₁ = Membership-pow {P = Prop ℓ} ⦄ ⊤ (A ∪ A⁻¹))

is-decidable-subset : (A : ℙ X ℓ) → Type (level-of-type X ⊔ ℓ)
is-decidable-subset {X} A = Decidable (λ (x : X) → x ∈ A)

instance
  Decidability-subset : {X : Type ℓ} → Decidability (ℙ X ℓ)
  Decidability-subset {ℓ} .ℓ-decidability = ℓ
  Decidability-subset .Decidable = is-decidable-subset
  {-# OVERLAPPING Decidability-subset #-}

is-complemented→is-decidable-subset : (A : ℙ X ℓ) → is-complemented A → Decidable A
is-complemented→is-decidable-subset A (A⁻¹ , int , uni) {x} = case uni _ of
  [ yes
  , (λ x∈A⁻¹ → no λ x∈A → int (x∈A , x∈A⁻¹) .lower)
  ]ᵤ

is-decidable-subset→is-complemented : (A : ℙ X ℓ) → Decidable A → is-complemented A
is-decidable-subset→is-complemented {X} A d
  = (λ x → el! (¬ x ∈ A))
  , (λ z → lift (z .snd (z .fst)))
  , Dec.rec (λ x∈A _ → ∣ inl x∈A ∣₁) (λ x∈A⁻¹ _ → ∣ inr x∈A⁻¹ ∣₁) d

ℙᵈ : {ℓ : Level} → Type ℓˣ → Type (ℓˣ ⊔ ℓsuc ℓ)
ℙᵈ {ℓ} X = Σ[ A ꞉ ℙ X ℓ ] Decidable A

@0 decidable-subobject-classifier : {X : 𝒰 ℓ} → (X → Bool) ≃ ℙᵈ X
decidable-subobject-classifier {ℓ} {X} = ≅→≃ $ to , iso (λ pr x → from pr x .fst) ri li where
  to : (X → Bool) → ℙᵈ X
  to ch = (λ x → el (Lift ℓ (is-true (ch x))) (Bool.elim {P = λ b → is-prop (Lift ℓ (is-true b))} hlevel! hlevel! (ch x)))
        , λ {x} → Bool.elim {P = λ x → Dec (Lift ℓ (is-true x))} auto auto (ch x)

  from : (pr : ℙᵈ X) (x : X) → Σ[ b ꞉ Bool ] (is-true b ≃ (x ∈ pr .fst))
  from (A , d) x = Dec.elim (λ x∈A → true  , prop-extₑ! (λ _ → x∈A) _)
                            (λ x∉A → false , prop-extₑ! (⊥.rec $_) x∉A) d

  ri : _
  ri A = Σ-prop-path! (ℙ-ext (from A _ .snd .fst ∘ lower) (lift ∘ Equiv.from (from A _ .snd)))

  li : _
  li ch = fun-ext λ x → Bool.elim {P = λ p → from (to λ _ → p) x .fst ＝ p} refl refl (ch x)
