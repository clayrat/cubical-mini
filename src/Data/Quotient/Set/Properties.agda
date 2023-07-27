{-# OPTIONS --safe #-}
module Data.Quotient.Set.Properties where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Search.HLevel

open import Structures.n-Type

open import Correspondences.Base
open import Correspondences.Decidable
open import Correspondences.Discrete

import Data.Empty.Base as ⊥
open import Data.Empty.Instances.HLevel
import Data.Dec.Base as Dec
open Dec using (Dec)
open import Data.Dec.Instances.HLevel
import Data.Quotient.Type.Base as Q∞
open import Data.Quotient.Set.Base

import Truncation.Propositional as ∥-∥₁
open ∥-∥₁ using (∃-syntax; ∥_∥₁ ; ∣_∣₁)

private variable
  ℓᵃ ℓᵇ ℓᶜ ℓᵖ ℓʳ ℓˢ ℓᵗ ℓ : Level
  A : Type ℓᵃ
  x y : A
  B : Type ℓᵇ
  C : Type ℓᶜ
  P : A → Type ℓᵖ
  R : A → A → Type ℓʳ
  S : B → B → Type ℓˢ
  T : C → C → Type ℓᵗ

elim-prop!
  : {@(tactic hlevel-tactic-worker) P-prop : Π[ x ꞉ A / R ] is-prop (P x)}
    (f : Π[ a ꞉ A ] P ⦋ a ⦌)
  → Π[ q ꞉ A / R ] P q
elim-prop! {P-prop} = elim-prop P-prop

elim₂-prop
  : {P : A / R → B / S → Type ℓ}
    (P-prop : ∀ x y → is-prop (P x y))
    (f : Π[ a ꞉ A ] Π[ b ꞉ B ] P ⦋ a ⦌ ⦋ b ⦌)
  → Π[ q₁ ꞉ A / R ] Π[ q₂ ꞉ B / S ] P q₁ q₂
elim₂-prop {P} P-prop f = elim-prop! λ a → elim-prop! (f a)
  where instance P-prop′ : ∀ {x y} → is-prop (P x y) ; P-prop′ = P-prop _ _

elim₂-prop!
  : {P : A / R → B / S → Type ℓ}
    {@(tactic hlevel-tactic-worker) P-prop : ∀ x y → is-prop (P x y)}
    (f : Π[ a ꞉ A ] Π[ b ꞉ B ] P ⦋ a ⦌ ⦋ b ⦌)
  → Π[ q₁ ꞉ A / R ] Π[ q₂ ꞉ B / S ] P q₁ q₂
elim₂-prop! {P} {P-prop} = elim₂-prop P-prop

elim₃-prop
  : {P : A / R → B / S → C / T → Type ℓ}
    (P-prop : ∀ x y z → is-prop (P x y z))
    (f : Π[ a ꞉ A ] Π[ b ꞉ B ] Π[ c ꞉ C ] P ⦋ a ⦌ ⦋ b ⦌ ⦋ c ⦌)
  → Π[ q₁ ꞉ A / R ] Π[ q₂ ꞉ B / S ] Π[ q₃ ꞉ C / T ] P q₁ q₂ q₃
elim₃-prop {P} P-prop f = elim-prop! λ a → elim-prop! λ b → elim-prop! (f a b)
  where instance P-prop′ : ∀ {x y z} → is-prop (P x y z) ; P-prop′ = P-prop _ _ _

elim₃-prop!
  : {P : A / R → B / S → C / T → Type ℓ}
    {@(tactic hlevel-tactic-worker) P-prop : ∀ x y z → is-prop (P x y z)}
    (f : Π[ a ꞉ A ] Π[ b ꞉ B ] Π[ c ꞉ C ] P ⦋ a ⦌ ⦋ b ⦌ ⦋ c ⦌)
  → Π[ q₁ ꞉ A / R ] Π[ q₂ ꞉ B / S ] Π[ q₃ ꞉ C / T ] P q₁ q₂ q₃
elim₃-prop! {P} {P-prop} = elim₃-prop P-prop


elim!
  : {@(tactic hlevel-tactic-worker) P-set : Π[ x ꞉ A / R ] is-set (P x)}
    (f : Π[ a ꞉ A ] P ⦋ a ⦌)
  → (∀ a b (r : R a b) → ＜ f a ／ (λ i → P (glue/ a b r i)) ＼ f b ＞)
  → Π[ q ꞉ A / R ] P q
elim! {P-set} = elim P-set


rec! : {@(tactic hlevel-tactic-worker) B-set : is-set B}
     → (f : A → B)
     → (∀ a b → R a b → f a ＝ f b)
     → A / R → B
rec! {B-set} = rec B-set

rec₂ : is-set C
     → (f : A → B → C)
     → (∀ x y b → R x y → f x b ＝ f y b)
     → (∀ a x y → S x y → f a x ＝ f a y)
     → A / R → B / S → C
rec₂ C-set f fa= fb= =
  rec! (λ a → rec! (f a) (fb= a)) λ a b r → fun-ext $ elim-prop! λ x → fa= a b x r
  where instance _ = C-set

rec₂! : {@(tactic hlevel-tactic-worker) C-set : is-set C}
      → (f : A → B → C)
      → (∀ x y b → R x y → f x b ＝ f y b)
      → (∀ a x y → S x y → f a x ＝ f a y)
      → A / R → B / S → C
rec₂! {C-set} = rec₂ C-set


-- Actual properties

⦋-⦌-surjective : (x : A / R) → ∃[ a ꞉ A ] ⦋ a ⦌ ＝ x
⦋-⦌-surjective = elim-prop! λ a → ∣ a , refl ∣₁

universal : is-set B
          → (A / R → B)
          ≃ Σ[ f ꞉ (A → B) ] (∀ a b → R a b → f a ＝ f b)
universal {B} {A} {R} B-set = iso→equiv $ inc , iso back (λ _ → refl) li where
  instance _ = B-set
  inc : (A / R → B) → Σ[ f ꞉ (A → B) ] (∀ a b → R a b → f a ＝ f b)
  inc f = f ∘ ⦋_⦌ , λ a b r i → f (glue/ a b r i)
  back = rec! $₂_
  li : _
  li f′ = fun-ext λ r → ∥-∥₁.rec! (λ (_ , p) → ap (back (inc f′)) (sym p) ∙ ap f′ p) (⦋-⦌-surjective r)

module @0 _ {R : Corr 2 ℓ A} (congr : is-congruence R) where
  private
    open is-congruence congr
    instance
      R-prop : ∀{x y} → is-prop (R x y)
      R-prop {x} {y} = has-is-prop x y

  Code : A → A / R → Prop ℓ
  Code x = elim! (λ y → el! (R x y)) λ y z r →
    n-ua $ prop-extₑ! (_∙ᶜ r) (_∙ᶜ symᶜ r)

  encode : ∀ x y (p : ⦋ x ⦌ ＝ y) → ⌞ Code x y ⌟
  encode x y p = subst (λ z → ⌞ Code x z ⌟) p reflᶜ

  decode : ∀ x y (p : ⌞ Code x y ⌟) → ⦋ x ⦌ ＝ y
  decode = elim-prop! ∘ glue/

  effective : ⦋ x ⦌ ＝ ⦋ y ⦌
            ≃ R x y
  effective {x} {y} = prop-extₑ! (encode x ⦋ y ⦌) (decode x ⦋ y ⦌)

@0 equivalence→effective₁
  : Equivalence R
  → ⦋ x ⦌ ＝ ⦋ y ⦌
  ≃ ∥ R x y ∥₁
equivalence→effective₁ {R} R-equiv = effective (mk-congruence (λ _ _ → ∥-∥₁.∥-∥₁-is-prop) ∥R∥₁-equiv) where
  open Equivalence R-equiv
  ∥R∥₁-equiv : Equivalence (λ a b → ∥ R a b ∥₁)
  ∥R∥₁-equiv .Equivalence.reflᶜ = ∣ reflᶜ ∣₁
  ∥R∥₁-equiv .Equivalence.symᶜ = ∥-∥₁.map symᶜ
  ∥R∥₁-equiv .Equivalence._∙ᶜ_ = ∥-∥₁.elim₂! λ a b → ∣ a ∙ᶜ b ∣₁

-- @0 what : Equivalence R → (∀ x y → Dec (R x y)) → is-discrete (A / R)
-- what {R} R-equiv d = is-discrete-η $ elim₂-prop! λ x y →
--   Dec.map (go x y) {!!} $ d′ x y
--   where
--     d′ : ∀ x y → Dec ∥ R x y ∥₁
--     d′ x y = Dec.map ∣_∣₁ (λ f → ∥-∥₁.rec! f) (d x y)
--     go : ∀ x y → ∥ R x y ∥₁ → ⦋ x ⦌ ＝ ⦋ y ⦌
--     go x y r = {!!}
--   -- Dec.map (λ r → {!!}) {!!} (Dec.map ∣_∣₁ (λ f → ∥-∥₁.rec! f) (d x y))
--   -- Dec.map {!!}
--   --         (λ f p → ⊥.absurd (f (effective (mk-congruence {!!}  R-equiv) .fst p)))
--   --         (d x y)