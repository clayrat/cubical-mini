{-# OPTIONS --safe #-}
module Foundations.Notation.Isomorphism where

open import Foundations.Prim.Type

open import Foundations.Notation.Composition
open import Foundations.Notation.Duality
open import Foundations.Notation.Inverse
open import Foundations.Notation.Reflexivity
open import Foundations.Notation.Retraction
open import Foundations.Notation.Section
open import Foundations.Notation.Underlying
open import Foundations.Notation.Unital.Outer

open import Agda.Builtin.Sigma

module _
  {ℓᵃ ℓᵇ : Level} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {ℓ ℓ′ ℓ″ ℓ‴ : Level}
  (F : A → B → 𝒰 ℓ′) (G : B → A → 𝒰 ℓ)
  {F∙G : A → A → 𝒰 ℓ″} {G∙F : B → B → 𝒰 ℓ‴}
  ⦃ _ : Refl F∙G ⦄ ⦃ _ : Comp F G F∙G ⦄
  ⦃ _ : Refl G∙F ⦄ ⦃ _ : Comp G F G∙F ⦄ where

  record Iso (x : A) (y : B) : 𝒰 (ℓ ⊔ ℓ′ ⊔ ℓ″ ⊔ ℓ‴) where
    no-eta-equality
    constructor make-iso
    field
      to       : F x y
      from     : G y x
      inverses : Inverses to from

    open Inverses inverses public
  {-# INLINE make-iso #-}

open Iso

module _
  {ℓᵃ ℓᵇ : Level} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {ℓ ℓ′ ℓ″ ℓ‴ : Level}
  {F : A → B → 𝒰 ℓ′} {G : B → A → 𝒰 ℓ}
  {F∙G : A → A → 𝒰 ℓ″} {G∙F : B → B → 𝒰 ℓ‴}
  ⦃ _ : Refl F∙G ⦄ ⦃ _ : Comp F G F∙G ⦄
  ⦃ _ : Refl G∙F ⦄ ⦃ _ : Comp G F G∙F ⦄
  {x : A} {y : B} where

  iso : (f : F x y) (g : G y x) → f retraction-of g → f section-of g
      → Iso F G x y
  iso f g r s .to = f
  iso f g r s .from = g
  iso f g r s .inverses .Inverses.inv-o = r
  iso f g r s .inverses .Inverses.inv-i = s
  {-# INLINE iso #-}

  is-inv→≅ : (f : F x y) (fi : is-invertible f) → Iso F G x y
  is-inv→≅ f fi .to = f
  is-inv→≅ f fi .from = fi .is-invertible.inv
  is-inv→≅ f fi .inverses = fi .is-invertible.inverses
  {-# INLINE is-inv→≅ #-}

  ≅→is-inv : (i : Iso F G x y) → is-invertible (i .to)
  ≅→is-inv i .is-invertible.inv = i .from
  ≅→is-inv i .is-invertible.inverses = i .inverses
  {-# INLINE ≅→is-inv #-}

  ≅→to-has-section : (i : Iso F G x y) → has-section (i .to)
  ≅→to-has-section i .section = i .from
  ≅→to-has-section i .is-section = i .inv-o
  {-# INLINE ≅→to-has-section #-}

  ≅→from-has-section : (i : Iso F G x y) → has-section (i .from)
  ≅→from-has-section i .section = i .to
  ≅→from-has-section i .is-section = i .inv-i
  {-# INLINE ≅→from-has-section #-}

  ≅→to-has-retraction : (i : Iso F G x y) → has-retraction (i .to)
  ≅→to-has-retraction i .retraction = i .from
  ≅→to-has-retraction i .is-retraction = i .inv-i
  {-# INLINE ≅→to-has-retraction #-}

  ≅→from-has-retraction : (i : Iso F G x y) → has-retraction (i .from)
  ≅→from-has-retraction i .retraction = i .to
  ≅→from-has-retraction i .is-retraction = i .inv-o
  {-# INLINE ≅→from-has-retraction #-}

  is-inv→retract : (f : F x y) → is-invertible f → Retract G x y
  is-inv→retract _ fi .fst = fi .is-invertible.inv
  is-inv→retract f _ .snd .section = f
  is-inv→retract _ fi .snd .is-section = fi .is-invertible.inverses .Inverses.inv-i
  {-# INLINE is-inv→retract #-}

  is-inv→retract⁻ : (f : F x y) → is-invertible f → Retract F y x
  is-inv→retract⁻ f _ .fst = f
  is-inv→retract⁻ _ fi .snd .section = fi .is-invertible.inv
  is-inv→retract⁻ _ fi .snd .is-section = fi .is-invertible.inverses .Inverses.inv-o
  {-# INLINE is-inv→retract⁻ #-}

  ≅→retract : Iso F G x y → Retract F y x
  ≅→retract i .fst = i .to
  ≅→retract i .snd = ≅→to-has-section i
  {-# INLINE ≅→retract #-}

-- homogeneous isomorphism
HIso
  : ∀ {ℓᵃ ℓ} {A : 𝒰 ℓᵃ} (R : A → A → 𝒰 ℓ) ⦃ _ : Refl R ⦄ ⦃ _ : Trans R ⦄
  → (x y : A) → 𝒰 ℓ
HIso R = Iso R R


record ≅-notation {ℓᵃ ℓᵇ ℓ}
  (A : 𝒰 ℓᵃ) (B : 𝒰 ℓᵇ) (R : 𝒰 ℓ) : 𝒰ω where
  infix 1 _≅_
  field _≅_ : A → B → R
open ≅-notation ⦃ ... ⦄ public


instance
  Funlike-≅
    : {ℓᵃ ℓᵇ ℓᶜ : Level} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ}
      {ℓ ℓ′ ℓ″ ℓ‴ : Level}
      ⦃ ua : Underlying A ⦄
      {F : A → B → 𝒰 ℓ′} {G : B → A → 𝒰 ℓ}
      {F∙G : A → A → 𝒰 ℓ″} {G∙F : B → B → 𝒰 ℓ‴}
      {x : A} {y : B} {C : Σ (F x y) (λ _ → ⌞ x ⌟) → 𝒰 ℓᶜ}
      ⦃ _ : Refl F∙G ⦄ ⦃ _ : Comp F G F∙G ⦄
      ⦃ _ : Refl G∙F ⦄ ⦃ _ : Comp G F G∙F ⦄
      ⦃ f : Funlike ur (F x y) ⌞ x ⌟ C ⦄
    → Funlike ur (Iso F G x y) ⌞ x ⌟ λ (i , a) → C (i .to , a)
  Funlike-≅ ._#_ i a = i .to # a

  Refl-≅
    : ∀ {ℓᵃ ℓ} {A : 𝒰 ℓᵃ} {R : A → A → 𝒰 ℓ}
      ⦃ _ : Refl R ⦄ ⦃ _ : Trans R ⦄ ⦃ _ : HUnit-o R ⦄
    → Refl (Iso R R)
  Refl-≅ .refl .to = refl
  Refl-≅ .refl .from = refl
  Refl-≅ .refl .inverses .Inverses.inv-o = ∙-id-o _
  Refl-≅ .refl .inverses .Inverses.inv-i = ∙-id-o _

  Dual-≅
    : ∀ {ℓᵃ ℓᵇ ℓᵃ̇ ℓᵇ̇ ℓ ℓ′} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ}
      {F : A → B → 𝒰 ℓ}  {G : B → A → 𝒰 ℓ′}
      {U : A → A → 𝒰 ℓᵃ̇} {V : B → B → 𝒰 ℓᵇ̇}
      ⦃ _ : Comp F G U ⦄ ⦃ _ : Comp G F V ⦄
      ⦃ _ : Refl U ⦄     ⦃ _ : Refl V ⦄
    → Dual (Iso F G) (Iso G F)
  Dual-≅ ._ᵒᵖ i .to = i .from
  Dual-≅ ._ᵒᵖ i .from = i .to
  Dual-≅ ._ᵒᵖ i .inverses = i .inverses ᵒᵖ
