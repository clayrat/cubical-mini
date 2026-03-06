{-# OPTIONS --safe #-}
module Functions.Surjection.Epic where

open import Meta.Prelude
open import Meta.Effect
open import Meta.Extensionality

open import Data.Unit.Base
open import Data.Truncation.Propositional.Base
open import Data.Truncation.Propositional.Path
open import Data.Truncation.Propositional.Instances.Bind
open import Data.Truncation.Set.Base as ∥-∥₂
open import Data.Truncation.Set.Path

open import Homotopy.Connectedness
open import Structures.n-Type
open import Functions.Surjection

private variable
  ℓ ℓ′ ℓ″ : Level
  A : 𝒰 ℓ
  B : 𝒰 ℓ′
  f : A → B
  g : B → A

is-surjective→set-epic
  : is-surjective f
  → ∀ {C : Set ℓ″} (g h : B → ⌞ C ⌟) → g ∘ f ＝ h ∘ f → g ＝ h
is-surjective→set-epic {f} srj g h p =
  fun-ext λ x → rec! (λ a e → ap g (e ⁻¹) ∙ happly p a ∙ ap h e) (srj x)

data Cofibre {ℓ ℓ′} {A : 𝒰 ℓ} {B : 𝒰 ℓ′} (f : A → B) : 𝒰 (ℓ ⊔ ℓ′) where
  tip  : Cofibre f
  base : B → Cofibre f
  cone : ∀ a → tip ＝ base (f a)

@0 connected₂-cofibre→surjective
  : ∀ {ℓ ℓ′} {A : 𝒰 ℓ} {B : 𝒰 ℓ′}
    (f : A → B)
  → is-contr ∥ Cofibre f ∥₂
  → is-surjective f
connected₂-cofibre→surjective {ℓ} {ℓ′} f conn x = transport cen (lift tt)
  where
  P : Cofibre f → Prop (ℓ ⊔ ℓ′)
  P tip = el! (Lift (ℓ ⊔ ℓ′) ⊤)
  P (base x) = el! ∥ fibre f x ∥₁
  P (cone a i) =
    n-ua {X = el! (Lift (ℓ ⊔ ℓ′) ⊤)} {Y = el! ∥ fibre f (f a) ∥₁}
      (prop-extₑ!
         (λ _ → ∣ a , refl ∣₁)
         λ _ → lift tt)
      i

  P' : ∥ Cofibre f ∥₂ → Prop (ℓ ⊔ ℓ′)
  P' = ∥-∥₂.elim (λ _ → n-Type-is-of-hlevel 1) P

  cen : Lift (ℓ ⊔ ℓ′) ⊤ ＝ ∥ fibre f x ∥₁
  cen =
    ap (⌞_⌟ ∘ P')
       (is-contr→is-prop conn ∣ tip ∣₂ ∣ base x ∣₂)

@0 epi-set→connected-cofibre
  : ∀ {ℓ} {A B : Set ℓ} (f : ⌞ A ⌟ → ⌞ B ⌟)
  → (∀ {ℓ″} {C : Set ℓ″} (g h : ⌞ B ⌟ → ⌞ C ⌟) → g ∘ f ＝ h ∘ f → g ＝ h)
  → is-contr ∥ Cofibre f ∥₂
epi-set→connected-cofibre {A} {B} f epi =
    ∣ tip ∣₂
  , ∥-∥₂.elim hlevel! (λ c → =∘∣-∣₂≃∥-∥₁∘= ⁻¹ $ hom c)
  where
  go : ∀ x → ∥ tip ＝ base x ∥₁
  go x =
    =∘∣-∣₂≃∥-∥₁∘= $
    happly (epi {C = el! ∥ Cofibre f ∥₂}
                (λ _ → ∣ tip ∣₂) (λ q → ∣ base q ∣₂)
                (fun-ext λ z → ap ∣_∣₂ (cone z)))
                x
  hom : ∀ w → ∥ tip ＝ w ∥₁
  hom tip = ∣ refl ∣₁
  hom (base x) = go x
  hom (cone a i) =
    is-prop→pathᴾ (λ j → squash₁ {A = tip ＝ cone a j}) ∣ refl ∣₁ (go (f a)) i

@0 epi-set→surjective
  : ∀ {ℓ} {A B : Set ℓ} (f : ⌞ A ⌟ → ⌞ B ⌟)
  → (∀ {ℓ″} {C : Set ℓ″} (g h : ⌞ B ⌟ → ⌞ C ⌟) → g ∘ f ＝ h ∘ f → g ＝ h)
  → is-surjective f
epi-set→surjective {A} {B} f epi =
  connected₂-cofibre→surjective f $
  epi-set→connected-cofibre {A = A} {B = B} f (λ {ℓ″} {C} → epi {C = C})
