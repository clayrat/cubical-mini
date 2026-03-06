{-# OPTIONS --safe #-}
module Functions.Surjection where

open import Meta.Prelude
open import Meta.Effect
open import Meta.Extensionality

open import Functions.Embedding

open import Data.Truncation.Propositional.Base
open import Data.Truncation.Propositional.Path
open import Data.Truncation.Propositional.Instances.Bind

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ
  B : Type ℓ′
  f : A → B
  g : B → A

Split-surjective : (A → B) → Type _
Split-surjective {B} f = Π[ y ꞉ B ] fibre f y

Split-surjectiveᴱ : (A → B) → Type _
Split-surjectiveᴱ {B} f = Π[ y ꞉ B ] fibreᴱ f y

_↠!_ : Type ℓ → Type ℓ′ → Type _
A ↠! B = Σ[ f ꞉ (A → B) ] Split-surjective f

is-surjective : (A → B) → Type _
is-surjective {B} f = Π[ y ꞉ B ] ∥ fibre f y ∥₁

is-surjective-is-prop : is-prop (is-surjective f)
is-surjective-is-prop = hlevel 1

-- squash₁

_↠_ : Type ℓ → Type ℓ′ → Type _
A ↠ B = Σ[ f ꞉ (A → B) ] is-surjective f

instance
  Refl-Split-surj :  Refl (_↠!_ {ℓ})
  Refl-Split-surj .refl = refl , (_, refl)

  Refl-Surj :  Refl (_↠_ {ℓ})
  Refl-Surj .refl = refl , λ a → ∣ a , refl ∣₁

  Comp-Split-surj : Comp (_↠!_ {ℓ} {ℓ′}) (_↠!_ {ℓ′ = ℓ″}) _↠!_
  Comp-Split-surj ._∙_ (f , _) (g , _) .fst = f ∙ g
  Comp-Split-surj ._∙_ (f , φ) (g , ψ) .snd c =
    let u  , v  = ψ c
        u′ , v′ = φ u
    in u′ , ap g v′ ∙ v

  Comp-Surj : Comp (_↠_ {ℓ} {ℓ′}) (_↠_ {ℓ′ = ℓ″}) _↠_
  Comp-Surj ._∙_ (f , _) (g , _) .fst = f ∙ g
  Comp-Surj ._∙_ (f , φ) (g , ψ) .snd c = do
    u  , v  ← ψ c
    u′ , v′ ← φ u
    pure (u′ , ap g v′ ∙ v)

retraction→split-surjective
  : {f : A → B} {g : B → A}
  → f retraction-of g → Split-surjective f
retraction→split-surjective {g} s b = g b , s # b

retraction→is-surjective
  : {f : A → B} {g : B → A}
  → f retraction-of g → is-surjective f
retraction→is-surjective s b = ∣ retraction→split-surjective s b ∣₁

is-equiv→split-surjective : is-equiv f → Split-surjective f
is-equiv→split-surjective r y = equiv-proof r y .fst

is-equiv→is-surjective : is-equiv f → is-surjective f
is-equiv→is-surjective r y = ∣ is-equiv→split-surjective r y ∣₁

split-surjective→epic
  : Split-surjective f
  → ∀ {C : 𝒰 ℓ″} (g h : B → ⌞ C ⌟) → g ∘ f ＝ h ∘ f → g ＝ h
split-surjective→epic ssrj g h p =
  fun-ext λ x → let (a , e) = ssrj x in ap g (e ⁻¹) ∙ happly p a ∙ ap h e

≃→↠! : A ≃ B → A ↠! B
≃→↠! = second is-equiv→split-surjective

≃→↠ : A ≃ B → A ↠ B
≃→↠ = second is-equiv→is-surjective

is-surjective-comp+is-surjective-inner→is-surjective-outer
  : {A : Type ℓ} {B : Type ℓ′} {C : Type ℓ″} {f : A → B} {g : B → C}
  → is-surjective (f ∙ g) → is-surjective f → is-surjective g
is-surjective-comp+is-surjective-inner→is-surjective-outer {f} {g} gfs gs z = do
  a , p ← gfs z
  b , q ← gs (f a)
  pure (f a , p)

instance
  Extensional-↠
    : {A : Type ℓ} ⦃ sb : Extensional (A → B) ℓ″ ⦄
    → Extensional (A ↠ B) ℓ″
  Extensional-↠ ⦃ sb ⦄ = Σ-prop→extensional! sb
