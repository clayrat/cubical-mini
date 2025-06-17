{-# OPTIONS --safe #-}
module Data.Id.Base where

open import Foundations.Base
  renaming ( _＝_ to _＝ₚ_
           ; apˢ  to apₚˢ
           )

open import Data.Dec.Base

-- Martin Escardo's equality
_＝_ : ∀{ℓ} {A : 𝒰 ℓ} (x y : A) → 𝒰 ℓ
x ＝ y = (z : _) → z ＝ₚ x → z ＝ₚ y

private variable
  ℓ ℓ′ ℓᵃ ℓᵇ ℓᶜ : Level
  A : 𝒰 ℓᵃ
  B : 𝒰 ℓᵇ
  C : 𝒰 ℓᶜ
  x y z : A
  a b c : B

instance
  Refl-＝ : Refl (_＝_ {A = A})
  Refl-＝ .refl _ = id

  Sym-＝ : Sym (_＝_ {A = A})
  Sym-＝ ._ᵒᵖ p _ q = q ∙ p _ refl ⁻¹

  Trans-＝ : Trans (_＝_ {A = A})
  Trans-＝ ._∙_ p q _ = q _ ∘ p _

＝ₚ→＝ : x ＝ₚ y → x ＝ y
＝ₚ→＝ e z q = q ∙ e

＝→＝ₚ : x ＝ y → x ＝ₚ y
＝→＝ₚ e = e _ refl

transportˢ : A ＝ B → A → B
transportˢ p = transport (＝→＝ₚ p)

apˢ : (f : A → B) → x ＝ y → f x ＝ f y
apˢ f p _ q = q ∙ ap f (＝→＝ₚ p)

-- TODO simplified
ap²ˢ : (f : A → B → C) → x ＝ y → a ＝ b
     → f x a ＝ f y b
ap²ˢ {x} f e₁ e₂ c q = q ∙ ap² f (＝→＝ₚ e₁) (＝→＝ₚ e₂)

substˢ : (P : A → Type ℓ)
       → x ＝ y → P x → P y
substˢ P = transportˢ ∘ apˢ P

_on-pathsˢ-of_ : (Type ℓ → Type ℓ′) → Type ℓ → Type (ℓ ⊔ ℓ′)
S on-pathsˢ-of A = Π[ a ꞉ A ] Π[ a′ ꞉ A ] S (a ＝ a′)

is-discreteˢ : Type ℓ → Type ℓ
is-discreteˢ = Dec on-pathsˢ-of_
