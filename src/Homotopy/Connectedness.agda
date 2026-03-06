{-# OPTIONS --safe #-}
module Homotopy.Connectedness where

open import Meta.Prelude
open import Meta.Deriving.HLevel
open import Meta.Extensionality

open import Structures.n-Type

open import Data.Truncation.Propositional.Base
open import Data.Truncation.Propositional.Path
open import Data.Truncation.Set.Base as ∥-∥₂
open import Data.Truncation.Set.Path

private variable
  ℓ : Level
  A : Type ℓ

record is-connected {ℓ} (A : 𝒰 ℓ) : 𝒰 ℓ where
  no-eta-equality
  constructor conn₁
  field
    centre₁ : ∥ A ∥₁
    paths₁  : ∥_∥₁ on-paths-of A

open is-connected public

unquoteDecl H-Level-is-connected =
  declare-record-hlevel 1 H-Level-is-connected (quote is-connected)

Connected-component : (c : A) → Type (level-of-type A)
Connected-component {A} c = Σ[ a ꞉ A ] ∥ c ＝ a ∥₁

-- TODO equiv

is-connected→contr-settrunc : is-connected A → is-contr ∥ A ∥₂
is-connected→contr-settrunc conn =
  rec!
    (λ x → ∣ x ∣₂ , ∥-∥₂.elim hlevel!
                       (λ y′ → rec! (ap ∣_∣₂) (conn .paths₁ x y′)))
    (conn .centre₁)

@0 contr-settrunc→is-connected : is-contr ∥ A ∥₂ → is-connected A
contr-settrunc→is-connected ctr .centre₁ = rec! ∣_∣₁ (ctr .fst)
contr-settrunc→is-connected ctr .paths₁ x y =
  =∘∣-∣₂≃∥-∥₁∘= $ (ctr .snd ∣ x ∣₂) ⁻¹ ∙ ctr .snd ∣ y ∣₂

