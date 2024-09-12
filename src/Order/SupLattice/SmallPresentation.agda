{-# OPTIONS --safe #-}
open import Cat.Prelude

open import Order.Base
open import Order.SupLattice
open import Order.SupLattice.SmallBasis

open import Combinatorics.Power

module Order.SupLattice.SmallPresentation
  {o ℓ ℓ′}
  {P : Poset o ℓ} {L : is-sup-lattice P ℓ′}
  {B : 𝒰 ℓ′} {β : B → ⌞ P ⌟}
  (h : is-basis L β) where

  open is-sup-lattice L
  open is-basis h

  is-a-small-presentation : Σ[ J ꞉ 𝒰 ℓ′ ] (J → ℙ B ℓ′) × ℙ (B × ℙ B ℓ′) ℓ′ → 𝒰 (ℓsuc ℓ′)
  is-a-small-presentation (J , Y , R) =
      (b : B) (X : ℙ B ℓ′)
    → b ≤ᴮ ℙ⋃ L β X ≃ ∃[ j ꞉ J ] Y j ⊆ X × (b , Y j) ∈ R

  has-small-presentation : 𝒰 (ℓsuc ℓ′)
  has-small-presentation =
    Σ[ 𝓡 ꞉ Σ[ J ꞉ 𝒰 ℓ′ ] (J → ℙ B ℓ′) × ℙ (B × ℙ B ℓ′) ℓ′ ] is-a-small-presentation 𝓡
