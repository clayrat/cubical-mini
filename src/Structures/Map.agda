{-# OPTIONS --safe #-}
module Structures.Map where

open import Foundations.Base

open import Meta.Membership
open import Meta.Record

open import Data.Empty.Base
open import Data.Maybe.Base

module _ {ℓᵏ ℓᵛ ℓ} (K : 𝒰 ℓᵏ) (V : 𝒰 ℓᵛ) (M : 𝒰 ℓ) where
  private variable
    m : M
    k k₁ k₂ : K
    v x y : V

  record MapI : 𝒰 (ℓᵏ ⊔ ℓᵛ ⊔ ℓ) where
    no-eta-equality
    field
      empty  : M
      lookup : M → K → Maybe V
      insert : M → K → V → M
      remove : M → K → M

      lookup-empty     : Erased $ᴱ lookup empty k ＝ nothing
      lookup-insert    : Erased $ᴱ lookup (insert m k v) k ＝ just v
      lookup-remove    : Erased $ᴱ lookup (remove m k) k ＝ nothing
      insert-nop       : lookup m k ＝ just v
                       → Erased $ᴱ insert m k v ＝ m
      insert-overwrite : Erased $ᴱ insert (insert m k x) k y ＝ insert m k y
      insert-insert    : k₁ ≠ k₂
                       → Erased $ᴱ insert (insert m k₁ x) k₂ y ＝ insert (insert m k₂ y) k₁ x
      insert-remove    : lookup m k ＝ just v
                       → Erased $ᴱ insert (remove m k) k v ＝ m
      remove-nop       : lookup m k ＝ nothing
                       → Erased $ᴱ remove m k ＝ m
      remove-remove    : Erased $ᴱ remove (remove m k₁) k₂ ＝ remove (remove m k₂) k₁
      remove-insert    : lookup m k ＝ nothing
                       → Erased $ᴱ remove (insert m k v) k ＝ m

    instance
      Membership-map : Membership K M ℓᵛ
      Membership-map ._∈_ k m = Σ[ v ꞉ _ ] (lookup m k ＝ just v)

unquoteDecl MapI-iso = declare-record-iso MapI-iso (quote MapI)
