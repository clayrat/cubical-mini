{-# OPTIONS --safe #-}
module Data.Truncation.Set.Instances.Bind where

open import Foundations.Base
open import Foundations.HLevel

open import Meta.Effect.Base
open import Meta.Effect.Bind
open import Meta.Effect.Idiom
open import Meta.Inductive

open import Data.Truncation.Set.Base
open import Data.Truncation.Set.Instances.Idiom public

open Idiom ⦃ ... ⦄
open Bind ⦃ ... ⦄
open Lawful-Bind ⦃ ... ⦄

private variable
  n : HLevel
  ℓ : Level
  A : Type ℓ

instance
  private
    _ : H-Level (2 + n) ∥ A ∥₂
    _ = hlevel-basic-instance 2 squash₂

  Bind-∥-∥₂ : Bind (eff ∥_∥₂)
  Bind-∥-∥₂ .Bind._>>=_ = flip rec!

  Lawful-Bind-∥-∥₂ : Lawful-Bind (eff ∥_∥₂)
  Lawful-Bind-∥-∥₂ .Lawful-Bind.>>=-id-l = refl
  Lawful-Bind-∥-∥₂ .Lawful-Bind.>>=-id-r {A} {mx} = go mx where opaque
    go : (x : ∥ A ∥₂) → (x >>= pure) ＝ x
    go = elim! λ _ → refl
  Lawful-Bind-∥-∥₂ .Lawful-Bind.>>=-assoc {A} {mx} {f} {g} = go mx where opaque
    go : (x : ∥ A ∥₂) → (x >>= f >>= g) ＝ (x >>= λ x → f x >>= g)
    go = elim! λ _ → refl
  Lawful-Bind-∥-∥₂ .<*>->>= {A} {B} {mf} {mx} = go mf mx where opaque
    go : (f : ∥ (A → B) ∥₂) (x : ∥ A ∥₂) → (f <*> x) ＝ (f >>= λ f → x >>= (pure ∘ f))
    go = elim! (λ _ _ → refl)
