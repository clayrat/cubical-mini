{-# OPTIONS --safe #-}
module Cat.Diagram.Equaliser where

open import Cat.Prelude
import Cat.Reasoning

module _ {o ℓ} (C : Precategory o ℓ) where
  open Cat.Reasoning C
  private variable
    A B : Ob
    f g h : Hom A B
  
  record is-equaliser {E} (f g : Hom A B) (equ : Hom E A) : Type (o ⊔ ℓ) where
    field
      equal     : f ∘ equ ＝ g ∘ equ
      universal : ∀ {F} {e' : Hom F A} (p : f ∘ e' ＝ g ∘ e') → Hom F E
      factors   : ∀ {F} {e' : Hom F A} {p : f ∘ e' ＝ g ∘ e'} → equ ∘ universal p ＝ e'
      unique
        : ∀ {F} {e' : Hom F A} {p : f ∘ e' ＝ g ∘ e'} {other : Hom F E}
        → equ ∘ other ＝ e'
        → other ＝ universal p

    equal-∘ : f ∘ equ ∘ h ＝ g ∘ equ ∘ h
    equal-∘ {h = h} =
      f ∘ equ ∘ h ~⟨ extendl equal ⟩
      g ∘ equ ∘ h ∎

    unique₂
      : ∀ {F} {e' : Hom F A}  {o1 o2 : Hom F E}
      → f ∘ e' ＝ g ∘ e'
      → equ ∘ o1 ＝ e'
      → equ ∘ o2 ＝ e'
      → o1 ＝ o2
    unique₂ p q r = unique {p = p} q ∙ unique r ⁻¹

  record Equaliser (f g : Hom A B) : Type (o ⊔ ℓ) where
    field
      {apex}  : Ob
      equ     : Hom apex A
      has-is-eq : is-equaliser f g equ

    open is-equaliser has-is-eq public

module _ {o ℓ} {C : Precategory o ℓ} where
  open Cat.Reasoning C
  private variable
    A B : Ob
    f g h : Hom A B

  is-equaliser→is-monic
    : ∀ {E} (equ : Hom E A)
    → is-equaliser C f g equ
    → is-monic equ
  is-equaliser→is-monic equ equalises g h p =
    unique₂ (extendl equal) p refl
    where open is-equaliser equalises

  is-equaliser→iso
    : {E E' : Ob}
    → {e : Hom E A} {e' : Hom E' A}
    → is-equaliser C f g e
    → is-equaliser C f g e'
    → E ≅ E'
  is-equaliser→iso {e} {e'} eq eq' =
    make-iso
      (eq' .universal (eq .equal))
      (eq .universal (eq' .equal)) $
      make-inverses 
        (unique₂ eq' (eq' .equal) (pulll (eq' .factors) ∙ eq  .factors) (∙-id-o _))
        (unique₂ eq  (eq  .equal) (pulll (eq  .factors) ∙ eq' .factors) (∙-id-o _))
    where open is-equaliser

  id-is-equaliser : is-equaliser C f f id
  id-is-equaliser .is-equaliser.equal = refl
  id-is-equaliser .is-equaliser.universal {e' = e'} _ = e'
  id-is-equaliser .is-equaliser.factors = ∙-id-i _
  id-is-equaliser .is-equaliser.unique p = sym (∙-id-i _) ∙ p

{-
  equaliser+epi→invertible
    : ∀ {E} {e : Hom E A}
    → is-equaliser C f g e
    → is-epic e
    → is-invertible e

  equaliser+epi→invertible {f = f} {g = g} {e = e} e-equaliser e-epi =
    make-invertible
      (universal {e' = id} (ap₂ _∘_ f＝g refl))
      factors
      (unique₂ (ap₂ _∘_ f＝g refl) (pulll factors) id-comm)
    where
      open is-equaliser e-equaliser
      f＝g : f ＝ g
      f＝g = e-epi f g equal
-}

has-equalisers : ∀ {o ℓ} → Precategory o ℓ → Type _
has-equalisers C = ∀ {a b} (f g : Hom a b) → Equaliser C f g
  where open Precategory C

module Equalisers
  {o ℓ}
  (C : Precategory o ℓ)
  (all-equalisers : has-equalisers C)
  where
  open Cat.Reasoning C
  module equaliser {a b} (f g : Hom a b) = Equaliser (all-equalisers f g)

  Equ : ∀ {a b} (f g : Hom a b) → Ob
  Equ = equaliser.apex
