{-# OPTIONS --safe #-}
open import Cat.Prelude

module Cat.Diagram.Pullback {ℓ ℓ′} (C : Precategory ℓ ℓ′) where

import Cat.Morphism
open Cat.Morphism C
private variable
  P′ X Y Z : Ob
  h p₁′ p₂′ : Hom X Y

record universal-for {P : Ob} (p₁ : P ⇒ X) (f : X ⇒ Z) (p₂ : P ⇒ Y) (g : Y ⇒ Z)
                     {P′ : Ob} (p₁′ : P′ ⇒ X) (p₂′ : P′ ⇒ Y)
                     (comm : f ∘ p₁′ ＝ g ∘ p₂′)
  : Type (ℓ ⊔ ℓ′) where

  no-eta-equality
  field
    universal    : P′ ⇒ P
    p₁∘universal : p₁ ∘ universal ＝ p₁′
    p₂∘universal : p₂ ∘ universal ＝ p₂′

    unique : {lim′ : P′ ⇒ P}
           → p₁ ∘ lim′ ＝ p₁′
           → p₂ ∘ lim′ ＝ p₂′
           → lim′ ＝ universal

  unique²
    : {lim′ lim″ : Hom P′ P}
    → p₁ ∘ lim′ ＝ p₁′ → p₂ ∘ lim′ ＝ p₂′
    → p₁ ∘ lim″ ＝ p₁′ → p₂ ∘ lim″ ＝ p₂′
    → lim′ ＝ lim″
  unique² p q r s = unique p q ∙ sym (unique r s)

record is-pullback {P : Ob} (p₁ : P ⇒ X) (f : X ⇒ Z) (p₂ : P ⇒ Y) (g : Y ⇒ Z)
  : Type (ℓ ⊔ ℓ′) where

  no-eta-equality
  field
    square   : f ∘ p₁ ＝ g ∘ p₂
    has-univ : {P′ : Ob} {p₁′ : P′ ⇒ X} {p₂′ : P′ ⇒ Y}
             → (comm : f ∘ p₁′ ＝ g ∘ p₂′) → universal-for p₁ f p₂ g p₁′ p₂′ comm

  pullback-univ
    : ⦃ hl : ∀ {x y} → H-Level 2 (Hom x y) ⦄ {O : Ob}
    → O ⇒ P
    ≃ Σ[ h ꞉ O ⇒ X ] Σ[ h′ ꞉ O ⇒ Y ] (f ∘ h ＝ g ∘ h′)
  pullback-univ .fst h = p₁ ∘ h , p₂ ∘ h , assoc _ _ _ ⁻¹ ∙ ap (_∘ h) square ∙ assoc _ _ _
  pullback-univ {O} .snd = qinv→is-equiv $ qinv (λ (f , g , α) → (has-univ α) .universal-for.universal)
    (fun-ext λ (h , h′ , prf) → (has-univ prf) .universal-for.p₁∘universal
                             ,ₚ (has-univ prf) .universal-for.p₂∘universal
                             ,ₚ prop!) -- TODO prove manually?
    (fun-ext λ _ → (has-univ _) .universal-for.unique refl refl ⁻¹)

-- two directions of pullback lemma

pullback-lemma-fwd : ∀ {A B C D E F : Ob}
                       (f : A ⇒ B) (g : B ⇒ C)
                       (h : D ⇒ E) (i : E ⇒ F)
                       (u : A ⇒ D) (v : B ⇒ E) (w : C ⇒ F)
                   → is-pullback f v u h
                   → is-pullback g w v i
                   → is-pullback (g ∘ f) w u (i ∘ h)
pullback-lemma-fwd f g h i u v w pl pr .is-pullback.square =
    assoc f g w ⁻¹
  ∙ ap (_∘ f) (pr .is-pullback.square)
  ∙ assoc f v i
  ∙ ap (i ∘_) (pl .is-pullback.square)
  ∙ assoc u h i ⁻¹
pullback-lemma-fwd {A} {B} f g h i u v w pl pr .is-pullback.has-univ {P′} {p₁′} {p₂′} comm =
  record
   { universal = plu
   ; p₁∘universal =
          assoc plu f g
        ∙ ap (g ∘_) (plhu .universal-for.p₁∘universal)
        ∙ prhu .universal-for.p₁∘universal
   ; p₂∘universal = plhu .universal-for.p₂∘universal
   ; unique = λ {lim′} e1 e2 →
                     plhu .universal-for.unique
                        (prhu .universal-for.unique
                           (  assoc lim′ f g ⁻¹
                            ∙ e1)
                           (  assoc lim′ f v ⁻¹
                            ∙ ap (_∘ lim′) (pl .is-pullback.square)
                            ∙ assoc lim′ u h
                            ∙ ap (h ∘_) e2))
                        e2
   }
  where
  prhu = pr .is-pullback.has-univ {P′} {p₁′ = p₁′} {p₂′ = h ∘ p₂′}
              (comm ∙ assoc p₂′ h i)
  pru : P′ ⇒ B
  pru = prhu .universal-for.universal

  plhu = pl .is-pullback.has-univ {P′} {p₁′ = pru} {p₂′ = p₂′}
              (prhu .universal-for.p₂∘universal)
  plu : P′ ⇒ A
  plu = plhu .universal-for.universal

pullback-lemma-bwd : ∀ {A B C D E F : Ob}
                       (f : A ⇒ B) (g : B ⇒ C)
                       (h : D ⇒ E) (i : E ⇒ F)
                       (u : A ⇒ D) (v : B ⇒ E) (w : C ⇒ F)
                   → is-pullback g w v i
                   → is-pullback (g ∘ f) w u (i ∘ h)
                   → v ∘ f ＝ h ∘ u
                   → is-pullback f v u h
pullback-lemma-bwd f g h i u v w pr pb eq .is-pullback.square = eq
pullback-lemma-bwd f g h i u v w pr pb eq .is-pullback.has-univ {P′} {p₁′} {p₂′} comm =
  record {
    universal    = ub
  ; p₁∘universal =
      pr-c .universal-for.unique {lim′ = f ∘ ub}
             (  assoc ub f g ⁻¹
              ∙ pb-c .universal-for.p₁∘universal)
             (  assoc ub f v ⁻¹
              ∙ ap (_∘ ub) eq
              ∙ assoc ub u h
              ∙ ap (h ∘_)
                   (pb-c .universal-for.p₂∘universal))
      ∙ pr-c .universal-for.unique {lim′ = p₁′} refl comm ⁻¹
  ; p₂∘universal = pb-c .universal-for.p₂∘universal
  ; unique = λ {lim′} e1 e2 →
                 pb-c .universal-for.unique
                        (assoc lim′ f g ∙ ap (g ∘_) e1) e2
  }
  where
  eq′ : w ∘ g ∘ p₁′ ＝ (i ∘ h) ∘ p₂′
  eq′ =   assoc p₁′ g w ⁻¹
        ∙ ap (_∘ p₁′) (pr .is-pullback.square)
        ∙ assoc p₁′ v i
        ∙ ap (i ∘_) comm
        ∙ assoc p₂′ h i ⁻¹
  pb-c = pb .is-pullback.has-univ eq′
  pr-c = pr .is-pullback.has-univ (eq′ ∙ assoc p₂′ h i)
  ub   = pb-c .universal-for.universal

record Pullback {X Y Z : Ob} (f : X ⇒ Z) (g : Y ⇒ Z) : Type (ℓ ⊔ ℓ′) where
  no-eta-equality
  field
    {apex} : Ob
    p₁ : apex ⇒ X
    p₂ : apex ⇒ Y
    has-is-pb : is-pullback p₁ f p₂ g

  open is-pullback has-is-pb public

has-pullbacks : Type _
has-pullbacks = {A B X : Ob} (f : A ⇒ X) (g : B ⇒ X) → Pullback f g

module Pullbacks (all-pullbacks : has-pullbacks) where
  module pullback {x y z : Ob} (f : x ⇒ z) (g : y ⇒ z) = Pullback (all-pullbacks f g)

  Pb : {x y z : Ob} → x ⇒ z → y ⇒ z → Ob
  Pb = pullback.apex

is-pullback-stable
  : ∀ {ℓ′} → ({a b : Ob} → a ⇒ b → Type ℓ′) → Type _
is-pullback-stable P =
  ∀ {p A B X : Ob} (f : A ⇒ B) (g : X ⇒ B) {f⁺ : p ⇒ X} {p₂ : p ⇒ A}
  → P f → is-pullback f⁺ g p₂ f
  → P f⁺
