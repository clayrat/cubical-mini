{-# OPTIONS --safe #-}
module Order.SupLattice.TarskiLFP where

open import Categories.Prelude
open import Meta.Prelude

open import Data.Empty
open import Data.Unit

open import Combinatorics.Power
open import Functions.Surjection

open import Order.Diagram.Lub
open import Order.Base
open import Order.Category
open import Order.SupLattice
open import Order.SupLattice.SmallBasis
import Order.Reasoning

module _ {o ℓ} (P : Poset o ℓ) where

  open Poset P

  has-lfp : (Ob → Ob) → 𝒰 (o ⊔ ℓ)
  has-lfp f = Σ[ p ꞉ Ob ] (f p ＝ p) × ((a : Ob) → f a ＝ a → p ≤ a)

  has-lfp-is-prop : (f : Ob → Ob) → is-prop (has-lfp f)
  has-lfp-is-prop f (p₁ , fp₁ , l₁) (p₂ , fp₂ , l₂) =
    Σ-prop-path (λ x → hlevel 1)
                (≤-antisym (l₁ p₂ fp₂) (l₂ p₁ fp₁))

module _ {o ℓ ℓ′} {B : 𝒰 ℓ′}
         (P : Poset o ℓ)
         (L : is-sup-lattice P ℓ′)
         (β : B → ⌞ P ⌟)
         (h : is-basis P L β)
        where

  open Poset P
  open is-sup-lattice L
  open is-basis h

  c-closure : {ℓ″ : Level} (S : ℙ B ℓ″) → 𝒰 (ℓsuc ℓ′ ⊔ ℓ″)
  c-closure S = (U : ℙ B ℓ′) → U ⊆ S → (b : B) → b ≤ᴮ (sup (ℙ→fam β U .snd)) → b ∈ S

  Φ-closure : (ϕ : ℙ (B × Ob) (o ⊔ ℓ′))
           → {ℓ″ : Level} (S : ℙ B ℓ″)
           → 𝒰 (o ⊔ ℓ′ ⊔ ℓ″)
  Φ-closure ϕ S = (a : Ob)
                → (b : B)
                → (b , a) ∈ ϕ
                → ((b' : B) → b' ≤ᴮ a → b' ∈ S)
                → b ∈ S

  data 𝓘 (ϕ : ℙ (B × Ob) (o ⊔ ℓ′)) : B → 𝒰 (o ⊔ ℓsuc ℓ′) where
    c-closed : (U : ℙ B ℓ′) → ({b : B} → b ∈ U → 𝓘 ϕ b)
             → (b : B) → b ≤ᴮ (sup (ℙ→fam β U .snd)) → 𝓘 ϕ b
    ϕ-closed : (a : Ob) → (b : B) → (b , a) ∈ ϕ
              → ((b' : B) → b' ≤ᴮ a → 𝓘 ϕ b')
              → 𝓘 ϕ b
    𝓘-trunc : (b : B) → is-prop (𝓘 ϕ b)

  module trunc-ind-def (ϕ : ℙ (B × Ob) (o ⊔ ℓ′)) where

    𝓘nd : ℙ B (o ⊔ ℓsuc ℓ′)
    𝓘nd b = el (𝓘 ϕ b) (𝓘-trunc b)

    𝓘nd-is-c-closed : c-closure 𝓘nd
    𝓘nd-is-c-closed = c-closed

    𝓘nd-is-ϕ-closed : Φ-closure ϕ 𝓘nd
    𝓘nd-is-ϕ-closed = ϕ-closed

    𝓘nd-is-initial : {ℓ″ : Level} (P : ℙ B ℓ″)
                   → c-closure P
                   → Φ-closure ϕ P
                   → 𝓘nd ⊆ P
    𝓘nd-is-initial P cc ϕc (c-closed U sub b le) = cc U (λ ua → 𝓘nd-is-initial P cc ϕc (sub ua)) b le
    𝓘nd-is-initial P cc ϕc (ϕ-closed a b m f)    = ϕc a b m (λ b' le → 𝓘nd-is-initial P cc ϕc (f b' le))
    𝓘nd-is-initial P cc ϕc (𝓘-trunc b x y i)     = hlevel 1 (𝓘nd-is-initial P cc ϕc x) (𝓘nd-is-initial P cc ϕc y) i

module local-inductive-definitions
         {o ℓ ℓ′} {B : 𝒰 ℓ′}
         (P : Poset o ℓ)
         (L : is-sup-lattice P ℓ′)
         (β : B → ⌞ P ⌟)
         (h : is-basis P L β)
       where

  open Poset P
  open is-lub
  open is-sup-lattice L
  open is-basis h

  _↓_ : ℙ (B × Ob) (o ⊔ ℓ′) → Ob → 𝒰 (o ⊔ ℓ ⊔ ℓ′)
  φ ↓ a = Σ[ b ꞉ B ] ∃[ a' ꞉ Ob ] (b , a') ∈ φ × a' ≤ a

  ↓→base : (ϕ : ℙ (B × Ob) (o ⊔ ℓ′)) → (a : Ob) → ϕ ↓ a → B
  ↓→base ϕ a = fst

  ↓-monotonicity-lemma : (ϕ : ℙ (B × Ob) (o ⊔ ℓ′))
                       → (x y : Ob) → x ≤ y
                       → ϕ ↓ x → ϕ ↓ y
  ↓-monotonicity-lemma ϕ x y le (b , c) = b , map (second $ second λ le0 → ≤-trans le0 le) c

  ↓-has-sup-implies-monotone : (ϕ : ℙ (B × Ob) (o ⊔ ℓ′))
                             → (x y s s' : Ob) → x ≤ y
                             → is-lub P (β ∘ ↓→base ϕ x) s
                             → is-lub P (β ∘ ↓→base ϕ y) s'
                             → s ≤ s'
  ↓-has-sup-implies-monotone ϕ x y s s' le lu1 lu2 =
    lu1 .least s' $ lu2 .fam≤lub ∘ ↓-monotonicity-lemma ϕ x y le

  is-local : (ϕ : ℙ (B × Ob) (o ⊔ ℓ′)) → 𝒰 (o ⊔ ℓ ⊔ ℓsuc ℓ′)
  is-local ϕ = (a : Ob) → is-of-size ℓ′ (ϕ ↓ a)

  module _ (ϕ : ℙ (B × Ob) (o ⊔ ℓ′)) (loc : is-local ϕ) where

    private
      S' : Ob → 𝒰 ℓ′
      S' a = ⌞ loc a ⌟

      S'≃↓ : (a : Ob) → S' a ≃ ϕ ↓ a
      S'≃↓ a = resizing-cond (loc a)

      S'→↓ : (a : Ob) → S' a → ϕ ↓ a
      S'→↓ a = S'≃↓ a $_

      ↓→S' : (a : Ob) → ϕ ↓ a → S' a
      ↓→S' a = S'≃↓ a ⁻¹ $_

      S'-monotone-ish : (x y : Ob) → x ≤ y
                      → S' x → S' y
      S'-monotone-ish x y o =
       ↓→S' y ∘ ↓-monotonicity-lemma ϕ x y o ∘ S'→↓ x

    Γ : Ob → Ob
    Γ a = sup (β ∘ fst ∘ S'→↓ a)

    Γ-is-monotone : ∀ {x y} → x ≤ y → Γ x ≤ Γ y
    Γ-is-monotone {x} {y} le =
      ↓-has-sup-implies-monotone ϕ x y (Γ x) (Γ y) le
         (sup-of-small-fam-is-lub L (β ∘ ↓→base ϕ x) (loc x))
         (sup-of-small-fam-is-lub L (β ∘ ↓→base ϕ y) (loc y))

  monotone-map-give-local-ind-def : (f : Ob → Ob)
                                  → (∀ {x y} → x ≤ y → f x ≤ f y)
                                  → Σ[ ϕ ꞉ ℙ (B × Ob) (o ⊔ ℓ′) ] Σ[ loc ꞉ is-local ϕ ] ((x : Ob) → Γ ϕ loc x ＝ f x)
  monotone-map-give-local-ind-def f f-mono = ϕ , loc , H
    where
      ϕ : ℙ (B × Ob) (o ⊔ ℓ′)
      ϕ (b , a) = el (Lift o (b ≤ᴮ f a)) (≃→is-of-hlevel 1 lift≃id ≤ᴮ-is-prop)

      ↓ᴮf-equiv-↓-tot : (a : Ob) → small-↓ᴮ (f a) ≃ (ϕ ↓ a)
      ↓ᴮf-equiv-↓-tot a =
        Σ-ap-snd λ b →
          prop-extₑ ≤ᴮ-is-prop (hlevel 1)
            (λ le → ∣ a , lift le , refl ∣₁)
            (∥-∥₁.elim (λ _ → ≤ᴮ-is-prop)
               λ where (a' , lo , le') → ≤→≤ᴮ (≤-trans (≤ᴮ→≤ (lift≃id $ lo)) (f-mono le')))

      loc : is-local ϕ
      loc a = small-↓ᴮ (f a) , ↓ᴮf-equiv-↓-tot a

      G : (x : Ob) → is-lub P (β ∘ ↓→base ϕ x) (f x)
      G x .fam≤lub (b , e) = elim! (λ a' lo le' → ≤-trans (≤ᴮ→≤ lo) (f-mono le')) e
      G x .least u' ub     = is-lubᴮ u' (ub ∘ (↓ᴮf-equiv-↓-tot x $_))

      H : (x : Ob) → Γ ϕ loc x ＝ f x
      H x = reindexing-along-equiv-=-sup {P = P} refl (β ∘ ↓→base ϕ x) (Γ ϕ loc x) (f x)
             (sup-of-small-fam-is-lub L (β ∘ ↓→base ϕ x) (loc x)) (G x)

  ind-def-from-monotone-map : (f : Ob → Ob)
                            → (∀ {x y} → x ≤ y → f x ≤ f y)
                            → ℙ (B × Ob) (o ⊔ ℓ′)
  ind-def-from-monotone-map f f-mono = monotone-map-give-local-ind-def f f-mono .fst

  local-from-monotone-map : (f : Ob → Ob)
                          → (f-mono : ∀ {x y} → x ≤ y → f x ≤ f y)
                          → is-local (ind-def-from-monotone-map f f-mono)
  local-from-monotone-map f f-mono = monotone-map-give-local-ind-def f f-mono .snd .fst

  local-ind-def-is-section-of-Γ : (f : Ob → Ob)
                                → (f-mono : ∀ {x y} → x ≤ y → f x ≤ f y)
                                → (x : Ob)
                                → Γ (ind-def-from-monotone-map f f-mono) (local-from-monotone-map f f-mono) x ＝ f x
  local-ind-def-is-section-of-Γ f f-mono = monotone-map-give-local-ind-def f f-mono .snd .snd

module _ {o ℓ ℓ′} {B : 𝒰 ℓ′}
         (P : Poset o ℓ)
         (L : is-sup-lattice P ℓ′)
         (β : B → ⌞ P ⌟)
         (h : is-basis P L β)
       where

  open Poset P
  open is-lub
  open is-sup-lattice L
  open is-basis h
  open local-inductive-definitions P L β h

  module correspondance-from-locally-small-ϕ
           (ϕ : ℙ (B × Ob) (o ⊔ ℓ′))
           (loc : is-local ϕ)
        where

    is-small-closed-subset : ℙ B ℓ′ → 𝒰 (o ⊔ ℓsuc ℓ′)
    is-small-closed-subset S = c-closure P L β h S × Φ-closure P L β h ϕ S

    is-small-closed-subset-is-prop : (P : ℙ B ℓ′) → is-prop (is-small-closed-subset P)
    is-small-closed-subset-is-prop P = hlevel 1

    small-closed-subsets : 𝒰 (o ⊔ ℓsuc ℓ′)
    small-closed-subsets = Σ[ P ꞉ ℙ B ℓ′ ] is-small-closed-subset P

    is-deflationary : Ob → 𝒰 ℓ
    is-deflationary a = Γ ϕ loc a ≤ a

    is-deflationary-is-prop : (a : Ob) → is-prop (is-deflationary a)
    is-deflationary-is-prop a = hlevel 1

    deflationary-points : 𝒰 (o ⊔ ℓ)
    deflationary-points = Σ[ a ꞉ Ob ] is-deflationary a

    small-closed-subsets→def-points : small-closed-subsets → deflationary-points
    small-closed-subsets→def-points (P , cc , φc) =
        sup-of-P
      , sup-of-small-fam-is-lub L (β ∘ ↓→base ϕ sup-of-P) (loc sup-of-P) .least sup-of-P
          λ where (b , e) →
                    rec! (λ a p le →
                           suprema (ℙ→fam β P .snd) .fam≤lub
                             (b , φc a b p λ b' le' →
                                              cc P refl b' (≤→≤ᴮ (≤-trans (≤ᴮ→≤ le') le))))
                         e
      where
        sup-of-P : Ob
        sup-of-P = sup (ℙ→fam β P .snd)

    def-points→small-closed-subsets : deflationary-points → small-closed-subsets
    def-points→small-closed-subsets (a , isdef) =
      Q a , Q-c-closed , Q-φ-closed
      where
        Q : Ob → ℙ B ℓ′
        Q x b = el (b ≤ᴮ x) ≤ᴮ-is-prop

        sup-Q : Ob → Ob
        sup-Q x = sup (ℙ→fam β (Q x) .snd)

        is-sup-Q : (x : Ob) → sup-Q x ＝ x
        is-sup-Q x = is-supᴮ' ⁻¹

        Q-c-closed : c-closure P L β h (Q a)
        Q-c-closed U C b le =
          ≤→≤ᴮ $ ≤-trans (≤ᴮ→≤ le) $
          subst (sup (ℙ→fam β U .snd) ≤_) (is-sup-Q a)
                (joins-preserve-containment L β U (Q a) C)

        Q-φ-closed : Φ-closure P L β h ϕ (Q a)
        Q-φ-closed a' b p f =
          ≤→≤ᴮ $ ≤-trans
            (sup-of-small-fam-is-lub L (β ∘ ↓→base ϕ a) (loc a) .fam≤lub
              (b , ∣ a' , p , subst (_≤ a) (is-sup-Q a')
                                (subst (sup-Q a' ≤_) (is-sup-Q a)
                                   (joins-preserve-containment L β (Q a') (Q a) (λ {z} → f z))) ∣₁))
            isdef

    @0 small-closed-subsets≃def-points : small-closed-subsets ≃ deflationary-points
    small-closed-subsets≃def-points =
        small-closed-subsets→def-points
      , is-iso→is-equiv (iso def-points→small-closed-subsets ri li)
      where
      ri : def-points→small-closed-subsets is-right-inverse-of small-closed-subsets→def-points
      ri (a , isdef) = Σ-prop-path is-deflationary-is-prop (is-supᴮ' ⁻¹)

      @0 li : def-points→small-closed-subsets is-left-inverse-of small-closed-subsets→def-points
      li (P , cc , φc) =
        Σ-prop-path is-small-closed-subset-is-prop
          (fun-ext λ b → n-ua (prop-extₑ ≤ᴮ-is-prop (hlevel 1)
                                 (cc P refl b)
                                 λ r → ≤→≤ᴮ (suprema (ℙ→fam β P .snd) .fam≤lub (b , r))))

    module small-𝓘nd-from-exists where

      open trunc-ind-def P L β h ϕ

      module smallness-assumption (j : (b : B) → is-of-size ℓ′ (b ∈ 𝓘nd)) where

        private

          𝓘' : B → 𝒰 ℓ′
          𝓘' b = ⌞ j b ⌟

          𝓘'≃𝓘nd : (b : B) → 𝓘' b ≃ b ∈ 𝓘nd
          𝓘'≃𝓘nd b = resizing-cond (j b)

          𝓘'→𝓘nd : (b : B) → 𝓘' b → b ∈ 𝓘nd
          𝓘'→𝓘nd b = 𝓘'≃𝓘nd b $_

          𝓘nd→𝓘' : (b : B) → b ∈ 𝓘nd → 𝓘' b
          𝓘nd→𝓘' b = 𝓘'≃𝓘nd b ⁻¹ $_

          𝓘'-is-prop : {b : B} → is-prop (𝓘' b)
          𝓘'-is-prop {b} = ≃→is-of-hlevel 1 (𝓘'≃𝓘nd b) (𝓘-trunc b)

          𝓘'-subset : ℙ B ℓ′
          𝓘'-subset b = el (𝓘' b) 𝓘'-is-prop

          𝓘'-is-c-closed : c-closure P L β h 𝓘'-subset
          𝓘'-is-c-closed U C b le = 𝓘nd→𝓘' b (𝓘nd-is-c-closed U (λ {x} → 𝓘'→𝓘nd x ∘ C) b le)

          𝓘'-is-ϕ-closed : Φ-closure P L β h ϕ 𝓘'-subset
          𝓘'-is-ϕ-closed a b p f = 𝓘nd→𝓘' b (𝓘nd-is-ϕ-closed a b p (λ b' → 𝓘'→𝓘nd b' ∘ f b'))

          total-space-𝓘-is-small : is-of-size ℓ′ Σ[ 𝓘nd ]
          total-space-𝓘-is-small = Σ[ 𝓘'-subset ] , Σ-ap-snd 𝓘'≃𝓘nd

          e : Σ[ 𝓘'-subset ] ≃ Σ[ 𝓘nd ]
          e = resizing-cond total-space-𝓘-is-small

          sup-𝓘 : Ob
          sup-𝓘 = sup {I = Σ[ 𝓘'-subset ]} (β ∘ 𝕋→carrier 𝓘nd ∘ (e $_))

          sup-𝓘-is-lub : is-lub P (ℙ→fam β 𝓘nd .snd) sup-𝓘
          sup-𝓘-is-lub = sup-of-small-fam-is-lub L (β ∘ 𝕋→carrier 𝓘nd) total-space-𝓘-is-small

        sup-𝓘-is-fixed-point : Γ ϕ loc sup-𝓘 ＝ sup-𝓘
        sup-𝓘-is-fixed-point =
          ≤-antisym Γ-sup-below-sup $
          subst (sup-𝓘 ≤_) sup-Q-is-Γ-sup sup-𝓘-below-sup-Q
          where
          Γ-sup-below-sup : Γ ϕ loc sup-𝓘 ≤ sup-𝓘
          Γ-sup-below-sup =
            small-closed-subsets→def-points (𝓘'-subset , 𝓘'-is-c-closed , 𝓘'-is-ϕ-closed) .snd

          Q-Γ-sc-sub : small-closed-subsets
          Q-Γ-sc-sub = def-points→small-closed-subsets
                         (Γ ϕ loc sup-𝓘 , Γ-is-monotone ϕ loc Γ-sup-below-sup)

          Q-Γ-sup : ℙ B ℓ′
          Q-Γ-sup = Q-Γ-sc-sub .fst
          Q-is-c-closed : c-closure P L β h Q-Γ-sup
          Q-is-c-closed = Q-Γ-sc-sub .snd .fst
          Q-is-ϕ-closed : Φ-closure P L β h ϕ Q-Γ-sup
          Q-is-ϕ-closed = Q-Γ-sc-sub .snd .snd

          sup-Q : Ob
          sup-Q = sup (ℙ→fam β Q-Γ-sup .snd)

          sup-Q-is-Γ-sup : sup-Q ＝ Γ ϕ loc sup-𝓘
          sup-Q-is-Γ-sup = is-supᴮ' ⁻¹

          sup-𝓘-below-sup-Q : sup-𝓘 ≤ sup-Q
          sup-𝓘-below-sup-Q =
            joins-preserve-containment L β 𝓘'-subset Q-Γ-sup
              λ {x} → 𝓘nd-is-initial Q-Γ-sup Q-is-c-closed Q-is-ϕ-closed ∘ 𝓘'→𝓘nd x


        sup-𝓘-is-least-fixed-point : (a : Ob)
                                   → Γ ϕ loc a ＝ a → sup-𝓘 ≤ a
        sup-𝓘-is-least-fixed-point a p =
          subst (sup-𝓘 ≤_) sup-P-is-a sup-𝓘-below-sup-P
          where
            P-sc-sub : small-closed-subsets
            P-sc-sub = def-points→small-closed-subsets (a , subst (Γ ϕ loc a ≤_) p refl)

            P-a : ℙ B ℓ′
            P-a = P-sc-sub .fst
            P-is-c-closed : c-closure P L β h P-a
            P-is-c-closed = P-sc-sub .snd .fst
            P-is-ϕ-closed : Φ-closure P L β h ϕ P-a
            P-is-ϕ-closed = P-sc-sub .snd .snd

            sup-P : Ob
            sup-P = sup (ℙ→fam β P-a .snd)

            sup-P-is-a : sup-P ＝ a
            sup-P-is-a = is-supᴮ' ⁻¹

            sup-𝓘-below-sup-P : sup-𝓘 ≤ sup-P
            sup-𝓘-below-sup-P =
              joins-preserve-containment L β 𝓘'-subset P-a
                 λ {x} → 𝓘nd-is-initial P-a P-is-c-closed P-is-ϕ-closed ∘ 𝓘'→𝓘nd x

        Γ-has-least-fixed-point : has-lfp P (Γ ϕ loc)
        Γ-has-least-fixed-point =
          (sup-𝓘 , sup-𝓘-is-fixed-point , sup-𝓘-is-least-fixed-point)

module bounded-inductive-definitions {o ℓ ℓ′}
         {B : 𝒰 ℓ′}
         (P : Poset o ℓ)
         (L : is-sup-lattice P ℓ′)
         (β : B → ⌞ P ⌟)
         (h : is-basis P L β)
       where

  open Poset P
  open is-lub
  open is-sup-lattice L
  open is-basis h
  open local-inductive-definitions P L β h

  _is-a-small-cover-of_ : ∀ {ℓ″} → 𝒰 ℓ′ → 𝒰 ℓ″ → 𝒰 (ℓ′ ⊔ ℓ″)
  X is-a-small-cover-of Y = X ↠ Y

  covering-cond : {ϕ : ℙ (B × Ob) (o ⊔ ℓ′)}
                → (T : 𝒰 ℓ′) → (T → 𝒰 ℓ′) → 𝒰 (o ⊔ ℓ ⊔ ℓ′)
  covering-cond {ϕ} T α = (a : Ob) → (b : B) → (b , a) ∈ ϕ
                        → ∃[ t ꞉ T ] α t is-a-small-cover-of ↓ᴮ P L β a

  has-a-bound : ℙ (B × Ob) (o ⊔ ℓ′) → 𝒰 (o ⊔ ℓ ⊔ ℓsuc ℓ′)
  has-a-bound ϕ = Σ[ T ꞉ 𝒰 ℓ′ ] Σ[ α ꞉ (T → 𝒰 ℓ′) ] covering-cond {ϕ} T α

  is-bounded : ℙ (B × Ob) (o ⊔ ℓ′) → 𝒰 (o ⊔ ℓ ⊔ ℓsuc ℓ′)
  is-bounded ϕ = ((a : Ob) → (b : B) → is-of-size ℓ′ ((b , a) ∈ ϕ)) × has-a-bound ϕ

  bounded→local : (ϕ : ℙ (B × Ob) (o ⊔ ℓ′))
                → is-bounded ϕ → is-local ϕ
  bounded→local ϕ (ϕ-small , ϕ-has-bound) a =
    ≃→is-of-size (≅→≃ (S₀→↓ , iso ↓→S₀ ri li))
      S₀-is-small
    where
      T : 𝒰 ℓ′
      T = ϕ-has-bound .fst
      α : T → 𝒰 ℓ′
      α = ϕ-has-bound .snd .fst
      cov : covering-cond {ϕ} T α
      cov = ϕ-has-bound .snd .snd

      S₀ : 𝒰 (o ⊔ ℓ ⊔ ℓ′)
      S₀ = Σ[ b ꞉ B ] ∃[ t ꞉ T ] Σ[ m ꞉ (α t → ↓ᴮ P L β a) ] (b , sup (↓ᴮ-inclusion P L β a ∘ m)) ∈ ϕ

      S₀-is-small : is-of-size ℓ′ S₀
      S₀-is-small = Σ-is-of-size (B , refl) λ b →
                    ∥-∥₁.∥-∥₁-is-of-size $
                    Σ-is-of-size (T , refl) λ t →
                    Σ-is-of-size (Π-is-of-size (α t , refl) λ _ → ↓ᴮ-is-small)
                      λ m → ϕ-small (sup (↓ᴮ-inclusion P L β a ∘ m)) b

      S₀→↓-aux : {b : B}
               → Σ[ t ꞉ T ] Σ[ m ꞉ (α t → ↓ᴮ P L β a) ] (b , sup (↓ᴮ-inclusion P L β a ∘ m)) ∈ ϕ
               → Σ[ a' ꞉ Ob ] ((b , a') ∈ ϕ × a' ≤ a)
      S₀→↓-aux (t , m , p) =
          sup (↓ᴮ-inclusion P L β a ∘ m) , p
        , suprema (↓ᴮ-inclusion P L β a ∘ m) .least a (↓-is-sup a .fam≤lub ∘ m)

      S₀→↓ : S₀ → ϕ ↓ a
      S₀→↓ = second (map S₀→↓-aux)

      g : {b : B} (a' : Ob) (p : (b , a') ∈ ϕ) (le : a' ≤ a)
        → Σ[ t ꞉ T ] α t is-a-small-cover-of ↓ᴮ P L β a'
        → Σ[ t ꞉ T ] Σ[ m ꞉ (α t → ↓ᴮ P L β a) ] (b , sup (↓ᴮ-inclusion P L β a ∘ m)) ∈ ϕ
      g {b} a' p le (t , α-c) =
          t , g-m , subst (λ z → (b , z) ∈ ϕ) g-path p
        where
        g-m :  α t → ↓ᴮ P L β a
        g-m = ↓ᴮ-≤ P L β le ∘ (α-c $_)
        g-path : a' ＝ sup (↓ᴮ-inclusion P L β a ∘ g-m)
        g-path = reindexing-along-surj-=-sup α-c (β ∘ fst) a' (sup (↓ᴮ-inclusion P L β a ∘ₜ g-m))
                   {!!}
                   {!!}

      cur-trunc-g : {b : B} (a' : Ob) (p : (b , a') ∈ ϕ) (le : a' ≤ a)
                  → ∃[ t ꞉ T ] Σ[ m ꞉ (α t → ↓ᴮ P L β a) ] (b , sup (↓ᴮ-inclusion P L β a ∘ m)) ∈ ϕ
      cur-trunc-g {b} a' p le = map (g a' p le) (cov a' b p)

      ↓→S₀ : ϕ ↓ a → S₀
      ↓→S₀ = second (rec! cur-trunc-g)

      ri : ↓→S₀ is-right-inverse-of S₀→↓
      ri = {!!}

      li : ↓→S₀ is-left-inverse-of S₀→↓
      li = {!!}
