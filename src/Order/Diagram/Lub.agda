{-# OPTIONS --safe #-}
module Order.Diagram.Lub where

open import Cat.Prelude
open import Functions.Surjection

open import Order.Base
import Order.Reasoning

private variable o o′ ℓ ℓ′ ℓᵢ : Level

module _ (P : Poset o ℓ) where
  open Poset P

  record is-lub
    {ℓᵢ} {I : 𝒰 ℓᵢ} (F : I → Ob) (lub : Ob)
    : Type (o ⊔ ℓ ⊔ ℓᵢ)
    where
    no-eta-equality
    field
      fam≤lub : ∀ i → F i ≤ lub
      least   : (ub′ : Ob) → (∀ i → F i ≤ ub′) → lub ≤ ub′

  record Lub {ℓᵢ} {I : 𝒰 ℓᵢ} (F : I → Ob) : 𝒰 (o ⊔ ℓ ⊔ ℓᵢ) where
    no-eta-equality
    field
      lub     : Ob
      has-lub : is-lub F lub
    open is-lub has-lub public

unquoteDecl H-Level-is-lub = declare-record-hlevel 1 H-Level-is-lub (quote is-lub)
unquoteDecl Lub-Iso = declare-record-iso Lub-Iso (quote Lub)

Has-lubs-of-size : Poset o ℓ → (ℓ′ : Level) → Type (o ⊔ ℓ ⊔ ℓsuc ℓ′)
Has-lubs-of-size P ℓ′ = {I : Type ℓ′} {F : I → ⌞ P ⌟} → Lub P F

module _ {P : Poset o ℓ} where
  open Order.Reasoning P
  open is-lub

  lub-unique
    : ∀ {ℓᵢ} {I : 𝒰 ℓᵢ} {F : I → Ob} {x y}
    → is-lub P F x → is-lub P F y
    → x ＝ y
  lub-unique {x} {y} lub lub′ = ≤-antisym
    (lub  .least y (lub′ .fam≤lub))
    (lub′ .least x (lub  .fam≤lub))

  Lub-is-prop
    : ∀ {ℓᵢ} {I : 𝒰 ℓᵢ} {F : I → Ob}
    → is-prop (Lub P F)
  Lub-is-prop = ≅→is-of-hlevel 1 Lub-Iso λ x y → lub-unique (x .snd) (y .snd) ,ₚ prop!

  instance opaque
    H-Level-Lub
      : ∀ {ℓᵢ} {I : Type ℓᵢ} {F : I → Ob} {n} ⦃ _ : 1 ≤ʰ n ⦄
      → H-Level n (Lub P F)
    H-Level-Lub ⦃ s≤ʰs _ ⦄ = hlevel-basic-instance 1 Lub-is-prop

  lift-is-lub
    : ∀ {ℓᵢ ℓᵢ′} {I : Type ℓᵢ} {F : I → Ob} {lub}
    → is-lub P F lub → is-lub P (F ∘ₜ Lift.lower {ℓ′ = ℓᵢ′}) lub
  lift-is-lub is .fam≤lub (lift ix) = is .fam≤lub ix
  lift-is-lub is .least ub′ le = is .least ub′ (le ∘ₜ lift)

  lift-lub
    : ∀ {ℓᵢ ℓᵢ′} {I : 𝒰 ℓᵢ} {F : I → Ob}
    → Lub P F → Lub P (F ∘ₜ Lift.lower {ℓ′ = ℓᵢ′})
  lift-lub lub .Lub.lub = Lub.lub lub
  lift-lub lub .Lub.has-lub = lift-is-lub (Lub.has-lub lub)

  lower-is-lub
    : ∀ {ℓᵢ ℓᵢ′} {I : 𝒰 ℓᵢ} {F : I → Ob} {lub}
    → is-lub P (F ∘ₜ Lift.lower {ℓ′ = ℓᵢ′}) lub → is-lub P F lub
  lower-is-lub is .fam≤lub ix = is .fam≤lub (lift ix)
  lower-is-lub is .least ub′ le = is .least ub′ (le ∘ₜ Lift.lower)

  lower-lub
    : ∀ {ℓᵢ ℓᵢ′} {I : 𝒰 ℓᵢ} {F : I → Ob}
    → Lub P (F ∘ₜ Lift.lower {ℓ′ = ℓᵢ′}) → Lub P F
  lower-lub lub .Lub.lub = Lub.lub lub
  lower-lub lub .Lub.has-lub = lower-is-lub (Lub.has-lub lub)

  module _
    {ℓᵢ ℓᵢ′} {Ix : Type ℓᵢ} {Im : Type ℓᵢ′}
    {F : Im → Ob} where
    module _ (f : Ix ↠ Im) where
      cover-preserves-is-lub : ∀ {lub} → is-lub P F lub → is-lub P (F ∘ₜ (f $_)) lub
      cover-preserves-is-lub l .fam≤lub x = l .fam≤lub (f $ x)
      cover-preserves-is-lub l .least   ub′ le = l .least ub′ λ i → ∥-∥₁.proj! do
        i′ , p ← f .snd i
        pure (=→≤ (ap F (p ⁻¹)) ∙ le i′)

      cover-preserves-lub : Lub P F → Lub P (F ∘ₜ (f $_))
      cover-preserves-lub l .Lub.lub = _
      cover-preserves-lub l .Lub.has-lub = cover-preserves-is-lub (l .Lub.has-lub)

      cover-reflects-is-lub : ∀ {lub} → is-lub P (F ∘ₜ (f $_)) lub → is-lub P F lub
      cover-reflects-is-lub l .fam≤lub x = ∥-∥₁.proj! do
        y , p ← f .snd x
        pure (=→≤ (ap F (p ⁻¹)) ∙ l .fam≤lub y)
      cover-reflects-is-lub l .least ub′ le = l .least ub′ λ i → le (f $ i)

      cover-reflects-lub : Lub P (F ∘ₜ (f $_)) → Lub P F
      cover-reflects-lub l .Lub.lub     = _
      cover-reflects-lub l .Lub.has-lub = cover-reflects-is-lub (l .Lub.has-lub)

      cover-reindexing : (s s′ : Ob) → is-lub P F s → is-lub P (F ∘ₜ (f $_)) s′ → s ＝ s′
      cover-reindexing s s′ l l′ = ≤-antisym
        (least l s′ λ t → elim! (λ x p → subst (λ φ → F φ ≤ s′) p (fam≤lub l′ x)) (f .snd t))
        (least l′ s λ t′ → fam≤lub l (f $ t′))

    module _ (f : Ix ≃ Im) where
      equiv-reindexing : (s s′ : Ob) → is-lub P F s → is-lub P (F ∘ₜ (f $_)) s′ → s ＝ s′
      equiv-reindexing = cover-reindexing (≃→↠ f)

  cast-is-lub
    : ∀ {ℓᵢ ℓᵢ′} {I : 𝒰 ℓᵢ} {I′ : 𝒰 ℓᵢ′} {F : I → Ob} {G : I′ → Ob} {lub}
    → (e : I ≃ I′)
    → (∀ i → F i ＝ G (e $ i))
    → is-lub P F lub
    → is-lub P G lub
  cast-is-lub {G} e p has-lub .fam≤lub i′
    = =→~⁻ (p (e ⁻¹ $ i′) ∙ ap G (Equiv.ε e # i′))
    ∙ has-lub .fam≤lub (e ⁻¹ $ i′)
  cast-is-lub e p has-lub .least ub G≤ub =
    has-lub .least ub (λ i → =→≤ (p i) ∙ G≤ub (e $ i))

  cast-lub
    : ∀ {ℓᵢ ℓᵢ′} {I : 𝒰 ℓᵢ} {I′ : 𝒰 ℓᵢ′} {F : I → Ob} {G : I′ → Ob}
    → (e : I ≃ I′)
    → (∀ i → F i ＝ G (e $ i))
    → Lub P F
    → Lub P G
  cast-lub e p l .Lub.lub     = l .Lub.lub
  cast-lub e p l .Lub.has-lub = cast-is-lub e p (l .Lub.has-lub)

  cast-is-lubᶠ
    : ∀ {ℓᵢ} {I : 𝒰 ℓᵢ} {F G : I → Ob} {lub}
    → (∀ i → F i ＝ G i)
    → is-lub P F lub
    → is-lub P G lub
  cast-is-lubᶠ = cast-is-lub refl

  fam-bound→is-lub
    : ∀ {ℓᵢ} {I : 𝒰 ℓᵢ} {F : I → Ob}
    → (i : I) → (∀ j → F j ≤ F i)
    → is-lub P F (F i)
  fam-bound→is-lub i ge .fam≤lub = ge
  fam-bound→is-lub i ge .least y le = le i

  lub-of-const-fam
    : ∀ {ℓᵢ} {I : 𝒰 ℓᵢ} {F : I → Ob} {x}
    → (∀ i j → F i ＝ F j)
    → is-lub P F x
    → ∀ i → F i ＝ x
  lub-of-const-fam {F = F} is-const x-lub i =
    ≤-antisym
      (fam≤lub x-lub i)
      (least x-lub (F i) λ j → =→≥ (is-const i j))

  const-inhabited-fam→is-lub
    : ∀ {ℓᵢ} {I : 𝒰 ℓᵢ} {F : I → Ob} {x}
    → (∀ i → F i ＝ x)
    → ∥ I ∥₁
    → is-lub P F x
  const-inhabited-fam→is-lub {I} {F} {x} is-const =
    rec! mk-is-lub where
      mk-is-lub : I → is-lub P F x
      mk-is-lub i .is-lub.fam≤lub j = =→≤ (is-const j)
      mk-is-lub i .is-lub.least y le =
        x    =⟨ is-const i ⟨
        F i  ≤⟨ le i ⟩
        y    ∎

  const-inhabited-fam→lub
    : ∀ {ℓᵢ} {I : 𝒰 ℓᵢ} {F : I → Ob}
    → (∀ i j → F i ＝ F j)
    → ∥ I ∥₁
    → Lub P F
  const-inhabited-fam→lub {I} {F} is-const =
    rec! mk-lub where
      mk-lub : I → Lub P F
      mk-lub i .Lub.lub = F i
      mk-lub i .Lub.has-lub =
        const-inhabited-fam→is-lub (λ j → is-const j i) ∣ i ∣₁


module _ {P : Poset o ℓ} {Q : Poset o′ ℓ′} {I : 𝒰 ℓᵢ} {F : I → ⌞ P ⌟} where
  private
    module P = Poset P
    module Q = Order.Reasoning Q
  open Iso

  ≅→is-lub : (e : P ≅ Q) {x : ⌞ P ⌟}
           → is-lub P F x → is-lub Q (F ∙ e #_) (e # x)
  ≅→is-lub e     l .is-lub.fam≤lub i = e .to # l .is-lub.fam≤lub i
  ≅→is-lub e {x} l .is-lub.least ub′ f
    = subst (e # x Q.≤_) (e .inv-o #ₚ ub′) -- TODO Galois connections
    $ e .to $ l .is-lub.least (e .from # ub′) λ i
    → =→~ (e .inv-i #ₚ F i ⁻¹) ∙ e .from # f i

  ≅→Lub : (e : P ≅ Q)
        → Lub P F → Lub Q (F ∙ e #_)
  ≅→Lub e l .Lub.lub = e # l .Lub.lub
  ≅→Lub e l .Lub.has-lub = ≅→is-lub e (l .Lub.has-lub)


module _ {P : Poset o ℓ} {Q : Poset o′ ℓ′} {I : 𝒰 ℓᵢ} {F : I → ⌞ Q ⌟} where
  private
    module P = Poset P
    module Q = Order.Reasoning Q
  open Iso

  ≅→is-lub⁻ : (e : P ≅ Q) {y : ⌞ Q ⌟}
            → is-lub P (F ∙ e .from #_) (e .from # y) → is-lub Q F y
  ≅→is-lub⁻ e {y} l = subst² (is-lub Q)
    (fun-ext λ i → e .inv-o #ₚ F i) (e .inv-o #ₚ y)
      (≅→is-lub e l)

  ≅→Lub⁻ : (e : P ≅ Q)
         → Lub P (F ∙ e .from #_) → Lub Q F
  ≅→Lub⁻ e l .Lub.lub = e .to # l .Lub.lub
  ≅→Lub⁻ e l .Lub.has-lub = ≅→is-lub⁻ e $
    subst (is-lub P (F ∙ e .from #_))
      (e .inv-i #ₚ l .Lub.lub ⁻¹)
      (l .Lub.has-lub)
