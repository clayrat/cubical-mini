{-# OPTIONS --safe #-}
module Data.List.Membership where

open import Foundations.Prelude

open import Meta.Extensionality
open import Meta.Membership

open import Logic.Discreteness

open import Data.Dec.Base as Dec
open import Data.Empty.Base as ⊥
open import Data.List.Base
open import Data.Maybe.Base
open import Data.Maybe.Path using (just-inj)

private variable
  ℓᵃ ℓ : Level
  A : Type ℓ
  a x y : A
  xs : List A

data _∈ₗ_ {ℓ} {A : Type ℓ} (x : A) : List A → Type ℓ where
  here  : (p : x ＝ y) → x ∈ₗ (y ∷ xs)
  there : x ∈ₗ xs      → x ∈ₗ (y ∷ xs)

here≠there : {p : x ＝ y} {q : x ∈ₗ xs} → here p ≠ there q
here≠there {q} w = subst discrim w tt where
  discrim : x ∈ₗ xs → Type
  discrim (here  _)  = ⊤
  discrim (there _) = ⊥

there≠here : {p : x ＝ y} {q : x ∈ₗ xs} → there q ≠ here p
there≠here = here≠there ∘ sym

here-inj : {p p′ : x ＝ y} → here {xs = xs} p ＝ here p′ → p ＝ p′
here-inj = just-inj ∘ ap unhere where
  unhere : x ∈ₗ (y ∷ xs) → Maybe (x ＝ y)
  unhere (here  p) = just p
  unhere (there _) = nothing

there-inj : {q q′ : x ∈ₗ xs} → there {y = y} q ＝ there q′ → q ＝ q′
there-inj = just-inj ∘ ap unthere where
  unthere : (a : x ∈ₗ (y ∷ xs)) → Maybe (x ∈ₗ xs)
  unthere (here  _) = nothing
  unthere (there q) = just q


instance
  Membership-List : ∀{ℓ} {A : Type ℓ}
                  → Membership A (List A) ℓ
  Membership-List ._∈_ = _∈ₗ_

  ∈ₗ-head
    : ∀ {ℓ} {A : Type ℓ} {x : A} {xs : List A}
    → x ∈ (x ∷ xs)
  ∈ₗ-head = here refl
  {-# OVERLAPPING ∈ₗ-head #-}

  ∈ₗ-tail
    : ∀ {ℓ} {A : Type ℓ} {x y : A} {xs : List A}
    → ⦃ x ∈ xs ⦄ → x ∈ (y ∷ xs)
  ∈ₗ-tail = there auto
  {-# OVERLAPPABLE ∈ₗ-tail #-}

module _ {A : 𝒰 ℓᵃ} ⦃ sa : ∀ {x y : A} → Extensional (x ＝ y) ℓ ⦄ where
  Code-∈ₗ : {x : A} {xs : List A} (p q : x ∈ xs) → 𝒰 ℓ
  Code-∈ₗ (here  p) (here  p′) = sa .Pathᵉ p p′
  Code-∈ₗ (there q) (there q′) = Code-∈ₗ q q′
  Code-∈ₗ _ _  = Lift _ ⊥

  code-∈ₗ-refl : {x : A} {xs : List A} (p : x ∈ xs) → Code-∈ₗ p p
  code-∈ₗ-refl (here  p) = sa .reflᵉ p
  code-∈ₗ-refl (there q) = code-∈ₗ-refl q

  decode-∈ₗ : {x : A} {xs : List A} {p q : x ∈ xs} (c : Code-∈ₗ p q) → p ＝ q
  decode-∈ₗ {p = here p}  {here  p′} c = ap here (sa .idsᵉ .to-path c)
  decode-∈ₗ {p = there q} {there q′} c = ap there (decode-∈ₗ c)

  decode-∈ₗ-refl
    : {x : A} {xs : List A} {p q : x ∈ xs} (c : Code-∈ₗ p q)
    → code-∈ₗ-refl p ＝[ ap (Code-∈ₗ p) (decode-∈ₗ c) ]＝ c
  decode-∈ₗ-refl {p = here  p} {here p′}  = sa .idsᵉ .to-path-over
  decode-∈ₗ-refl {p = there q} {there q′} = decode-∈ₗ-refl {p = q}

  Extensional-∈ₗ : {x : A} {xs : List A} → Extensional (x ∈ xs) ℓ
  Extensional-∈ₗ .Pathᵉ = Code-∈ₗ
  Extensional-∈ₗ .reflᵉ = code-∈ₗ-refl
  Extensional-∈ₗ .idsᵉ .to-path = decode-∈ₗ
  Extensional-∈ₗ .idsᵉ .to-path-over {a} = decode-∈ₗ-refl {p = a}

opaque
  -- TODO feels like it can be strengthened
  code-∈ₗ-is-of-hlevel
    : ∀ {n} {x : A} {xs : List A} {u v : x ∈ xs}
    → is-of-hlevel (2 + n) A → is-of-hlevel (1 + n) (Code-∈ₗ u v)
  code-∈ₗ-is-of-hlevel {u = here _} {here _} hl =
    path-is-of-hlevel-same (suc _) (hl _ _)
  code-∈ₗ-is-of-hlevel {u = here  _} {there _} _ = hlevel _
  code-∈ₗ-is-of-hlevel {u = there _} {here _}  _ = hlevel _
  code-∈ₗ-is-of-hlevel {u = there q} {there _} = code-∈ₗ-is-of-hlevel {u = q}

  ∈ₗ-is-of-hlevel
    : (n : HLevel) {x : A} {xs : List A}
    → is-of-hlevel (2 + n) A
    → is-of-hlevel (2 + n) (x ∈ xs)
  ∈ₗ-is-of-hlevel n hl =
    identity-system→is-of-hlevel (suc n) (Extensional-∈ₗ .idsᵉ) λ x _ → code-∈ₗ-is-of-hlevel {u = x} hl

instance opaque
  H-Level-∈ₗ : ∀ {n} {x : A} {xs : List A} → ⦃ A-hl : H-Level (2 + n) A ⦄ → H-Level (2 + n) (x ∈ xs)
  H-Level-∈ₗ {n} .H-Level.has-of-hlevel = ∈ₗ-is-of-hlevel n (hlevel (2 + n))

instance
  Dec-∈ₗ
    : {a : A} {xs : List A}
    → ⦃ di : is-discrete A ⦄
    → Dec (a ∈ xs)
  Dec-∈ₗ {xs = []} = no λ()
  Dec-∈ₗ {a} {xs = x ∷ xs} =
    caseᵈ a ＝ x of λ where
      (yes a=x) → yes (here a=x)
      (no  a≠x) → case Dec-∈ₗ {a = a} {xs = xs} of λ where
        (yes a∈xs) → yes (there a∈xs)
        (no  a∉xs) → no λ where
          (here  a=x)  → a≠x a=x
          (there a∈xs) → a∉xs a∈xs
  {-# OVERLAPPING Dec-∈ₗ #-}

  ∈ₗ-is-discrete
    : {a : A} {xs : List A}
    → ⦃ A-set : H-Level 2 A ⦄
    → is-discrete (a ∈ xs)
  ∈ₗ-is-discrete {a} {xs = x ∷ xs} {x = here p}  {here p′}  = yes (ap here prop!)
  ∈ₗ-is-discrete {a} {xs = x ∷ xs} {x = here p}  {there q}  = no here≠there
  ∈ₗ-is-discrete {a} {xs = x ∷ xs} {x = there q} {here p′}  = no there≠here
  ∈ₗ-is-discrete {a} {xs = x ∷ xs} {x = there q} {there q′} =
    case (∈ₗ-is-discrete {a = a} {xs = xs} {q} {q′}) of λ where
      (yes q=q′) → yes (ap there q=q′)
      (no  q≠q′) → no (contra there-inj q≠q′)
  {-# OVERLAPPING ∈ₗ-is-discrete #-}


here+there→∉!ₗ : a ＝ x → a ∈ xs → a ∉! (x ∷ xs)
here+there→∉!ₗ _   a∈xs (here  p , uniq) = here≠there $ uniq (there a∈xs)
here+there→∉!ₗ a=x _    (there q , uniq) = there≠here $ uniq (here a=x)

¬here+¬there!→∉!ₗ : a ≠ x → a ∉! xs → a ∉! (x ∷ xs)
¬here+¬there!→∉!ₗ a≠x _     (here  a=x  , _)    = a≠x a=x
¬here+¬there!→∉!ₗ _   a∉!xs (there a∈xs , uniq) = a∉!xs (a∈xs , there-inj ∘ uniq ∘ there)

here+¬there→∈!ₗ
  : {a x : A} {xs : List A} ⦃ A-set : H-Level 2 A ⦄
  → a ＝ x → a ∉ xs → a ∈! (x ∷ xs)
here+¬there→∈!ₗ a=x a∉xs = here a=x , λ where
  (here  _)    → ap here prop!
  (there a∈xs) → ⊥.rec (a∉xs a∈xs)

¬here+there!→∈!ₗ : a ≠ x → a ∈! xs → a ∈! (x ∷ xs)
¬here+there!→∈!ₗ a≠x (a∈xs , uniq) = there a∈xs , λ where
  (here  a=x)   → ⊥.rec (a≠x a=x)
  (there a∈xs′) → ap there (uniq a∈xs′)

instance
  Dec-∈!ₗ
    : {a : A} {xs : List A}
    → ⦃ di : is-discrete A ⦄
    → Dec (a ∈! xs)
  Dec-∈!ₗ {xs = []} = no λ ()
  Dec-∈!ₗ {a} {xs = x ∷ xs} =
    caseᵈ a ＝ x of λ where
      (yes a=x) → caseᵈ a ∈ xs of λ where
        (yes a∈xs) → no  (here+there→∉!ₗ  a=x a∈xs)
        (no  a∉xs) → yes (here+¬there→∈!ₗ a=x a∉xs)
      (no  a≠x) → case Dec-∈!ₗ {a = a} {xs} of λ where
        (yes a∈!xs) → yes (¬here+there!→∈!ₗ  a≠x a∈!xs)
        (no  a∉!xs) → no  (¬here+¬there!→∉!ₗ a≠x a∉!xs)
  {-# OVERLAPPING Dec-∈!ₗ #-}
