{-# OPTIONS --safe #-}
module Data.Dec.Base where

open import Foundations.Base

open import Data.Bool.Base as Bool
  using (Bool; false; true; not; if_then_else_; is-true)
open import Data.Empty.Base as ⊥
  using ()

open import Data.Reflects.Base as Reflects
  using (Reflects⁰; ofⁿ; ofʸ)
  public

private variable
  ℓ ℓ′ ℓ″ : Level
  P : Type ℓ
  Q : Type ℓ′
  a b : Bool

-- witness of a predicate being (already) decided
infix 2 _because_
record Dec {ℓ} (P : Type ℓ) : Type ℓ where
  constructor _because_
  field
    does  : Bool
    proof : Reflects⁰ P does
open Dec public

pattern yes p =  true because ofʸ  p
pattern no ¬p = false because ofⁿ ¬p

elim : {C : Dec P → Type ℓ′}
     → (( p :   P) → C (yes p))
     → ((¬p : ¬ P) → C (no ¬p))
     → (d : Dec P) → C d
elim y n (no ¬p) = n ¬p
elim y n (yes p) = y p

elim² : {C : Dec P → Dec Q → Type ℓ″}
      → (( p :   P) → ( q :   Q) → C (yes p) (yes q))
      → (( p :   P) → (¬q : ¬ Q) → C (yes p) (no ¬q))
      → ((¬p : ¬ P) → ( q :   Q) → C (no ¬p) (yes q))
      → ((¬p : ¬ P) → (¬q : ¬ Q) → C (no ¬p) (no ¬q))
      → (p : Dec P) → (q : Dec Q) → C p q
elim² yy yn ny nn (no ¬p) (no ¬q) = nn ¬p ¬q
elim² yy yn ny nn (no ¬p) (yes q) = ny ¬p q
elim² yy yn ny nn (yes p) (no ¬q) = yn p ¬q
elim² yy yn ny nn (yes p) (yes q) = yy p q

dmap : (P → Q) → (¬ P → ¬ Q) → Dec P → Dec Q
dmap to fro dec .does  = dec .does
dmap to fro dec .proof = Reflects.dmap to fro (dec .proof)

recover : Dec P → Recomputable P
recover (yes p) _  = p
recover (no ¬p) (erase 0p) = ⊥.rec (¬p 0p)

recover′ : Dec P → @irr P → P
recover′ (yes p) _ = p
recover′ (no ¬p) p = ⊥.rec′ (¬p p)

rec : (P → Q) → (¬ P → Q) → Dec P → Q
rec {Q} = elim {C = λ _ → Q}

⌊_⌋ : Dec P → Bool
⌊ b because _ ⌋ = b

is-trueᵈ : Dec P → Type
is-trueᵈ = is-true ∘ ⌊_⌋

caseᵈ_of_ : (A : Type ℓ) ⦃ d : Dec A ⦄ {B : Type ℓ′}
          → (Dec A → B) → B
caseᵈ_of_ A ⦃ d ⦄ f = f d
{-# INLINE caseᵈ_of_ #-}

caseᵈ_return_of_ : (A : Type ℓ) ⦃ d : Dec A ⦄
                   (B : Dec A → Type ℓ)
                 → (∀ x → B x) → B d
caseᵈ_return_of_ A ⦃ d ⦄ B f = f d
{-# INLINE caseᵈ_return_of_ #-}

_~?_
  : {A : Type ℓ} {B : Type ℓ′} {_~_ : A → B → Type ℓ″}
    ⦃ d : {x : A} {y : B} → Dec (x ~ y) ⦄
  → (x : A) (y : B) → Dec (x ~ y)
_~?_ ⦃ d ⦄ _ _ = d

infix 30 _∈?_ _∈!?_

_∈?_
  : {A : Type ℓ} {ℙA : Type ℓ′} ⦃ m : Membership A ℙA ℓ″ ⦄
  → ⦃ d : {y : A} {ys : ℙA} → Dec (y ∈ ys) ⦄
  → (x : A) (xs : ℙA) → Dec (x ∈ xs)
_∈?_ = _~?_

_∈!?_
  : {A : Type ℓ} {ℙA : Type ℓ′} ⦃ m : Membership A ℙA ℓ″ ⦄
  → ⦃ d : {y : A} {ys : ℙA} → Dec (y ∈! ys) ⦄
  → (x : A) (xs : ℙA) → Dec (x ∈! xs)
_∈!?_ = _~?_
