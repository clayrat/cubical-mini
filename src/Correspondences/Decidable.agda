{-# OPTIONS --safe #-}
module Correspondences.Decidable where

open import Meta.Prelude

open import Meta.Reflection.Base
open import Meta.Reflection.Signature
open import Meta.Reflection.Subst
open import Meta.Search.HLevel

open import Structures.n-Type

open import Correspondences.Base public
open import Correspondences.Classical

open import Data.Bool.Base
open import Data.Bool.Path
open import Data.Dec.Base as Dec
open import Data.Empty.Base as ⊥
open import Data.List.Instances.FromProduct
open import Data.Nat.Base
open import Data.Reflects.Path
open import Data.Reflects.Properties

private variable
  ℓ ℓᵃ ℓᵇ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ
  n : HLevel

dec→essentially-classical : Dec A → Essentially-classical A
dec→essentially-classical = Dec.rec
  (λ a _ → a)
  (λ ¬a f → ⊥.rec $ f ¬a)

decide : ⦃ d : Dec A ⦄ → Dec A
decide ⦃ d ⦄ = d

×-decision : Dec A → Dec B → Dec (A × B)
×-decision da db .does = da .does and db .does
×-decision (no ¬a) db .proof = ofⁿ $ ¬a ∘′ fst
×-decision (yes a) (no ¬b) .proof = ofⁿ $ ¬b ∘′ snd
×-decision (yes a) (yes b) .proof = ofʸ (a , b)

fun-decision : Dec A → Dec B → Dec (A → B)
fun-decision da db .does = not (da .does) or db .does
fun-decision (no ¬a) db .proof = ofʸ $ λ a → ⊥.rec $ ¬a a
fun-decision (yes a) (no ¬b) .proof = ofⁿ $ ¬b ∘′ (_$ a)
fun-decision (yes a) (yes b) .proof = ofʸ λ _ → b

¬-decision : Dec A → Dec (¬ A)
¬-decision da .does = not (da .does)
¬-decision (yes a) .proof = ofⁿ (_$ a)
¬-decision (no ¬a) .proof = ofʸ ¬a

lift-decision : Dec A → Dec (Lift ℓ A)
lift-decision da .does = da .does
lift-decision (yes a) .proof = ofʸ (lift a)
lift-decision (no ¬a) .proof = ofⁿ (¬a ∘′ lower)

instance
  universe-decision : Dec (Type ℓ)
  universe-decision = yes (Lift _ ⊤)


-- Decidability of a generalized predicate
Decidableⁿ : Variadic-binding¹
Decidableⁿ {arity} P = Π[ mapⁿ arity Dec ⌞ P ⌟ ]

macro
  Decidable : Term → Term → TC ⊤
  Decidable t hole = do
    ar , r ← variadic-worker t
    und ← variadic-instance-worker r
    unify hole
      $   it Decidableⁿ ##ₕ ar ##ₕ unknown ##ₕ unknown
      ##ₕ unknown ##ₕ unknown ##ᵢ und ##ₙ t

-- Decision procedure
DProc
  : (arity : ℕ)
    {ls : Levels arity} (As : Types _ ls)
  → Type (ℓsup arity ls)
DProc arity As = Arrows arity As Bool

DProc⁰ = DProc 0
DProc¹ = DProc 1
DProc² = DProc 2
DProc³ = DProc 3
DProc⁴ = DProc 4
DProc⁵ = DProc 5

-- Evidence of a correspondence `P` being reflected by a decision procedure
Reflectsⁿ
  : {arity : ℕ} {ls : Levels arity} {As : Types _ ls}
    {ℓ : Level} {U : Type ℓ} ⦃ u : Underlying U ⦄
  → SCorr _ As U → DProc _ As → Type (u .ℓ-underlying ⊔ ℓsup _ ls)
Reflectsⁿ {0}                         P d = Reflects⁰ ⌞ P ⌟⁰ d
Reflectsⁿ {1}           {As = A}      P d = Π[ x ꞉ A ] Reflectsⁿ (P x) (d x)
Reflectsⁿ {suc (suc _)} {As = A , As} P d = Π[ x ꞉ A ] Reflectsⁿ (P x) (d x)

reflectsⁿ-is-of-hlevel
  : {arity : ℕ} {ls : Levels arity} {As : Types _ ls}
    {ℓ : Level} {U : Type ℓ} ⦃ u : Underlying U ⦄
    {h : HLevel} {P : SCorr _ As U} {d : DProc _ As}
  → Π[ mapⁿ arity (is-of-hlevel (suc h)) ⌞ P ⌟ ]
  → is-of-hlevel (suc h) (Reflectsⁿ P d)
reflectsⁿ-is-of-hlevel {0} = reflects-is-of-hlevel _
reflectsⁿ-is-of-hlevel {1} hl = Π-is-of-hlevel _ λ _ →
  reflects-is-of-hlevel _ (hl _)
reflectsⁿ-is-of-hlevel {suc (suc arity)} hl = Π-is-of-hlevel _ λ _ →
  reflectsⁿ-is-of-hlevel (hl _)

macro
  Reflects : Term → Term → Term → TC ⊤
  Reflects c d hole = do
    car , r ← variadic-worker c
    dar , _ ← variadic-worker d
    unify car dar
    und ← variadic-instance-worker r
    unify hole
      $   it Reflectsⁿ ##ₕ car ##ₕ unknown ##ₕ unknown
      ##ₕ unknown ##ₕ unknown ##ᵢ und ##ₙ c ##ₙ d

reflectsⁿ-bool-inj
  : {arity : ℕ} {ls : Levels arity} {As : Types _ ls}
    {ℓ : Level} {U : Type ℓ} ⦃ u : Underlying U ⦄
    {P : SCorr _ As U} {d₁ d₂ : DProc _ As}
  → Reflects P d₁ → Reflects P d₂
  → d₁ ＝ d₂
reflectsⁿ-bool-inj {0} = reflects-bool-inj
reflectsⁿ-bool-inj {1} r₁ r₂ = fun-ext λ x → reflects-bool-inj (r₁ x) (r₂ x)
reflectsⁿ-bool-inj {suc (suc _)} r₁ r₂ = fun-ext λ x → reflectsⁿ-bool-inj (r₁ x) (r₂ x)

reflects→decidable
  : {arity : ℕ} {ls : Levels arity} {As : Types _ ls}
    {ℓ : Level} {U : Type ℓ} ⦃ u : Underlying U ⦄
    {P : SCorr _ As U} {d : DProc _ As}
  → Reflects P d → Decidable P
reflects→decidable {0}          {d} p   = d because p
reflects→decidable {1}          {d} f x = d x because f x
reflects→decidable {suc (suc _)}    f x = reflects→decidable (f x)

opaque
  unfolding is-of-hlevel
  decidable₁→reflects!
    : {arity : ℕ} {ls : Levels arity} {As : Types _ ls}
      {ℓ : Level} {P : Rel _ As ℓ}
    → Decidable P → ∃![ d ꞉ DProc _ As ] Reflects P d
  decidable₁→reflects! {0} p =
      (p .does , p .proof)
    , λ z → Σ-prop-path! $ reflects-bool-inj (z .snd) (p .proof) ⁻¹
  decidable₁→reflects! {1} f =
      (does ∘ f  , proof ∘ f)
    , λ z → Σ-prop-path! $ fun-ext λ x → reflects-bool-inj (z .snd x) (f x .proof) ⁻¹
  decidable₁→reflects! {suc (suc arity)} {As} {ℓ} {P} f =
    let ih = decidable₁→reflects!
    in ((λ x → ih (f x) .fst .fst) , λ x → ih (f x) .fst .snd)
      , λ z → Σ-prop-path (λ _ → reflectsⁿ-is-of-hlevel {arity = suc (suc arity)} {h = 0} $ corr→is-of-hlevelⁿ {arity = suc (suc arity)})
                          (fun-ext λ x → let u = ih (f x) .snd (z .fst x , z .snd x) in ap fst u)
