{-# OPTIONS --safe #-}
open import Cat.Prelude
open import Foundations.Equiv

-- open import Functions.Embedding renaming (_↪_ to _↣_)
--open import 1Lab.Equiv
--open import 1Lab.Path
-- open import 1Lab.Type hiding (id; _∘_)

open import Cat.Base

module Cat.Reasoning {o ℓ} (C : Precategory o ℓ) where

open import Cat.Morphism C public

private variable
  u v w x y z : Ob
  a a' a'' b b' b'' c c' c'' d d' d'' e : Hom x y
  f f' g g' h h' i i' k k' : Hom x y

-- Lenses
{-
module _ {w x y z} {a : Hom y z} {b : Hom x y} {c : Hom w x} {f : Hom w z} where abstract
  reassocl : ((a ∘ b) ∘ c ＝ f) ≃ (a ∘ b ∘ c ＝ f)
  reassocl = whisker-path-lₑ (assoc _ _ _) ⁻¹

  reassocr : (f ＝ (a ∘ b) ∘ c) ≃ (f ＝ a ∘ b ∘ c)
  reassocr = whisker-path-rₑ (sym (assoc _ _ _))

  module reassocl = Equiv reassocl
  module reassocr = Equiv reassocr
-}
-- Identity morphisms

abstract
  id-comm : ∀ {a b} {f : Hom a b} → f ∘ id ＝ id ∘ f
  id-comm {f = f} = ∙-id-o f ∙ sym (∙-id-i f)

  id-comm-sym : ∀ {a b} {f : Hom a b} → id ∘ f ＝ f ∘ id
  id-comm-sym {f = f} = ∙-id-i f ∙ sym (∙-id-o f)

  id2 : ∀ {x} → id {x} ∘ id {x} ＝ id
  id2 = ∙-id-i _

  ∙-id-o2 : ∀ {a b c} (f : Hom b c) (g : Hom a b) → f ∘ g ∘ id ＝ f ∘ g
  ∙-id-o2 f g = ap (f ∘_) (∙-id-o g)

  ∙-id-i2 : ∀ {a b c} (f : Hom b c) (g : Hom a b) → (id ∘ f) ∘ g ＝ f ∘ g
  ∙-id-i2 f g = ap (_∘ g) (∙-id-i f)

module _ (a＝id : a ＝ id) where abstract
  eliml : a ∘ f ＝ f
  eliml {f = f} =
    a ∘ f  ~⟨ ap (_∘ f) a＝id ⟩
    id ∘ f ~⟨ ∙-id-i f ⟩
    f ∎

  elimr : f ∘ a ＝ f
  elimr {f = f} =
    f ∘ a  ~⟨ ap (f ∘_) a＝id ⟩
    f ∘ id ~⟨ ∙-id-o f ⟩
    f ∎

  elim-inner : f ∘ a ∘ h ＝ f ∘ h
  elim-inner {f = f} = ap (f ∘_) eliml

  introl : f ＝ a ∘ f
  introl = sym eliml

  intror : f ＝ f ∘ a
  intror = sym elimr

  intro-inner : f ∘ h ＝ f ∘ a ∘ h
  intro-inner {f = f} = ap (f ∘_) introl

-- Reassocations
-- TODO assocs are flipped

module _ (ab＝c : a ∘ b ＝ c) where abstract
  pulll : a ∘ (b ∘ f) ＝ c ∘ f
  pulll {f = f} =
    a ∘ b ∘ f   ~⟨ assoc f b a ⁻¹ ⟩
    (a ∘ b) ∘ f ~⟨ ap (_∘ f) ab＝c ⟩
    c ∘ f ∎

  pullr : (f ∘ a) ∘ b ＝ f ∘ c
  pullr {f = f} =
    (f ∘ a) ∘ b =⟨ assoc b a f ⁻¹ ⟨
    f ∘ (a ∘ b) =⟨ ap (f ∘_) ab＝c ⟩
    f ∘ c ∎

  pull-inner : (f ∘ a) ∘ (b ∘ g) ＝ f ∘ c ∘ g
  pull-inner {f = f} = assoc _ _ _ ∙ ap (f ∘_) pulll

module _ (abc＝d : a ∘ b ∘ c ＝ d) where abstract
  pulll3 : a ∘ (b ∘ (c ∘ f)) ＝ d ∘ f
  pulll3 {f = f} =
    a ∘ b ∘ c ∘ f   =⟨ ap (a ∘_) (assoc _ _ _ ⁻¹) ⟩
    a ∘ (b ∘ c) ∘ f =⟨ assoc _ _ _ ⁻¹ ⟩
    (a ∘ b ∘ c) ∘ f =⟨ ap (_∘ f) abc＝d ⟩
    d ∘ f           ∎

  pullr3 : ((f ∘ a) ∘ b) ∘ c ＝ f ∘ d
  pullr3 {f = f} =
    ((f ∘ a) ∘ b) ∘ c =⟨ assoc _ _ _ ⁻¹ ⟨
    (f ∘ a) ∘ b ∘ c   =⟨ assoc _ _ _ ⁻¹ ⟨
    f ∘ a ∘ b ∘ c     =⟨ ap (f ∘_) abc＝d ⟩
    f ∘ d ∎

module _ (abcd＝e : a ∘ b ∘ c ∘ d ＝ e) where abstract
  pulll4 : a ∘ (b ∘ (c ∘ (d ∘ f))) ＝ e ∘ f
  pulll4 {f = f} =
    a ∘ b ∘ c ∘ d ∘ f =⟨ ap (λ x → a ∘ b ∘ x) (assoc _ _ _ ⁻¹) ⟩
    a ∘ b ∘ (c ∘ d) ∘ f =⟨ ap (a ∘_) (assoc _ _ _ ⁻¹) ⟩
    a ∘ (b ∘ c ∘ d) ∘ f =⟨ assoc _ _ _ ⁻¹ ⟩
    (a ∘ b ∘ c ∘ d) ∘ f =⟨ ap (_∘ f) abcd＝e ⟩
    e ∘ f ∎

module _ (c＝ab : c ＝ a ∘ b) where abstract
  pushl : c ∘ f ＝ a ∘ (b ∘ f)
  pushl = sym (pulll (sym c＝ab))

  pushr : f ∘ c ＝ (f ∘ a) ∘ b
  pushr = sym (pullr (sym c＝ab))

  push-inner : f ∘ c ∘ g ＝ (f ∘ a) ∘ (b ∘ g)
  push-inner {f = f} = ap (f ∘_) pushl ∙ assoc _ _ _ ⁻¹

module _ (d＝abc : d ＝ a ∘ b ∘ c) where abstract
  pushl3 : d ∘ f ＝ a ∘ (b ∘ (c ∘ f))
  pushl3 = sym (pulll3 (sym d＝abc))

  pushr3 : f ∘ d ＝ ((f ∘ a) ∘ b) ∘ c
  pushr3 = sym (pullr3 (sym d＝abc))

module _ (e＝abcd : e ＝ a ∘ b ∘ c ∘ d) where abstract
  pushl4 : e ∘ f ＝ a ∘ (b ∘ (c ∘ (d ∘ f)))
  pushl4 = sym (pulll4 (sym e＝abcd))

module _ (p : f ∘ h ＝ g ∘ i) where abstract
  extendl : f ∘ (h ∘ b) ＝ g ∘ (i ∘ b)
  extendl {b = b} =
    f ∘ (h ∘ b) =⟨ assoc b h f ⁻¹ ⟩
    (f ∘ h) ∘ b =⟨ ap (_∘ b) p ⟩
    (g ∘ i) ∘ b =⟨ assoc b i g ⁻¹ ⟨
    g ∘ (i ∘ b) ∎

  extendr : (a ∘ f) ∘ h ＝ (a ∘ g) ∘ i
  extendr {a = a} =
    (a ∘ f) ∘ h =⟨ assoc h f a ⁻¹ ⟨
    a ∘ (f ∘ h) =⟨ ap (a ∘_) p ⟩
    a ∘ (g ∘ i) =⟨ assoc i g a ⁻¹ ⟩
    (a ∘ g) ∘ i ∎

  extend-inner : a ∘ f ∘ h ∘ b ＝ a ∘ g ∘ i ∘ b
  extend-inner {a = a} = ap (a ∘_) extendl

module _ (p : a ∘ b ∘ c ＝ d ∘ f ∘ g) where abstract
  extendl3 : a ∘ (b ∘ (c ∘ h)) ＝ d ∘ (f ∘ (g ∘ h))
  extendl3 = pulll3 p ∙ sym (pulll3 refl)

  extendr3 : ((h ∘ a) ∘ b) ∘ c ＝ ((h ∘ d) ∘ f) ∘ g
  extendr3 = pullr3 p ∙ sym (pullr3 refl)

module _ (p : a ∘ b ∘ c ∘ d ＝ e ∘ f ∘ g ∘ h) where abstract
  extendl4 : a ∘ b ∘ c ∘ d ∘ i ＝ e ∘ f ∘ g ∘ h ∘ i
  extendl4 = pulll4 p ∙ sym (pulll4 refl)

abstract
  centralize
    : f ∘ g ＝ a ∘ b
    → h ∘ i ＝ c ∘ d
    → f ∘ g ∘ h ∘ i ＝ a ∘ (b ∘ c) ∘ d
  centralize {f = f} {g = g} {a = a} {b = b} {h = h} {i = i} {c = c} {d = d} p q =
    f ∘ g ∘ h ∘ i   =⟨ pulll p ⟩
    (a ∘ b) ∘ h ∘ i =⟨ pullr (pushr q) ⟩
    a ∘ (b ∘ c) ∘ d ∎

  centralizel
    : f ∘ g ＝ a ∘ b
    → f ∘ g ∘ h ∘ i ＝ a ∘ (b ∘ h) ∘ i
  centralizel p = centralize p refl

  centralizer
    : h ∘ i ＝ c ∘ d
    → f ∘ g ∘ h ∘ i ＝ f ∘ (g ∘ c) ∘ d
  centralizer p = centralize refl p

  disperse
    : f ∘ g ＝ a ∘ b
    → h ∘ i ＝ c ∘ d
    → f ∘ (g ∘ h) ∘ i ＝ a ∘ b ∘ c ∘ d
  disperse {f = f} {g = g} {a = a} {b = b} {h = h} {i = i} {c = c} {d = d} p q =
    f ∘ (g ∘ h) ∘ i =⟨ pushr (pullr q) ⟩
    (f ∘ g) ∘ c ∘ d =⟨ pushl p ⟩
    a ∘ b ∘ c ∘ d ∎

  dispersel
    : f ∘ g ＝ a ∘ b
    → f ∘ (g ∘ h) ∘ i ＝ a ∘ b ∘ h ∘ i
  dispersel p = disperse p refl

  disperser
    : h ∘ i ＝ c ∘ d
    → f ∘ (g ∘ h) ∘ i ＝ f ∘ g ∘ c ∘ d
  disperser p = disperse refl p

-- Cancellation

module _ (inv : h ∘ i ＝ id) where abstract
  cancell : h ∘ (i ∘ f) ＝ f
  cancell {f = f} =
    h ∘ (i ∘ f) =⟨ pulll inv ⟩
    id ∘ f      =⟨ ∙-id-i f ⟩
    f           ∎

  cancelr : (f ∘ h) ∘ i ＝ f
  cancelr {f = f} =
    (f ∘ h) ∘ i =⟨ pullr inv ⟩
    f ∘ id      =⟨ ∙-id-o f ⟩
    f           ∎

  insertl : f ＝ h ∘ (i ∘ f)
  insertl = sym cancell

  insertr : f ＝ (f ∘ h) ∘ i
  insertr = sym cancelr

  cancel-inner : (f ∘ h) ∘ (i ∘ g) ＝ f ∘ g
  cancel-inner = pulll cancelr

  insert-inner : f ∘ g ＝ (f ∘ h) ∘ (i ∘ g)
  insert-inner = pushl insertr

  deleter : (f ∘ g ∘ h) ∘ i ＝ f ∘ g
  deleter = pullr cancelr

  deletel : h ∘ (i ∘ f) ∘ g ＝ f ∘ g
  deletel = pulll cancell

module _ (inv : g ∘ h ∘ i ＝ id) where abstract
  cancell3 : g ∘ (h ∘ (i ∘ f)) ＝ f
  cancell3 {f = f} = pulll3 inv ∙ ∙-id-i f

  cancelr3 : ((f ∘ g) ∘ h) ∘ i ＝ f
  cancelr3 {f = f} = pullr3 inv ∙ ∙-id-o f

  insertl3 : f ＝ g ∘ (h ∘ (i ∘ f))
  insertl3 = sym cancell3

  insertr3 : f ＝ ((f ∘ g) ∘ h) ∘ i
  insertr3 = sym cancelr3

lswizzle : g ＝ h ∘ i → f ∘ h ＝ id → f ∘ g ＝ i
lswizzle {g = g} {h = h} {i = i} {f = f} p q =
  f ∘ g     =⟨ ap² _∘_ refl p ⟩
  f ∘ h ∘ i =⟨ cancell q ⟩
  i         ∎

rswizzle : g ＝ i ∘ h → h ∘ f ＝ id → g ∘ f ＝ i
rswizzle {g = g} {i = i} {h = h} {f = f} p q =
  g ∘ f       =⟨ ap² _∘_ p refl ⟩
  (i ∘ h) ∘ f =⟨ cancelr q ⟩
  i           ∎

swizzle : f ∘ g ＝ h ∘ i → g ∘ g' ＝ id → h' ∘ h ＝ id → h' ∘ f ＝ i ∘ g'
swizzle {f = f} {g = g} {h = h} {i = i} {g' = g'} {h' = h'} p q r =
  lswizzle (sym (assoc _ _ _ ⁻¹ ∙ rswizzle (sym p) q)) r

-- Sections and Retracts

module _
  {f : Hom x y}
  (f-section : has-section f)
  where abstract
  private module f = has-section f-section

  pre-section : a ∘ f ＝ b → a ＝ b ∘ f.section
  pre-section {a = a} {b = b} p = sym (rswizzle (sym p) f.is-section)

  post-section : f.section ∘ a ＝ b → a ＝ f ∘ b
  post-section {a = a} {b = b} p = sym (lswizzle (sym p) f.is-section)

module _
  {f : Hom x y}
  (f-retract : has-retraction f)
  where abstract
  private module f = has-retraction f-retract

  pre-retract : a ∘ f.retraction ＝ b → a ＝ b ∘ f
  pre-retract {a = a} {b = b} p = sym (rswizzle (sym p) f.is-retraction)

  post-retract : f ∘ a ＝ b → a ＝ f.retraction ∘ b
  post-retract {a = a} {b = b} p = sym (lswizzle (sym p) f.is-retraction)

{-
-- Isomorphisms

module _ {y z} (f : y ≅ z) where
  open _≅_

  abstract
    left-inv-unique
      : ∀ {g h}
      → g ∘ f .to ＝ id → h ∘ f .to ＝ id
      → g ＝ h
    left-inv-unique {g = g} {h = h} p q =
      g                   =⟨ intror (f .invl) ⟩
      g ∘ f .to ∘ f .from =⟨ extendl (p ∙ sym q) ⟩
      h ∘ f .to ∘ f .from =⟨ elimr (f .invl) ⟩
      h                   ∎

    left-right-inv-unique
      : ∀ {g h}
      → g ∘ f .to ＝ id → f .to ∘ h ＝ id
      → g ＝ h
    left-right-inv-unique {g = g} {h = h} p q =
      g                    =⟨ intror (f .invl) ⟩
      g ∘ f .to ∘ f .from  =⟨ cancell p ⟩
      f .from              =⟨ intror q ⟩
      f .from ∘ f .to ∘ h  =⟨ cancell (f .invr) ⟩
      h                    ∎

    right-inv-unique
      : ∀ {g h}
      → f .to ∘ g ＝ id → f .to ∘ h ＝ id
      → g ＝ h
    right-inv-unique {g = g} {h} p q =
      g                     =⟨ introl (f .invr) ⟩
      (f .from ∘ f .to) ∘ g =⟨ pullr (p ∙ sym q) ⟩
      f .from ∘ f .to ∘ h   =⟨ cancell (f .invr) ⟩
      h                     ∎

-- Lenses for isomorphisms

module _
  {x y z} {a : Hom x z} {f : Hom x y} {b : Hom y z}
  (f-inv : is-invertible f)
  where abstract

  private module f = is-invertible f-inv

  pre-invr : (a ∘ f.inv ＝ b) ≃ (a ＝ b ∘ f)
  pre-invr =
    (ap (_∘ f) , equiv→cancellable (invertible-precomp-equiv f-inv))
    ∙e ∙-pre-equiv (insertr f.invr)

  post-invr : (b ＝ a ∘ f.inv) ≃ (b ∘ f ＝ a)
  post-invr = sym-equiv ∙e pre-invr ∙e sym-equiv

  module pre-invr = Equiv pre-invr
  module post-invr = Equiv post-invr

module _
  {w x y} {a : Hom w y} {f : Hom x y} {b : Hom w x}
  (f-inv : is-invertible f)
  where abstract

  private module f = is-invertible f-inv

  pre-invl : (f.inv ∘ a ＝ b) ≃ (a ＝ f ∘ b)
  pre-invl =
    (ap (f ∘_) , equiv→cancellable (invertible-postcomp-equiv f-inv))
    ∙e ∙-pre-equiv (insertl f.invl)

  post-invl : (b ＝ f.inv ∘ a) ≃ (f ∘ b ＝ a)
  post-invl = sym-equiv ∙e pre-invl ∙e sym-equiv

  module pre-invl = Equiv pre-invl
  module post-invl = Equiv post-invl

Iso-swapr :
  ∀ {a : x ≅ y} {b : y ≅ z} {c : x ≅ z}
  → b ∘Iso a ＝ c
  → a ＝ b Iso⁻¹ ∘Iso c
Iso-swapr {a = a} {b = b} {c = c} p = ≅-path $
  a .to                     =⟨ introl (b .invr) ⟩
  (b .from ∘ b .to) ∘ a .to =⟨ pullr (ap to p) ⟩
  b .from ∘ c .to           ∎

Iso-swapl :
  ∀ {a : x ≅ y} {b : y ≅ z} {c : x ≅ z}
  → b ∘Iso a ＝ c
  → b ＝ c ∘Iso a Iso⁻¹
Iso-swapl {a = a} {b = b} {c = c} p = ≅-path $
  b .to                   =⟨ intror (a .invl) ⟩
  b .to ∘ a .to ∘ a .from =⟨ pulll (ap to p) ⟩
  c .to ∘ a .from         ∎

Iso-prism : ∀ {a : u ≅ v} {b : v ≅ w} {c : u ≅ w}
      → {d : u ≅ x} {e : v ≅ y} {f : w ≅ z}
      → {g : x ≅ y} {h : y ≅ z} {i : x ≅ z}
      → b ∘Iso a ＝ c
      → e ∘Iso a ＝ g ∘Iso d
      → f ∘Iso b ＝ h ∘Iso e
      → f ∘Iso c ＝ i ∘Iso d
      → h ∘Iso g ＝ i
Iso-prism {a = a} {b} {c} {d} {e} {f} {g} {h} {i} top left right front =
  ≅-path $
    h .to ∘ g .to                                           =⟨ ap₂ _∘_ (ap to (Iso-swapl (sym right))) (ap to (Iso-swapl (sym left)) ∙ sym (assoc _ _ _)) ⟩
    ((f .to ∘ b .to) ∘ e .from) ∘ (e .to ∘ a .to ∘ d .from) =⟨ cancel-inner (e .invr) ⟩
    (f .to ∘ b .to) ∘ (a .to ∘ d .from)                     =⟨ pull-inner (ap to top) ⟩
    f .to ∘ c .to ∘ d .from                                 =⟨ assoc _ _ _ ∙ sym (ap to (Iso-swapl (sym front))) ⟩
    i .to ∎

-- Notation

_⟩∘⟨_ : f ＝ h → g ＝ i → f ∘ g ＝ h ∘ i
_⟩∘⟨_ = ap₂ _∘_

infixr 20 _⟩∘⟨_

refl⟩∘⟨_ : g ＝ h → f ∘ g ＝ f ∘ h
refl⟩∘⟨_ {f = f} p = ap (f ∘_) p

_⟩∘⟨refl : f ＝ h → f ∘ g ＝ h ∘ g
_⟩∘⟨refl {g = g} p = ap (_∘ g) p

infix 21 refl⟩∘⟨_
infix 22 _⟩∘⟨refl

car : f ＝ g → f ∘ h ＝ g ∘ h
car p = ap₂ _∘_ p refl

cdr : f ＝ g → h ∘ f ＝ h ∘ g
cdr p = ap₂ _∘_ refl p

caar : f ＝ f' → (f ∘ g) ∘ h ＝ (f' ∘ g) ∘ h
cadr : g ＝ g' → f ∘ (g ∘ h) ＝ f ∘ (g' ∘ h)
cdar : g ＝ g' → (f ∘ g) ∘ h ＝ (f ∘ g') ∘ h
cddr : h ＝ h' → f ∘ (g ∘ h) ＝ f ∘ (g ∘ h')

caar p = car (car p)
cadr p = cdr (car p)
cdar p = car (cdr p)
cddr p = cdr (cdr p)

cdddr : i ＝ i' → f ∘ (g ∘ (h ∘ i)) ＝ f ∘ (g ∘ (h ∘ i'))

cdddr p = cddr (cdr p)

cddddr : k ＝ k' → f ∘ (g ∘ (h ∘ (i ∘ k))) ＝ f ∘ (g ∘ (h ∘ (i ∘ k')))

cddddr p = cdddr (cdr p)
-}
