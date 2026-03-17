{-# OPTIONS --safe #-}
module Data.List.Correspondences.Unary.Unique where

open import Prelude
open import Data.Empty
open import Data.Reflects
open import Data.Nat.Path
open import Data.Nat.Properties
open import Data.Nat.Order.Base
open import Data.Sum.Base
open import Data.List
open import Data.List.Correspondences.Unary.All
open import Data.List.Correspondences.Unary.Any
open import Data.List.Correspondences.Unary.Related
open import Data.List.Correspondences.Unary.Pairwise
open import Data.List.Correspondences.Binary.OPE
open import Data.List.Membership
open import Data.List.Operations
open import Data.List.Operations.Properties

private variable
  ℓ : Level
  A : 𝒰 ℓ
  x y : A
  xs : List A

data Uniq {ℓ} {A : 𝒰 ℓ} : List A → 𝒰 ℓ where
  []ᵘ : Uniq []
  _∷ᵘ_ : x ∉ xs → Uniq xs → Uniq (x ∷ xs)

Uniq-is-prop : is-prop (Uniq xs)
Uniq-is-prop  []ᵘ         []ᵘ        = refl
Uniq-is-prop (nx1 ∷ᵘ u1) (nx2 ∷ᵘ u2) = ap² _∷ᵘ_ prop! (Uniq-is-prop u1 u2)

uniq-uncons : {x : A} {xs : List A}
            → Uniq (x ∷ xs) → x ∉ xs × Uniq xs
uniq-uncons (x∉ ∷ᵘ u) = x∉ , u

uniq→++ : {xs ys : List A}
        → Uniq xs → Uniq ys → xs ∥ ys
        → Uniq (xs ++ ys)
uniq→++ {xs = []}            ux  uy dxy = uy
uniq→++ {xs = x ∷ xs} (nx ∷ᵘ ux) uy dxy =
     (contra ([ id , (λ hxy → absurd (dxy (here refl) hxy)) ]ᵤ ∘ any-split {xs = xs}) nx)
  ∷ᵘ uniq→++ ux uy (dxy ∘ there)

++→uniq : {xs ys : List A}
        → Uniq (xs ++ ys)
        → Uniq xs × Uniq ys × xs ∥ ys
++→uniq {xs = []}                 u  = []ᵘ , u , λ hx _ → false! hx
++→uniq {xs = x ∷ xs} {ys} (nx ∷ᵘ u) =
  let (ux , uy , dxy) = ++→uniq {xs = xs} u in
    (contra any-++-l nx) ∷ᵘ ux
  , uy
  , ∥-∷→l (contra any-++-r nx) dxy

uniq-snoc : {xs : List A} {x : A}
          → Uniq xs → x ∉ xs → Uniq (xs ∷r x)
uniq-snoc {xs} u x∉ =
  subst Uniq (snoc-append xs ⁻¹) $
  uniq→++ u (false! ∷ᵘ []ᵘ)
    λ x∈ → λ where (here e) → x∉ (subst (_∈ xs) e x∈)

uniq-concat : {xss : List (List A)}
            → Uniq (concat xss)
            → All Uniq xss × Pairwise _∥_ xss
uniq-concat {xss = []}       _   = [] , []ᵖ
uniq-concat {xss = xs ∷ xss} uss =
  let (ux , uss' , dx) = ++→uniq {xs = xs} uss
      (axs , pxs) = uniq-concat {xss = xss} uss'
    in
  ux ∷ axs , ∥-concat dx ∷ᵖ pxs

concat-uniq : {xss : List (List A)}
            → All Uniq xss → Pairwise _∥_ xss
            → Uniq (concat xss)
concat-uniq {xss = []}       _          _          = []ᵘ
concat-uniq {xss = xs ∷ xss} (u ∷ axs) (ax ∷ᵖ pxs) =
  uniq→++ u (concat-uniq axs pxs) (concat-∥ ax)

-- homotopy uniqueness

Uniq-set→is-unique : {xs : List A}
                   → is-set A → Uniq xs → is-unique xs
Uniq-set→is-unique {xs = x ∷ xs} sa (nx ∷ᵘ u) z (here e1)   (here e2)   = ap here (sa z x e1 e2)
Uniq-set→is-unique {xs = x ∷ xs} sa (nx ∷ᵘ u) z (here e1)   (there hz2) = absurd (nx (subst (_∈ₗ xs) e1 hz2))
Uniq-set→is-unique {xs = x ∷ xs} sa (nx ∷ᵘ u) z (there hz1) (here e2)   = absurd (nx (subst (_∈ₗ xs) e2 hz1))
Uniq-set→is-unique {xs = x ∷ xs} sa (nx ∷ᵘ u) z (there hz1) (there hz2) = ap there (Uniq-set→is-unique sa u z hz1 hz2)

is-unique→Uniq : is-unique xs → Uniq xs
is-unique→Uniq {xs = []}     _ = []ᵘ
is-unique→Uniq {xs = x ∷ xs} u =
  (λ hx → false! (u x (here refl) (there hx)))
  ∷ᵘ is-unique→Uniq λ y h1 h2 → there-inj (u y (there h1) (there h2))

-- relatedness/sortedness with irreflexive relation implies uniqueness

related→uniq : {ℓ′ : Level} {x : A} {xs : List A} {R : A → A → 𝒰 ℓ′} → ⦃ Trans R ⦄
             → (∀ {x} → ¬ R x x)
             → Related R x xs → Uniq (x ∷ xs)
related→uniq     {xs = []}         _    _           = false! ∷ᵘ []ᵘ
related→uniq {x} {xs = y ∷ xs} {R} irr (rxy ∷ʳ rel) =
  ¬any-∷ (contra (λ e → subst (R x) (e ⁻¹) rxy) irr)
         (λ hx → irr (rxy ∙ All→∀∈ (related→all rel) x hx))
  ∷ᵘ related→uniq irr rel

sorted→uniq : {ℓ′ : Level} {xs : List A} {R : A → A → 𝒰 ℓ′} → ⦃ Trans R ⦄
            → (∀ {x} → ¬ R x x)
            → Sorted R xs → Uniq xs
sorted→uniq {xs = []}     irr []ˢ      = []ᵘ
sorted→uniq {xs = x ∷ xs} irr (∷ˢ rel) = related→uniq irr rel

-- OPE, subset & set-equivalence

uniq-ope : {xs ys : List A}
         → OPE xs ys → Uniq ys → Uniq xs
uniq-ope  odone              []ᵘ       = []ᵘ
uniq-ope (otake {ys} e ope) (ny ∷ᵘ uy) =
  contra (subst (_∈ ys) e ∘ ope→subset ope) ny ∷ᵘ uniq-ope ope uy
uniq-ope (odrop ope)        (_ ∷ᵘ uy)  = uniq-ope ope uy

uniq⊆→len≤ : {xs ys : List A}
           → Uniq xs → xs ⊆ ys → length xs ≤ length ys
uniq⊆→len≤ {xs = []}           u        sub = z≤
uniq⊆→len≤ {xs = x ∷ xs} {ys} (nx ∷ᵘ u) sub =
  let hysaxs = all-uncons $ ∀∈→All λ z → sub {z}
      (ls , rs , e) = ∈-split (hysaxs .fst)
      sub′ = All→∀∈ (subst (λ q → All (_∈ q) xs) e (hysaxs .snd))
   in
  subst (λ q → suc (length xs) ≤ length q) (e ⁻¹) $
  subst (suc (length xs) ≤_) (+-suc-r (length ls) (length rs) ⁻¹ ∙ ++-length ls (x ∷ rs) ⁻¹) $
  s≤s $
  subst (length xs ≤_) (++-length ls rs) $
  uniq⊆→len≤ u λ {x = z} hz →
  any-split {xs = ls} (sub′ z hz) &
  [ any-++-l
  , [ (λ ez → absurd (nx (subst (_∈ xs) ez hz)))
    , any-++-r
    ]ᵤ ∘ any-uncons ]ᵤ

uniq⊆len≤→uniq : {xs ys : List A}
                → Uniq xs → xs ⊆ ys → length ys ≤ length xs
                → Uniq ys
uniq⊆len≤→uniq {xs = []}     u         sub le =
  let eys = length=0→nil $ ≤0→=0 le in
  subst Uniq (eys ⁻¹) []ᵘ
uniq⊆len≤→uniq {xs = x ∷ xs} (nx ∷ᵘ u) sub le =
  let hysaxs = all-uncons $ ∀∈→All λ z → sub {z}
      (ls , rs , e) = ∈-split (hysaxs .fst)
      sub′ = All→∀∈ (subst (λ q → All (_∈ q) xs) e (hysaxs .snd))
      sub″ : xs ⊆ (ls ++ rs)
      sub″ = λ {x = z} hz →
               [ any-++-l
               , [ (λ ez → absurd (nx (subst (_∈ xs) ez hz)))
                  , any-++-r
                  ]ᵤ ∘ any-uncons ]ᵤ (any-split {xs = ls} (sub′ z hz))
      le′ = subst (_≤ length xs) ((++-length ls rs) ⁻¹)  $
            ≤-peel $
            subst (_≤ suc (length xs)) (++-length ls (x ∷ rs) ∙ +-suc-r (length ls) (length rs)) $
            subst (λ q → length q ≤ suc (length xs)) e le
      ulurar : Uniq ls × Uniq rs × ls ∥ rs
      ulurar = ++→uniq {xs = ls} $
               uniq⊆len≤→uniq {xs = xs} {ys = ls ++ rs} u sub″ le′
      nlr : x ∉ (ls ++ rs)
      nlr = contra (λ hlr → <≃suc≤ $
                            uniq⊆→len≤ (nx ∷ᵘ u) λ {x = z} →
                            All→∀∈ {P = _∈ (ls ++ rs)} (hlr ∷ ∀∈→All λ q → sub″) z)
                   (≤→≯ le′)
   in
  subst Uniq (e ⁻¹) $
  uniq→++
    (ulurar .fst)
    (contra any-++-r nlr ∷ᵘ (ulurar .snd .fst))
    (∥-∷→r (contra any-++-l nlr) (ulurar .snd .snd))

uniq≈→len= : {xs ys : List A}
           → Uniq xs → Uniq ys
           → xs ≈ ys
           → length xs ＝ length ys
uniq≈→len= ux uy seq =
  ≤-antisym (uniq⊆→len≤ ux (seq .fst)) (uniq⊆→len≤ uy (seq .snd))

uniq≈len=→uniq : {xs ys : List A}
               → length xs ＝ length ys
               → xs ≈ ys
               → Uniq xs → Uniq ys
uniq≈len=→uniq es seq ux =
  uniq⊆len≤→uniq ux (seq .fst) (=→≤ (es ⁻¹))

-- reverse

uniq-reverse : {xs : List A}
             → Uniq xs → Uniq (reverse xs)
uniq-reverse = uniq≈len=→uniq (reverse-length ⁻¹) reverse-≈

-- map

map-uniq : {B : 𝒰 ℓ} {f : A → B} {xs : List A}
         → Uniq (mapₗ f xs) → Uniq xs
map-uniq     {xs = []}     _           = []ᵘ
map-uniq {f} {xs = x ∷ xs} (fx∉ ∷ᵘ um) =
  contra (∈-map f) fx∉ ∷ᵘ map-uniq um

uniq-map : {B : 𝒰 ℓ} {f : A → B} {xs : List A}
         → Injective f
         → Uniq xs → Uniq (mapₗ f xs)
uniq-map     {xs = []}     inj  _         = []ᵘ
uniq-map {f} {xs = x ∷ xs} inj (x∉ ∷ᵘ u) =
  contra (map-∈ f inj) x∉ ∷ᵘ uniq-map inj u

-- stronger local form
uniq-map-∈ : {B : 𝒰 ℓ} {f : A → B} {xs : List A}
         → (∀ {x y} → x ∈ xs → y ∈ xs → f x ＝ f y → x ＝ y)
         → Uniq xs → Uniq (mapₗ f xs)
uniq-map-∈     {xs = []}     inj  _         = []ᵘ
uniq-map-∈ {f} {xs = x ∷ xs} inj (x∉ ∷ᵘ u) =
     contra
       (λ fx∈ →
         let (q , q∈ , qe) = map-∈Σ f fx∈ in
         subst (_∈ xs) (inj (here refl) (there q∈) qe ⁻¹) q∈)
       x∉
  ∷ᵘ uniq-map-∈ (λ {x} {y} x∈ y∈ e → inj (there x∈) (there y∈) e) u

-- count-from-to

count-from-to-uniq : {m n : ℕ}
                   → Uniq (count-from-to m n)
count-from-to-uniq {m = m}    {n = zero}  = []ᵘ
count-from-to-uniq {m = zero} {n = suc n} =
    (λ mx → let (n , _ , ne) = map-∈Σ suc mx in false! ne)
  ∷ᵘ uniq-map suc-inj (count-from-to-uniq {m = 0} {n = n})
count-from-to-uniq {m = suc m} {n = suc n} =
  uniq-map suc-inj (count-from-to-uniq {m = m} {n = n})
