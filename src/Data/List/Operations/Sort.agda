{-# OPTIONS --safe #-}
module Data.List.Operations.Sort where

open import Meta.Prelude
open import Foundations.Base

open import Data.Empty as Empty
open import Data.Bool.Base as Bool
open import Data.Bool.Path
open import Data.Sum.Base as Sum

open import Data.Reflects.Base

open import Data.List.Base as List
open import Data.List.Operations
open import Data.List.Correspondences.Unary.All
open import Data.List.Correspondences.Unary.Any
open import Data.List.Membership
open import Data.List.Correspondences.Unary.At
open import Data.List.Correspondences.Unary.Related
open import Data.List.Correspondences.Unary.Unique
open import Data.List.Correspondences.Binary.Perm

private variable
  ℓ ℓ′ : Level
  A : 𝒰 ℓ
  cmp : A → A → Bool
  _≤_ _<_ : A → A → 𝒰 ℓ′
  x y z w : A
  xs : List A

insert-perm : Perm (insert cmp x xs) (x ∷ xs)
insert-perm           {xs = []}     = perm-refl
insert-perm {cmp} {x} {xs = y ∷ xs} with cmp x y
... | false = ptrans (pprep refl insert-perm) (pswap refl refl perm-refl)
... | true  = perm-refl

insertion-sort-perm : Perm (insertion-sort cmp xs) xs
insertion-sort-perm {xs = []}     = perm-refl
insertion-sort-perm {xs = x ∷ xs} = ptrans insert-perm (pprep refl insertion-sort-perm)

insert-sorted : {R : ∀ x y → Reflects (x ≤ y) (cmp x y)}
              → Trans _≤_ → (∀ x y → ¬ x ≤ y → y ≤ x)
              → ∀ {xs} → Sorted _≤_ xs → Sorted _≤_ (insert cmp x xs)
insert-sorted               _  _   {xs = []}     []ˢ    = ∷ˢ []ʳ
insert-sorted {cmp} {x} {R} tr tot {xs = y ∷ xs} (∷ˢ r) with cmp x y | recall (cmp x) y
... | false | ⟪ eq ⟫ = ∷ˢ (sorted-at0→related
                              (insert-sorted {R = R} tr tot (related→sorted r))
                              (all→atweak (perm-all (perm-sym insert-perm)
                                                    (tot x y (so→false! ⦃ R x y ⦄ $ not-so $ ¬so≃is-false ⁻¹ $ eq)
                                                              ∷ (related→all ⦃ tr ⦄ r)))
                                          0))
... | true  | ⟪ eq ⟫ = ∷ˢ ((so→true! ⦃ R x y ⦄ $ so≃is-true ⁻¹ $ eq) ∷ʳ r)

insertion-sort-sorted : {R : ∀ x y → Reflects (x ≤ y) (cmp x y)}
                      → Trans _≤_ → (∀ x y → ¬ x ≤ y → y ≤ x)
                      → ∀ {xs} → Sorted _≤_ (insertion-sort cmp xs)
insertion-sort-sorted _  _   {xs = []}     = []ˢ
insertion-sort-sorted {R} tr tot {xs = x ∷ xs} =
  insert-sorted {R = R} tr tot
    (insertion-sort-sorted {R = R} tr tot {xs})

-- sorting with strict comparison

insert-sorted-uniq-strict : {R : ∀ x y → Reflects (x < y) (cmp x y)}
                          → Trans _<_ → (∀ x y → ¬ x < y → (y < x) ⊎ (x ＝ y))
                          → ∀ {xs} → x ∉ xs → Uniq xs
                          → Sorted _<_ xs → Sorted _<_ (insert cmp x xs)
insert-sorted-uniq-strict               _  _    {xs = []}     _   _         []ˢ   = ∷ˢ []ʳ
insert-sorted-uniq-strict {cmp} {x} {R} tr stot {xs = y ∷ xs} nx (ny ∷ᵘ u) (∷ˢ r) with cmp x y | recall (cmp x) y
... | false | ⟪ eq ⟫ =
  let (ne , nxs) = ¬Any-uncons nx in
  ∷ˢ (sorted-at0→related
        (insert-sorted-uniq-strict {R = R} tr stot nxs u (related→sorted r))
        (all→atweak (perm-all (perm-sym insert-perm)
                              ([ id , (λ e → absurd (ne e)) ]ᵤ (stot x y (so→false! ⦃ R x y ⦄ $ not-so $ ¬so≃is-false ⁻¹ $ eq)) ∷ (related→all ⦃ tr ⦄ r)))
                    0))
... | true  | ⟪ eq ⟫ = ∷ˢ ((so→true! ⦃ R x y ⦄ $ so≃is-true ⁻¹ $ eq) ∷ʳ r)

insertion-sort-sorted-uniq-strict : {R : ∀ x y → Reflects (x < y) (cmp x y)}
                                  → Trans _<_ → (∀ x y → ¬ x < y → (y < x) ⊎ (x ＝ y))
                                  → ∀ {xs} → Uniq xs
                                  → Sorted _<_ (insertion-sort cmp xs)
insertion-sort-sorted-uniq-strict           _  _    {xs = []}     []ᵘ       = []ˢ
insertion-sort-sorted-uniq-strict {cmp} {R} tr stot {xs = x ∷ xs} (nx ∷ᵘ u) =
  let p = insertion-sort-perm {xs = xs} in
  insert-sorted-uniq-strict {R = R} tr stot
    (contra (≈↔→≈ {S = insertion-sort cmp xs} {T = xs} (perm→bag-equiv p) .fst) nx)
    (perm-unique (perm-sym p) u)
    (insertion-sort-sorted-uniq-strict {R = R} tr stot u)
