{-# OPTIONS --safe #-}
module Data.List.Correspondences.Unary.Dup where

open import Prelude
open import Data.Nat
open import Data.List
open import Data.List.Correspondences.Unary.Any

private variable
  ℓ ℓ′ : Level
  A : 𝒰 ℓ
  B : 𝒰 ℓ′
  x y : A
  xs ys : List A

data Dup {ℓ} {A : 𝒰 ℓ} : List A → 𝒰 ℓ where
  hereᵈ : x ∈ xs → Dup (x ∷ xs)
  thereᵈ : Dup xs → Dup (x ∷ xs)

-- TODO hlevel

dup→ℕ : Dup xs → ℕ
dup→ℕ (hereᵈ _)  = 0
dup→ℕ (thereᵈ d) = suc (dup→ℕ d)

dup-map : {f : A → B}
        → Dup xs → Dup (mapₗ f xs)
dup-map {f} (hereᵈ x∈) = hereᵈ (∈-map f x∈)
dup-map     (thereᵈ d) = thereᵈ (dup-map d)

dup-++-l : Dup xs → Dup (xs ++ ys)
dup-++-l (hereᵈ x∈) = hereᵈ (any-++-l x∈)
dup-++-l (thereᵈ d) = thereᵈ (dup-++-l d)

dup-++-r : Dup ys → Dup (xs ++ ys)
dup-++-r {xs = []}     d = d
dup-++-r {xs = x ∷ xs} d = thereᵈ (dup-++-r d)

dup-both : {z : A} {xs ys : List A}
         → z ∈ xs → z ∈ ys → Dup (xs ++ ys)
dup-both {xs = x ∷ xs} {ys} (here e)    zys = hereᵈ (any-++-r (subst (_∈ ys) e zys))
dup-both {xs = x ∷ xs}      (there zxs) zys = thereᵈ (dup-both zxs zys)

dup-overlap : {xs ys : List A}
            → xs ≬ ys → Dup (xs ++ ys)
dup-overlap (z , z∈xs , z∈ys) = dup-both z∈xs z∈ys

dup-reverse : Dup xs → Dup (reverse xs)
dup-reverse {xs = x ∷ xs} (hereᵈ x∈) = dup-both (any-reverse x∈) (here refl)
dup-reverse {xs = x ∷ xs} (thereᵈ d) = dup-++-l (dup-reverse d)
