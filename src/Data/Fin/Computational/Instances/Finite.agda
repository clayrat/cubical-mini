{-# OPTIONS --safe #-}
module Data.Fin.Computational.Instances.Finite where

open import Meta.Prelude

open import Combinatorics.Finiteness.ManifestBishop

open import Data.Fin.Computational.Base

private variable n : ℕ

instance
  fin-manifest-bishop-finite : Manifest-bishop-finite (Fin n)
  fin-manifest-bishop-finite = fin refl
  {-# OVERLAPPING fin-manifest-bishop-finite #-}
