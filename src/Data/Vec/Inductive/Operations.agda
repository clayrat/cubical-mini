{-# OPTIONS --safe #-}
module Data.Vec.Inductive.Operations where

open import Foundations.Base

open import Data.Bool
open import Data.Fin.Inductive.Base
open import Data.List.Base
open import Data.List.Operations
  hiding (all ; lookup ; unzip)

open import Data.Vec.Inductive.Base public

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′
  @0 n : ℕ

tabulate : {n : ℕ} → (Fin n → A) → Vec A n
tabulate {n = 0}     _ = []
tabulate {n = suc n} f = f fzero ∷ tabulate (f ∘ fsuc)

lookup : Vec A n → Fin n → A
lookup (x ∷ _)  fzero    = x
lookup (_ ∷ xs) (fsuc k) = lookup xs k

replace : Fin n → A → Vec A n → Vec A n
replace fzero y (_ ∷ xs) = y ∷ xs
replace (fsuc idx) y (x ∷ xs) = x ∷ replace idx y xs

vec→list : {A : Type ℓ} → Vec A n → Σ[ xs ꞉ List A ] Erased (length xs ＝ n)
vec→list [] = [] , erase refl
vec→list (x ∷ xs) =
  let xs′ , erase p = vec→list xs
  in x ∷ xs′ , erase (ap suc p)

list→vec : (xs : List A) → Σ[ len ꞉ ℕ ] Vec A len × (length xs ＝ len)
list→vec [] = 0 , [] , refl
list→vec (x ∷ xs) =
  let len′ , xs′ , p = list→vec xs
  in suc len′ , x ∷ xs′ , ap suc p

unzip : Vec (A × B) n → Vec A n × Vec B n
unzip []       = [] , []
unzip ((x , y) ∷ xys) =
  let (ihx , ihy) = unzip xys in
  x ∷ ihx , y ∷ ihy

all : (A → Bool) → Vec A n → Bool
all p []       = true
all p (x ∷ xs) = p x and all p xs

