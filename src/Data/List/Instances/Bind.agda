{-# OPTIONS --safe #-}
module Data.List.Instances.Bind where

open import Foundations.Base

open import Meta.Effect.Base
open import Meta.Effect.Bind

open import Data.List.Base
open import Data.List.Instances.Idiom public

instance
  Bind-List : Bind (eff List)
  Bind-List ._>>=_ = go where
    go : _
    go []       _ = []
    go (x ∷ xs) f = f x ++ go xs f
