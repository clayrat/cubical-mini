{-# OPTIONS --safe #-}
module Data.Maybe.Instances.Traversable where

open import Foundations.Base

open import Meta.Effect.Traversable

open import Data.Maybe.Base

instance
  Traversable-Maybe : Traversable (eff Maybe)
  Traversable-Maybe .traverse f (just x) = just <$> f x
  Traversable-Maybe .traverse _ nothing  = pure nothing
