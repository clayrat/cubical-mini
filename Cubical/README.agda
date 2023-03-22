{-# OPTIONS --guardedness #-}

module Cubical.README where

------------------------------------------------------------------------
-- A programmer's library for Cubical Agda
-----------------------------------------------------------------------

-- The library comes with a .agda-lib file, for use with the library
-- management system.

------------------------------------------------------------------------
-- Module hierarchy
------------------------------------------------------------------------

-- The core library for Cubical Agda.
-- It contains basic primitives, equivalences, glue types.
import Cubical.Core.Everything

-- The foundations for Cubical Agda.
-- The Prelude module is self-explanatory.
import Cubical.Foundations.Prelude
import Cubical.Foundations.Everything

-- Kinds and properties of functions
import Cubical.Functions.Everything

-- Data structures and their properties
import Cubical.Data.Everything

-- Higher-inductive types
import Cubical.HITs.Everything

-- Properties and proofs about relations
import Cubical.Relation.Everything

-- Category theory
import Cubical.Categories.Everything

-- Homotopy theory
import Cubical.Homotopy.Everything

-- Other modules (TODO: add descriptions)
import Cubical.Induction.Everything

-- Standard structures a la Escardo?
import Cubical.Structures.Everything

-- Algebra library
import Cubical.Algebra.Everything

-- Reflection
import Cubical.Reflection.Everything

-- Displayed univalent graphs
import Cubical.Displayed.Everything

-- Homotopy level truncations
import Cubical.Truncation.Everything

-- Quotients
import Cubical.Quotient.Everything

-- Automatic proving, solvers
import Cubical.Tactics.Everything

-- Interfaces for everyday programming
import Cubical.Interface.Everything

-- I/O
import Cubical.IO
