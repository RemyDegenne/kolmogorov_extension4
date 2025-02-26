/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

/-!

THIS FILE IS NOT USED FOR THE MAIN RESULT

-/

open Finset Set Filter

open scoped ENNReal NNReal Topology

section Accumulate

variable {α : Type*}

theorem MeasurableSet.accumulate {_ : MeasurableSpace α} {s : ℕ → Set α}
    (hs : ∀ n, MeasurableSet (s n)) (n : ℕ) : MeasurableSet (Set.Accumulate s n) :=
  MeasurableSet.biUnion (Set.to_countable _) fun n _ ↦ hs n

end Accumulate
