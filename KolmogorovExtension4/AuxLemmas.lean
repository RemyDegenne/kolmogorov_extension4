/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

open Finset Set Filter

open scoped ENNReal NNReal Topology

lemma Finset.sum_image_le_of_nonneg {ι α β : Type*} [DecidableEq α]
    [OrderedAddCommMonoid β] [SMulPosMono ℕ β]
    {J : Finset ι} {g : ι → α} {f : α → β} (hf : ∀ u ∈ J.image g, 0 ≤ f u) :
    ∑ u in J.image g, f u ≤ ∑ u in J, f (g u) := by
  rw [sum_comp f g]
  refine sum_le_sum fun a hag ↦ ?_
  obtain ⟨i, hi, hig⟩ := Finset.mem_image.mp hag
  conv_lhs => rw [← one_nsmul (f a)]
  refine smul_le_smul_of_nonneg_right ?_ (hf a hag)
  rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, card_pos]
  exact ⟨i, mem_filter.mpr ⟨hi, hig⟩⟩

section Accumulate

variable {α : Type*}

theorem MeasurableSet.accumulate {_ : MeasurableSpace α} {s : ℕ → Set α}
    (hs : ∀ n, MeasurableSet (s n)) (n : ℕ) : MeasurableSet (Set.Accumulate s n) :=
  MeasurableSet.biUnion (Set.to_countable _) fun n _ ↦ hs n

end Accumulate
