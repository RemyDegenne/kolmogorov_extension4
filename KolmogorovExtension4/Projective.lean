/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
import Mathlib.MeasureTheory.Constructions.Projective

open Set

namespace MeasureTheory

variable {ι : Type*} {α : ι → Type*} [∀ i, MeasurableSpace (α i)]

-- unused
-- /-- A family of objects indexed by a preoder `ι` with projections `π i j` when `j ≤ i` is
-- *projective* if it is invariant under the projections. -/
-- def IsProjective [Preorder ι] (P : ∀ j : ι, α j) (π : ∀ {i j : ι}, j ≤ i → α i → α j) : Prop :=
--   ∀ (i j) (hji : j ≤ i), P j = π hji (P i)

theorem IsProjectiveMeasureFamily.empty
    {P : ∀ J : Finset ι, Measure (Π j : J, α j)} (hP : IsProjectiveMeasureFamily P)
    (h : ∃ i, IsEmpty (α i)) (I : Finset ι) : P I = 0 := by
  classical
  rcases h with ⟨i, hi⟩
  rw [hP (insert i I) I (I.subset_insert i)]
  have : IsEmpty ((j : ↑(insert i I)) → α j) := by
    rw [← not_nonempty_iff, Classical.nonempty_pi]
    push_neg
    simp_rw [not_nonempty_iff]
    exact ⟨⟨i, I.mem_insert_self i⟩, hi⟩
  rw [(P (insert i I)).eq_zero_of_isEmpty]
  simp

end MeasureTheory
