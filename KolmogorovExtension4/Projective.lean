/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
import KolmogorovExtension4.Boxes
import Mathlib.MeasureTheory.Constructions.Projective

open Set

namespace MeasureTheory

variable {ι : Type*} {α : ι → Type*}

/-- A family of objects indexed by a preoder `ι` with projections `π i j` when `j ≤ i` is
*projective* if it is invariant under the projections. -/
def IsProjective [Preorder ι] (P : ∀ j : ι, α j) (π : ∀ {i j : ι}, j ≤ i → α i → α j) : Prop :=
  ∀ (i j) (hji : j ≤ i), P j = π hji (P i)

variable [∀ i, MeasurableSpace (α i)] {P : ∀ J : Finset ι, Measure (∀ j : J, α j)}

theorem IsProjectiveMeasureFamily.empty_of_subset (hP : IsProjectiveMeasureFamily P) (i : ι)
    [hi : IsEmpty (α i)] {I J : Finset ι} (hIJ : I ⊆ J) (i_mem : i ∈ J) : P I = 0 := by
  ext S mS
  rw [hP J I hIJ]
  simp only
  rw [Measure.map_apply (measurable_proj₂' J I hIJ) mS]
  have : IsEmpty ((j : J) → α j) := by
    rw [← not_nonempty_iff, Classical.nonempty_pi]
    push_neg
    simp_rw [not_nonempty_iff]
    exact ⟨⟨i, i_mem⟩, hi⟩
  have : P J = 0 := (P J).eq_zero_of_isEmpty
  simp [this]

theorem IsProjectiveMeasureFamily.empty (hP : IsProjectiveMeasureFamily P)
    (h : ¬(∀ i, Nonempty (α i))) (I : Finset ι) : P I = 0 := by
  classical
  simp only [not_forall, not_nonempty_iff] at h
  rcases h with ⟨i, hi⟩
  exact hP.empty_of_subset i (I.subset_insert i) (I.mem_insert_self i)

end MeasureTheory
