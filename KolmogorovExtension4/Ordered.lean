/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Lattice

/-!
# Ordered

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`


-/


open Set

namespace Finset

variable {α β : Type*}

lemma mem_map_univ_asEmbedding {α β : Type*} [Fintype α] {p : β → Prop}
    (e : α ≃ Subtype p) {b : β} :
    b ∈ Finset.map e.asEmbedding univ ↔ p b := by
  rw [mem_map]
  simp only [Finset.mem_univ, Equiv.asEmbedding_apply, Function.comp_apply, exists_true_left,
    true_and]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨a, rfl⟩ := h
    exact (e a).prop
  · obtain ⟨a, ha⟩ := e.surjective ⟨b, h⟩
    refine ⟨a, ?_⟩
    rw [ha]

/-- An ordering of the elements of a finset. -/
noncomputable def ordered (J : Finset α) : Fin J.card ↪ α :=
  J.equivFin.symm.asEmbedding

lemma ordered_mem {J : Finset α} (n : Fin J.card) : J.ordered n ∈ J := by
  simp_rw [Finset.ordered]; exact coe_mem _

lemma map_ordered (J : Finset α) : Finset.map J.ordered (univ : Finset (Fin J.card)) = J := by
  ext; simp_rw [Finset.ordered, Finset.mem_map_univ_asEmbedding]

lemma sum_ordered [AddCommMonoid β] (J : Finset α) (m : α → β) :
    ∑ i : Fin J.card, m (J.ordered i) = ∑ u in J, m u := by
  conv_rhs => rw [← map_ordered J]
  rw [sum_map]

section FinsetSet

variable {C : Set (Set α)} {J : Finset (Set α)}

lemma iUnion_ordered (J : Finset (Set α)) : (⋃ i, J.ordered i) = ⋃₀ J := by
  conv_rhs => rw [← map_ordered J]
  simp_rw [sUnion_eq_biUnion, coe_map, Set.biUnion_image]
  simp only [mem_coe, Finset.mem_univ, iUnion_true]

end FinsetSet

end Finset
