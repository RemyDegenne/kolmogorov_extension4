/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.MeasureTheory.PiSystem
import Mathlib.MeasureTheory.OuterMeasure.Basic
import KolmogorovExtension4.AuxLemmas
import Mathlib.Data.Set.Pairwise.Lattice
import Mathlib.MeasureTheory.SetSemiRing

/-! # Semirings of sets

A semi-ring of sets `C` is a family of sets containing `∅`, stable by intersection and such that
for all `s, t ∈ C`, `t \ s` is equal to a disjoint union of finitely many sets in `C`.

-/


open Finset Set MeasureTheory Order

open scoped NNReal Topology ENNReal

namespace MeasureTheory

variable {α : Type*} {C : Set (Set α)} {s t : Set α}

section Ordered

theorem Finset.mem_map_univ_asEmbedding {α β : Type*} [Fintype α] {p : β → Prop}
    (e : α ≃ Subtype p) {b : β} : b ∈ Finset.map e.asEmbedding univ ↔ p b := by
  rw [mem_map]
  simp only [Finset.mem_univ, Equiv.asEmbedding_apply, Function.comp_apply, exists_true_left,
    true_and]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨a, rfl⟩ := h
    exact (e a).prop
  · suffices ∃ a, e a = ⟨b, h⟩ by
      obtain ⟨a, ha⟩ := this
      refine ⟨a, ?_⟩
      rw [ha]
    exact e.surjective _

variable {J : Finset (Set α)}

/-- An ordering of the elements of a finset. -/
noncomputable def _root_.Finset.ordered (J : Finset α) : Fin J.card ↪ α :=
  J.equivFin.symm.asEmbedding

theorem map_ordered (J : Finset (Set α)) :
    Finset.map J.ordered (univ : Finset (Fin J.card)) = J := by
  ext1 s; simp_rw [Finset.ordered, Finset.mem_map_univ_asEmbedding]

theorem ordered_mem (n : Fin J.card) : J.ordered n ∈ J := by
  simp_rw [Finset.ordered]
  exact coe_mem _

theorem ordered_mem' (hJ : ↑J ⊆ C) (n : Fin J.card) : J.ordered n ∈ C :=
  hJ (ordered_mem n)

theorem iUnion_ordered (J : Finset (Set α)) : (⋃ i : Fin J.card, J.ordered i) = ⋃₀ J := by
  conv_rhs => rw [← map_ordered J]
  simp_rw [sUnion_eq_biUnion, coe_map, Set.biUnion_image]
  simp only [mem_coe, Finset.mem_univ, iUnion_true]

theorem sum_ordered {β : Type*} [AddCommMonoid β] (J : Finset (Set α)) (m : Set α → β) :
    ∑ i : Fin J.card, m (J.ordered i) = ∑ u in J, m u := by
  conv_rhs => rw [← map_ordered J]
  rw [sum_map]

/-- The n first sets in `J.ordered`. -/
noncomputable def finsetLT (J : Finset (Set α)) : Fin J.card → Finset (Set α) := fun n ↦
  (Finset.filter (fun j : Fin J.card ↦ j < n) univ).map J.ordered

theorem finsetLT_zero {J : Finset (Set α)} (hJ : 0 < J.card) : finsetLT J ⟨0, hJ⟩ = ∅ := by
  rw [finsetLT]
  simp only [univ_eq_attach, map_eq_empty]
  rw [filter_eq_empty_iff]
  intro n _
  simp only [not_lt]
  rw [← Fin.eta n n.2, Fin.mk_le_mk]
  exact zero_le'

theorem finsetLT_mono (J : Finset (Set α)) : Monotone (finsetLT J) := by
  intro n m hnm s
  rw [finsetLT, mem_map]
  rintro ⟨i, hi, rfl⟩
  simp only [Finset.ordered, finsetLT, Equiv.asEmbedding_apply, Function.comp_apply, mem_map,
    mem_filter, Finset.mem_univ, true_and_iff, exists_prop]
  refine ⟨i, ?_, rfl⟩
  rw [mem_filter] at hi
  exact hi.2.trans_le hnm

theorem finsetLT_subset (J : Finset (Set α)) (n : Fin J.card) : finsetLT J n ⊆ J := by
  intro u; rw [finsetLT, mem_map]; rintro ⟨i, _, rfl⟩; exact ordered_mem i

theorem mem_finsetLT (J : Finset (Set α)) (n : Fin J.card) {s : Set α} :
    s ∈ finsetLT J n ↔ ∃ m < n, s = J.ordered m := by
  rw [finsetLT, mem_map]
  simp only [mem_filter, Finset.mem_univ, true_and_iff, Equiv.asEmbedding_apply,
    Function.comp_apply, exists_prop]
  simp_rw [@eq_comm _ _ s]

theorem ordered_mem_finsetLT (J : Finset (Set α)) {n m : Fin J.card} (hnm : n < m) :
    J.ordered n ∈ finsetLT J m := by rw [mem_finsetLT _ _]; exact ⟨n, hnm, rfl⟩

theorem finsetLT_subset' (J : Finset (Set α)) (hJ : ↑J ⊆ C) (n : Fin J.card) :
    ↑(finsetLT J n) ⊆ C :=
  (Finset.coe_subset.mpr (finsetLT_subset J n)).trans hJ

theorem sUnion_finsetLT_eq_bUnion (J : Finset (Set α)) (n : Fin J.card) :
    ⋃₀ (finsetLT J n : Set (Set α)) = ⋃ i < n, J.ordered i := by
  ext1 a
  simp_rw [mem_sUnion, mem_coe, mem_finsetLT, mem_iUnion]
  constructor
  · rintro ⟨t, ⟨m, hmn, rfl⟩, hat⟩
    exact ⟨m, hmn, hat⟩
  · rintro ⟨m, hmn, hat⟩
    exact ⟨J.ordered m, ⟨m, hmn, rfl⟩, hat⟩

namespace IsSetSemiring

section IndexedDiff₀

theorem eq_add_diffFinset_of_subset (hC : IsSetSemiring C) (m : Set α → ℝ≥0∞)
    (m_add :
      ∀ (I : Finset (Set α)) (_h_ss : ↑I ⊆ C) (_h_dis : PairwiseDisjoint (I : Set (Set α)) id)
        (_h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) = ∑ u in I, m u)
    (hs : s ∈ C) (ht : t ∈ C) (hst : s ⊆ t) [DecidableEq (Set α)] :
    m t = m s + ∑ i in hC.diffFinset ht hs, m i := by
  classical
  conv_lhs => rw [← hC.sUnion_insert_diffFinset ht hs hst]
  rw [← coe_insert, m_add]
  · rw [sum_insert]
    exact hC.not_mem_diffFinset ht hs
  · rw [coe_insert]
    exact Set.insert_subset hs (hC.diffFinset_subset ht hs)
  · rw [coe_insert]
    exact hC.pairwiseDisjoint_insert_diffFinset ht hs
  · rw [coe_insert]
    rwa [hC.sUnion_insert_diffFinset ht hs hst]

/-- A finite set of sets in `C` such that
`⋃₀ ↑(hC.indexedDiff₀ hJ n) = J.ordered n \ ⋃₀ finsetLT J n`. -/
noncomputable def indexedDiff₀ (hC : IsSetSemiring C) {J : Finset (Set α)} (hJ : ↑J ⊆ C)
    (n : Fin J.card) : Finset (Set α) :=
  hC.diffFinset₀ (ordered_mem' hJ n) (finsetLT_subset' J hJ n)

theorem sUnion_indexedDiff₀ (hC : IsSetSemiring C) {J : Finset (Set α)} (hJ : ↑J ⊆ C)
    (n : Fin J.card) : ⋃₀ ↑(hC.indexedDiff₀ hJ n) = J.ordered n \ ⋃₀ finsetLT J n :=
  (hC.diff_sUnion_eq_sUnion_diffFinset₀ _ _).symm

theorem indexedDiff₀_subset (hC : IsSetSemiring C) {J : Finset (Set α)} (hJ : ↑J ⊆ C)
    (n : Fin J.card) : ↑(hC.indexedDiff₀ hJ n) ⊆ C :=
  hC.diffFinset₀_subset _ _

theorem sUnion_indexedDiff₀_subset (hC : IsSetSemiring C) {J : Finset (Set α)} (hJ : ↑J ⊆ C)
    (n : Fin J.card) : ⋃₀ ↑(hC.indexedDiff₀ hJ n) ⊆ J.ordered n :=
  subset_trans (hC.sUnion_indexedDiff₀ hJ n).subset Set.diff_subset

theorem subset_of_mem_indexedDiff₀ (hC : IsSetSemiring C) {J : Finset (Set α)} (hJ : ↑J ⊆ C)
    (n : Fin J.card) (t) (ht : t ∈ hC.indexedDiff₀ hJ n) : t ⊆ J.ordered n :=
  (subset_sUnion_of_mem ht).trans (sUnion_indexedDiff₀_subset hC hJ n)

theorem empty_not_mem_indexedDiff₀ (hC : IsSetSemiring C) {J : Finset (Set α)} (hJ : ↑J ⊆ C)
    (n : Fin J.card) : ∅ ∉ hC.indexedDiff₀ hJ n := by
  rw [IsSetSemiring.indexedDiff₀]; exact hC.empty_not_mem_diffFinset₀ _ _

theorem subset_ordered_of_mem_indexedDiff₀ (hC : IsSetSemiring C) {J : Finset (Set α)} (hJ : ↑J ⊆ C)
    {n : Fin J.card} (h : s ∈ hC.indexedDiff₀ hJ n) : s ⊆ J.ordered n := by
  refine Subset.trans ?_
    (hC.sUnion_diffFinset₀_subset (ordered_mem' hJ n) (finsetLT_subset' J hJ n))
  exact subset_sUnion_of_mem h

theorem iUnion_sUnion_indexedDiff₀ (hC : IsSetSemiring C) {J : Finset (Set α)} (hJ : ↑J ⊆ C) :
    (⋃ i, ⋃₀ (hC.indexedDiff₀ hJ i : Set (Set α))) = ⋃₀ J := by
  rw [← iUnion_ordered]
  refine subset_antisymm (fun a ↦ ?_) fun a ↦ ?_
  · simp_rw [mem_iUnion, mem_sUnion]
    rintro ⟨i, t, ht, hat⟩
    exact ⟨i, subset_ordered_of_mem_indexedDiff₀ hC hJ ht hat⟩
  · simp_rw [mem_iUnion]
    intro h
    have h' : ∃ (i : ℕ) (hi : i < J.card), a ∈ J.ordered ⟨i, hi⟩ := by
      obtain ⟨i, hai⟩ := h
      refine ⟨i.1, i.2, ?_⟩
      convert hai
    classical
    let i : ℕ := Nat.find h'
    have hi : i < J.card := (Nat.find_spec h').choose
    have ha_mem_i : a ∈ J.ordered ⟨i, hi⟩ := (Nat.find_spec h').choose_spec
    refine ⟨⟨i, hi⟩, ?_⟩
    rw [sUnion_indexedDiff₀, Set.mem_diff]
    refine ⟨ha_mem_i, ?_⟩
    rw [sUnion_finsetLT_eq_bUnion]
    simp only [mem_iUnion, exists_prop, not_exists, not_and]
    intro j hj_lt hj
    have hj_lt' : ↑j < i := by rwa [← Fin.eta j j.2, Fin.mk_lt_mk] at hj_lt
    refine (Nat.lt_find_iff h' j).mp hj_lt' j le_rfl ⟨hj_lt'.trans hi, ?_⟩
    convert hj

theorem disjoint_sUnion_finsetLT_of_mem_indexedDiff₀ (hC : IsSetSemiring C) {J : Finset (Set α)}
    (hJ : ↑J ⊆ C) {n : Fin J.card} (h : s ∈ hC.indexedDiff₀ hJ n) :
    Disjoint s (⋃₀ finsetLT J n) := by
  refine Disjoint.mono_left (subset_sUnion_of_mem h : s ⊆ ⋃₀ ↑(hC.indexedDiff₀ hJ n)) ?_
  rw [IsSetSemiring.sUnion_indexedDiff₀ hC hJ n, Set.disjoint_iff_inter_eq_empty, Set.inter_comm,
    inter_diff_self]

theorem disjoint_ordered_of_mem_indexedDiff₀ (hC : IsSetSemiring C) {J : Finset (Set α)} (hJ : ↑J ⊆ C)
    {n m : Fin J.card} (h : s ∈ hC.indexedDiff₀ hJ n) (hnm : m < n) :
    Disjoint s (J.ordered m) := by
  refine Disjoint.mono_right ?_ (hC.disjoint_sUnion_finsetLT_of_mem_indexedDiff₀ hJ h)
  exact subset_sUnion_of_mem (ordered_mem_finsetLT J hnm)

theorem disjoint_of_mem_indexedDiff₀_of_lt (hC : IsSetSemiring C) {J : Finset (Set α)} (hJ : ↑J ⊆ C)
    {n m : Fin J.card} (hnm : n < m) (hs : s ∈ hC.indexedDiff₀ hJ n)
    (ht : t ∈ hC.indexedDiff₀ hJ m) : Disjoint s t := by
  have hs_subset : s ⊆ J.ordered n := hC.subset_ordered_of_mem_indexedDiff₀ hJ hs
  have hs_disj : Disjoint t (J.ordered n) := hC.disjoint_ordered_of_mem_indexedDiff₀ hJ ht hnm
  exact Disjoint.mono_left hs_subset hs_disj.symm

theorem disjoint_of_mem_indexedDiff₀ (hC : IsSetSemiring C) {J : Finset (Set α)} (hJ : ↑J ⊆ C)
    {n m : Fin J.card} (hnm : n ≠ m) (hs : s ∈ hC.indexedDiff₀ hJ n)
    (ht : t ∈ hC.indexedDiff₀ hJ m) : Disjoint s t := by
  cases' lt_or_lt_iff_ne.mpr hnm with h h
  · exact hC.disjoint_of_mem_indexedDiff₀_of_lt hJ h hs ht
  · exact (hC.disjoint_of_mem_indexedDiff₀_of_lt hJ h ht hs).symm

theorem disjoint_indexedDiff₀ (hC : IsSetSemiring C) {J : Finset (Set α)} (hJ : ↑J ⊆ C)
    {n m : Fin J.card} (hnm : n ≠ m) :
    Disjoint (hC.indexedDiff₀ hJ n) (hC.indexedDiff₀ hJ m) := by
  classical
  rw [Finset.disjoint_iff_inter_eq_empty]
  ext1 s
  simp only [Finset.mem_inter, Finset.not_mem_empty, iff_false_iff, not_and]
  intro hsn hsm
  have : Disjoint s s := hC.disjoint_of_mem_indexedDiff₀ hJ hnm hsn hsm
  rw [Set.disjoint_iff_inter_eq_empty, Set.inter_self] at this
  rw [this] at hsn
  exact hC.empty_not_mem_indexedDiff₀ _ _ hsn

theorem pairwiseDisjoint_indexedDiff₀ (hC : IsSetSemiring C) {J : Finset (Set α)} (hJ : ↑J ⊆ C) :
    PairwiseDisjoint (↑(univ : Finset (Fin J.card))) (hC.indexedDiff₀ hJ) := fun _ _ _ _ hnm ↦
  hC.disjoint_indexedDiff₀ hJ hnm

theorem pairwiseDisjoint_indexedDiff₀' (hC : IsSetSemiring C) {J : Finset (Set α)} (hJ : ↑J ⊆ C)
    (n : Fin J.card) : PairwiseDisjoint ↑(hC.indexedDiff₀ hJ n) (id : Set α → Set α) :=
  hC.pairwiseDisjoint_diffFinset₀ _ _

end IndexedDiff₀

section AllDiff₀

/-- The union of all sets in `indexedDiff₀`, as a `finset`. -/
noncomputable def allDiff₀ (hC : IsSetSemiring C) {J : Finset (Set α)} (hJ : ↑J ⊆ C) :
    Finset (Set α) :=
  Finset.disjiUnion univ (hC.indexedDiff₀ hJ) (hC.pairwiseDisjoint_indexedDiff₀ hJ)

theorem pairwiseDisjoint_allDiff₀ (hC : IsSetSemiring C) {J : Finset (Set α)} (hJ : ↑J ⊆ C) :
    PairwiseDisjoint ↑(hC.allDiff₀ hJ) (id : Set α → Set α) := by
  intro u hu v hv huv
  simp_rw [Function.onFun]
  simp_rw [IsSetSemiring.allDiff₀, mem_coe, Finset.mem_disjiUnion] at hu hv
  obtain ⟨n, _, huBn⟩ := hu
  obtain ⟨m, _, hvBm⟩ := hv
  by_cases hnm : n = m
  · rw [← hnm] at hvBm
    exact hC.pairwiseDisjoint_indexedDiff₀' _ n huBn hvBm huv
  · exact hC.disjoint_of_mem_indexedDiff₀ hJ hnm huBn hvBm

theorem allDiff₀_subset (hC : IsSetSemiring C) {J : Finset (Set α)} (hJ : ↑J ⊆ C) :
    ↑(hC.allDiff₀ hJ) ⊆ C := by
  intro s
  rw [mem_coe, IsSetSemiring.allDiff₀, mem_disjiUnion]
  rintro ⟨n, _, h_mem⟩
  exact hC.indexedDiff₀_subset hJ n h_mem

theorem Finset.sUnion_disjUnion {α β : Type*} {f : α → Finset (Set β)} (I : Finset α)
    (hf : (I : Set α).PairwiseDisjoint f) :
    ⋃₀ (I.disjiUnion f hf : Set (Set β)) = ⋃ a ∈ I, ⋃₀ ↑(f a) := by
  ext1 b
  simp only [mem_sUnion, mem_iUnion, mem_coe, exists_prop, mem_disjiUnion]
  constructor
  · rintro ⟨t, ⟨a, haI, hatf⟩, hbt⟩
    exact ⟨a, haI, t, hatf, hbt⟩
  · rintro ⟨a, haI, t, hatf, hbt⟩
    exact ⟨t, ⟨a, haI, hatf⟩, hbt⟩

theorem sUnion_allDiff₀ (hC : IsSetSemiring C) {J : Finset (Set α)} (hJ : ↑J ⊆ C) :
    ⋃₀ (hC.allDiff₀ hJ : Set (Set α)) = ⋃₀ J := by
  simp only [allDiff₀, Finset.sUnion_disjUnion, Finset.mem_univ, iUnion_true,
    iUnion_sUnion_indexedDiff₀]

end AllDiff₀

end IsSetSemiring

end Ordered

namespace IsSetRing

theorem iUnion_le_mem (hC : IsSetRing C) {s : ℕ → Set α} (hs : ∀ n, s n ∈ C) (n : ℕ) :
    (⋃ i ≤ n, s i) ∈ C := by
  induction' n with n hn
  · simp only [Nat.zero_eq, le_zero_iff, iUnion_iUnion_eq_left, exists_prop]
    exact hs 0
  rw [Set.bUnion_le_succ]
  exact hC.union_mem hn (hs _)

theorem iInter_le_mem (hC : IsSetRing C) {s : ℕ → Set α} (hs : ∀ n, s n ∈ C) (n : ℕ) :
    (⋂ i ≤ n, s i) ∈ C := by
  induction' n with n hn
  · simp only [Nat.zero_eq, le_zero_iff, iInter_iInter_eq_left, exists_prop]
    exact hs 0
  rw [Set.bInter_le_succ]
  exact hC.inter_mem hn (hs _)

theorem partialSups_mem (hC : IsSetRing C) {s : ℕ → Set α} (hs : ∀ n, s n ∈ C) (n : ℕ) :
    partialSups s n ∈ C := by rw [partialSups_eq_biSup, iSup_eq_iUnion]; exact hC.iUnion_le_mem hs n

theorem disjointed_mem (hC : IsSetRing C) {s : ℕ → Set α} (hs : ∀ n, s n ∈ C) (n : ℕ) :
    disjointed s n ∈ C := by
  cases n with
  | zero => rw [disjointed_zero]; exact hs 0
  | succ n => rw [disjointed_succ]; exact hC.diff_mem (hs n.succ) (hC.partialSups_mem hs n)

theorem accumulate_mem (hC : IsSetRing C) {s : ℕ → Set α} (hs : ∀ i, s i ∈ C) (n : ℕ) :
    Set.Accumulate s n ∈ C := by
  induction' n with n hn
  · simp only [Set.Accumulate, le_zero_iff, Set.iUnion_iUnion_eq_left, hs 0, Nat.zero_eq,
      nonpos_iff_eq_zero, iUnion_iUnion_eq_left]
  · rw [Set.accumulate_succ]
    exact hC.union_mem hn (hs _)

end IsSetRing

/-- A field of sets is a family of sets which is stable under union, difference, and contains
the empty set and the whole space. -/
structure IsSetField (C : Set (Set α)) extends IsSetRing C : Prop where
  univ_mem : Set.univ ∈ C

namespace IsSetField

theorem inter_mem (hC : IsSetField C) (hs : s ∈ C) (ht : t ∈ C) : s ∩ t ∈ C :=
  hC.toIsSetRing.inter_mem hs ht

theorem compl_mem (hC :IsSetField C) (hs : s ∈ C) : sᶜ ∈ C := by
  rw [compl_eq_univ_diff]; exact hC.diff_mem hC.univ_mem hs

theorem toIsSetSemiring (hC :IsSetField C) : IsSetSemiring C :=
  hC.toIsSetRing.isSetSemiring

theorem iUnion_le_mem (hC :IsSetField C) {s : ℕ → Set α} (hs : ∀ n, s n ∈ C) (n : ℕ) :
    (⋃ i ≤ n, s i) ∈ C :=
  hC.toIsSetRing.iUnion_le_mem hs n

theorem iInter_le_mem (hC :IsSetField C) {s : ℕ → Set α} (hs : ∀ n, s n ∈ C) (n : ℕ) :
    (⋂ i ≤ n, s i) ∈ C :=
  hC.toIsSetRing.iInter_le_mem hs n

theorem partialSups_mem (hC :IsSetField C) {s : ℕ → Set α} (hs : ∀ n, s n ∈ C) (n : ℕ) :
    partialSups s n ∈ C :=
  hC.toIsSetRing.partialSups_mem hs n

theorem disjointed_mem (hC :IsSetField C) {s : ℕ → Set α} (hs : ∀ n, s n ∈ C) (n : ℕ) :
    disjointed s n ∈ C :=
  hC.toIsSetRing.disjointed_mem hs n

end IsSetField

end MeasureTheory
