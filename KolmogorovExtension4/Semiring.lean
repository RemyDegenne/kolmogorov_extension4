/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
import KolmogorovExtension4.AuxLemmas
import Mathlib.MeasureTheory.SetSemiring
import KolmogorovExtension4.Ordered

/-! # Semirings of sets

A semi-ring of sets `C` is a family of sets containing `∅`, stable by intersection and such that
for all `s, t ∈ C`, `t \ s` is equal to a disjoint union of finitely many sets in `C`.

-/


open Finset Set MeasureTheory Order

open scoped NNReal Topology ENNReal

namespace MeasureTheory

variable {α : Type*} {C : Set (Set α)} {s t : Set α}

section Ordered

namespace IsSetSemiring

theorem eq_add_diffFinset_of_subset (hC : IsSetSemiring C) (m : Set α → ℝ≥0∞)
    (m_add : ∀ (I : Finset (Set α)) (_ : ↑I ⊆ C) (_ : PairwiseDisjoint (I : Set (Set α)) id)
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

section indexedDiffFinset₀

/-- A finite set of sets in `C` such that
`⋃₀ ↑(hC.indexedDiffFinset₀ J hJ n) = J.ordered n \ ⋃₀ finsetLT J n`. -/
noncomputable def indexedDiffFinset₀ (hC : IsSetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C)
    (n : Fin J.card) : Finset (Set α) :=
  hC.diffFinset₀ (hJ (ordered_mem n)) (finsetLT_subset' J hJ n)

lemma sUnion_indexedDiffFinset₀ (hC : IsSetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C)
    (n : Fin J.card) : ⋃₀ ↑(hC.indexedDiffFinset₀ J hJ n) = J.ordered n \ ⋃₀ finsetLT J n :=
  (hC.diff_sUnion_eq_sUnion_diffFinset₀ _ _).symm

lemma indexedDiffFinset₀_subset (hC : IsSetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C)
    (n : Fin J.card) : ↑(hC.indexedDiffFinset₀ J hJ n) ⊆ C :=
  hC.diffFinset₀_subset _ _

lemma sUnion_indexedDiffFinset₀_subset (hC : IsSetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C)
    (n : Fin J.card) :
    ⋃₀ ↑(hC.indexedDiffFinset₀ J hJ n) ⊆ J.ordered n :=
  subset_trans (hC.sUnion_indexedDiffFinset₀ J hJ n).subset Set.diff_subset

lemma empty_not_mem_indexedDiffFinset₀ (hC : IsSetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C)
    (n : Fin J.card) :
    ∅ ∉ hC.indexedDiffFinset₀ J hJ n := by
  rw [indexedDiffFinset₀]; exact hC.empty_not_mem_diffFinset₀ _ _

lemma subset_ordered_of_mem_indexedDiffFinset₀ (hC : IsSetSemiring C)
    (J : Finset (Set α)) (hJ : ↑J ⊆ C)
    {n : Fin J.card} (h : s ∈ hC.indexedDiffFinset₀ J hJ n) :
    s ⊆ J.ordered n :=
  (subset_sUnion_of_mem h).trans
    (hC.sUnion_diffFinset₀_subset (hJ (ordered_mem n)) (finsetLT_subset' J hJ n))

lemma iUnion_sUnion_indexedDiffFinset₀ (hC : IsSetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C) :
    (⋃ i, ⋃₀ (hC.indexedDiffFinset₀ J hJ i : Set (Set α))) = ⋃₀ J := by
  rw [← iUnion_ordered]
  refine subset_antisymm (fun a ↦ ?_) (fun a ↦ ?_)
  · simp_rw [mem_iUnion, mem_sUnion]
    rintro ⟨i, t, ht, hat⟩
    exact ⟨i, subset_ordered_of_mem_indexedDiffFinset₀ hC J hJ ht hat⟩
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
    rw [sUnion_indexedDiffFinset₀, Set.mem_diff]
    refine ⟨ha_mem_i, ?_⟩
    rw [sUnion_finsetLT_eq_biUnion]
    simp only [mem_iUnion, exists_prop, not_exists, not_and]
    intro j hj_lt hj
    have hj_lt' : ↑j < i := by rwa [← Fin.eta j j.2, Fin.mk_lt_mk] at hj_lt
    refine (Nat.lt_find_iff h' j).mp hj_lt' j le_rfl ⟨hj_lt'.trans hi, ?_⟩
    convert hj

lemma disjoint_sUnion_finsetLT_of_mem_indexedDiffFinset₀
    (hC : IsSetSemiring C) (J : Finset (Set α))
    (hJ : ↑J ⊆ C) {n : Fin J.card} (h : s ∈ hC.indexedDiffFinset₀ J hJ n) :
    Disjoint s (⋃₀ finsetLT J n) := by
  refine Disjoint.mono_left (subset_sUnion_of_mem h : s ⊆ ⋃₀ ↑(hC.indexedDiffFinset₀ J hJ n)) ?_
  rw [sUnion_indexedDiffFinset₀ hC J hJ n, Set.disjoint_iff_inter_eq_empty, Set.inter_comm,
    inter_diff_self]

lemma disjoint_ordered_of_mem_indexedDiffFinset₀ (hC : IsSetSemiring C)
    (J : Finset (Set α)) (hJ : ↑J ⊆ C)
    {n m : Fin J.card} (h : s ∈ hC.indexedDiffFinset₀ J hJ n) (hnm : m < n) :
    Disjoint s (J.ordered m) := by
  refine Disjoint.mono_right ?_ (hC.disjoint_sUnion_finsetLT_of_mem_indexedDiffFinset₀ J hJ h)
  exact subset_sUnion_of_mem (ordered_mem_finsetLT J hnm)

lemma disjoint_of_mem_indexedDiffFinset₀_of_lt (hC : IsSetSemiring C)
    (J : Finset (Set α)) (hJ : ↑J ⊆ C)
    {n m : Fin J.card} (hnm : n < m) (hs : s ∈ hC.indexedDiffFinset₀ J hJ n)
    (ht : t ∈ hC.indexedDiffFinset₀ J hJ m) : Disjoint s t := by
  have hs_subset : s ⊆ J.ordered n := hC.subset_ordered_of_mem_indexedDiffFinset₀ J hJ hs
  have hs_disj : Disjoint t (J.ordered n) :=
    hC.disjoint_ordered_of_mem_indexedDiffFinset₀ J hJ ht hnm
  exact Disjoint.mono_left hs_subset hs_disj.symm

lemma disjoint_of_mem_indexedDiffFinset₀ (hC : IsSetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C)
    {n m : Fin J.card} (hnm : n ≠ m) (hs : s ∈ hC.indexedDiffFinset₀ J hJ n)
    (ht : t ∈ hC.indexedDiffFinset₀ J hJ m) : Disjoint s t := by
  cases' lt_or_lt_iff_ne.mpr hnm with h h
  · exact hC.disjoint_of_mem_indexedDiffFinset₀_of_lt J hJ h hs ht
  · exact (hC.disjoint_of_mem_indexedDiffFinset₀_of_lt J hJ h ht hs).symm

lemma disjoint_indexedDiffFinset₀ (hC : IsSetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C)
    {n m : Fin J.card} (hnm : n ≠ m) :
    Disjoint (hC.indexedDiffFinset₀ J hJ n) (hC.indexedDiffFinset₀ J hJ m) := by
  classical
  rw [Finset.disjoint_iff_inter_eq_empty]
  ext s
  simp only [Finset.mem_inter, Finset.not_mem_empty, iff_false, not_and]
  intro hsn hsm
  have : Disjoint s s := hC.disjoint_of_mem_indexedDiffFinset₀ J hJ hnm hsn hsm
  rw [Set.disjoint_iff_inter_eq_empty, Set.inter_self] at this
  rw [this] at hsn
  exact hC.empty_not_mem_indexedDiffFinset₀ _ _ _ hsn

lemma pairwiseDisjoint_indexedDiffFinset₀ (hC : IsSetSemiring C)
    (J : Finset (Set α)) (hJ : ↑J ⊆ C) :
    PairwiseDisjoint (↑(univ : Finset (Fin J.card))) (hC.indexedDiffFinset₀ J hJ) :=
  fun _ _ _ _ hnm ↦ hC.disjoint_indexedDiffFinset₀ J hJ hnm

lemma pairwiseDisjoint_indexedDiffFinset₀' (hC : IsSetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C)
    (n : Fin J.card) : PairwiseDisjoint ↑(hC.indexedDiffFinset₀ J hJ n) (id : Set α → Set α) :=
  hC.pairwiseDisjoint_diffFinset₀ _ _

end indexedDiffFinset₀

section AllDiffFinset₀

/-- This is a finset of pairwise disjoint sets in the set semi-ring `C`, such that
`⋃₀ hC.allDiffFinset₀ J hJ = ⋃₀ J`. -/
noncomputable def allDiffFinset₀ (hC : IsSetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C) :
    Finset (Set α) :=
  Finset.disjiUnion univ (hC.indexedDiffFinset₀ J hJ) (hC.pairwiseDisjoint_indexedDiffFinset₀ J hJ)

lemma pairwiseDisjoint_allDiffFinset₀ (hC : IsSetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C) :
    PairwiseDisjoint ↑(hC.allDiffFinset₀ J hJ) (id : Set α → Set α) := by
  intro u hu v hv huv
  simp_rw [Function.onFun]
  simp_rw [allDiffFinset₀, mem_coe, Finset.mem_disjiUnion] at hu hv
  obtain ⟨n, _, huBn⟩ := hu
  obtain ⟨m, _, hvBm⟩ := hv
  by_cases hnm : n = m
  · rw [← hnm] at hvBm
    exact hC.pairwiseDisjoint_indexedDiffFinset₀' _ _ n huBn hvBm huv
  · exact hC.disjoint_of_mem_indexedDiffFinset₀ J hJ hnm huBn hvBm

lemma allDiffFinset₀_subset (hC : IsSetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C) :
    ↑(hC.allDiffFinset₀ J hJ) ⊆ C := by
  intro s
  rw [mem_coe, allDiffFinset₀, mem_disjiUnion]
  rintro ⟨n, _, h_mem⟩
  exact hC.indexedDiffFinset₀_subset J hJ n h_mem

lemma sUnion_allDiffFinset₀ (hC : IsSetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C) :
    ⋃₀ (hC.allDiffFinset₀ J hJ : Set (Set α)) = ⋃₀ J := by
  simp only [allDiffFinset₀, Finset.sUnion_disjiUnion, Finset.mem_univ, iUnion_true,
    iUnion_sUnion_indexedDiffFinset₀]

end AllDiffFinset₀

end IsSetSemiring

end Ordered

namespace IsSetRing

theorem iUnion_le_mem (hC : IsSetRing C) {s : ℕ → Set α} (hs : ∀ n, s n ∈ C) (n : ℕ) :
    (⋃ i ≤ n, s i) ∈ C := by
  induction' n with n hn
  · simp only [Nat.zero_eq, le_zero_iff, iUnion_iUnion_eq_left, exists_prop]
    exact hs 0
  rw [Set.biUnion_le_succ]
  exact hC.union_mem hn (hs _)

theorem iInter_le_mem (hC : IsSetRing C) {s : ℕ → Set α} (hs : ∀ n, s n ∈ C) (n : ℕ) :
    (⋂ i ≤ n, s i) ∈ C := by
  induction' n with n hn
  · simp only [Nat.zero_eq, le_zero_iff, iInter_iInter_eq_left, exists_prop]
    exact hs 0
  rw [Set.biInter_le_succ]
  exact hC.inter_mem hn (hs _)

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
