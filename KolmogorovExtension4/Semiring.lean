/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
import KolmogorovExtension4.AuxLemmas
import Mathlib.MeasureTheory.SetSemiring

/-! # Semirings of sets

A semi-ring of sets `C` is a family of sets containing `∅`, stable by intersection and such that
for all `s, t ∈ C`, `t \ s` is equal to a disjoint union of finitely many sets in `C`.

-/


variable {α : Type*} {C : Set (Set α)} {s t : Set α} {J : Finset (Set α)}

open Finset Set
open scoped ENNReal

namespace MeasureTheory

namespace IsSetSemiring

theorem eq_add_disjointOfDiff_of_subset (hC : IsSetSemiring C) (m : Set α → ℝ≥0∞)
    (m_add : ∀ (I : Finset (Set α)) (_ : ↑I ⊆ C) (_ : PairwiseDisjoint (I : Set (Set α)) id)
        (_h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) = ∑ u ∈ I, m u)
    (hs : s ∈ C) (ht : t ∈ C) (hst : s ⊆ t) :
    m t = m s + ∑ i ∈ hC.disjointOfDiff ht hs, m i := by
  classical
  conv_lhs => rw [← hC.sUnion_insert_disjointOfDiff ht hs hst]
  rw [← coe_insert, m_add]
  · rw [sum_insert]
    exact hC.nmem_disjointOfDiff ht hs
  · rw [coe_insert]
    exact Set.insert_subset hs (hC.subset_disjointOfDiff ht hs)
  · rw [coe_insert]
    exact hC.pairwiseDisjoint_insert_disjointOfDiff ht hs
  · rw [coe_insert]
    rwa [hC.sUnion_insert_disjointOfDiff ht hs hst]

section AllDiffFinset₀

/-- This is a finset of pairwise disjoint sets in the set semi-ring `C`, such that
`⋃₀ hC.unionDisjointOfUnion J hJ = ⋃₀ J`. -/
noncomputable def unionDisjointOfUnion (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) :
    Finset (Set α) :=
  Finset.disjiUnion J (hC.disjointOfUnion hJ) (hC.pairwiseDisjoint_disjointOfUnion hJ)

lemma pairwiseDisjoint_unionDisjointOfUnion (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) :
    PairwiseDisjoint ↑(hC.unionDisjointOfUnion hJ) (id : Set α → Set α) := by
  intro u hu v hv huv
  simp_rw [unionDisjointOfUnion, mem_coe, Finset.mem_disjiUnion] at hu hv
  have h'u : u ∈ ⋃ x ∈ J, ↑(hC.disjointOfUnion hJ x) := by
    simp only [mem_iUnion, mem_coe, exists_prop, hu]
  have h'v : v ∈ ⋃ x ∈ J, ↑(hC.disjointOfUnion hJ x) := by
    simp only [mem_iUnion, mem_coe, exists_prop, hv]
  exact hC.pairwiseDisjoint_biUnion_disjointOfUnion hJ h'u h'v huv

lemma unionDisjointOfUnion_subset (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) :
    ↑(hC.unionDisjointOfUnion hJ) ⊆ C := by
  intro s
  rw [mem_coe, unionDisjointOfUnion, mem_disjiUnion]
  rintro ⟨n, h_mem, h'⟩
  exact hC.disjointOfUnion_subset hJ h_mem h'

lemma sUnion_unionDisjointOfUnion (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) :
    ⋃₀ (hC.unionDisjointOfUnion hJ : Set (Set α)) = ⋃₀ J := by
  simp only [unionDisjointOfUnion, Finset.sUnion_disjiUnion, Finset.mem_univ, iUnion_true]
  rw [← hC.sUnion_disjointOfUnion hJ]
  ext
  simp
  tauto

end AllDiffFinset₀

end IsSetSemiring

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
