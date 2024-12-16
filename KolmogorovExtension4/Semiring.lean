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

open Finset Set MeasureTheory Order

open scoped NNReal Topology ENNReal

namespace MeasureTheory

variable {α : Type*} {C : Set (Set α)} {s t : Set α}

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

section AllDiffFinset₀Exist

lemma allDiffFinset₀_props (hC : IsSetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C)
  [DecidableEq (Set α)] : ∃ K : Finset (Set α), (↑K ⊆ C) ∧ (PairwiseDisjoint
  (K : Set (Set α)) id) ∧ (⋃₀ (J : Set (Set α))) = (⋃₀ (K : Set (Set α))) := by
  revert hJ
  apply @Finset.cons_induction (Set α) (fun (J : Finset (Set α)) => (↑J ⊆ C) → (∃ K : Finset (Set α), (↑K ⊆ C) ∧ (PairwiseDisjoint (K : Set (Set α)) id) ∧ (⋃₀ J) = (⋃₀ (K : Set (Set α))))) _ _ J
  · intro _
    use ∅
    simp only [coe_empty, Set.empty_subset, pairwiseDisjoint_empty, sUnion_empty, and_self]
  · intros j J hj hJ h
    simp only [coe_cons] at h
    obtain h' := (@Set.insert_subset_iff (Set α) j ↑J C).1 h
    specialize hJ h'.2
    rcases hJ with ⟨K, h1, h2, h3⟩
    let K' := hC.diffFinset₀ h'.1 h'.2
    simp [IsSetSemiring.diffFinset₀] at K'
    obtain hK'1 := hC.diffFinset₀_subset h'.1 h'.2
    obtain hK'2 := hC.pairwiseDisjoint_diffFinset₀ h'.1 h'.2
    obtain hK'3 := hC.diff_sUnion_eq_sUnion_diffFinset₀ h'.1 h'.2
    use K ∪ K'
    constructor
    · simp only [coe_union, Set.union_subset_iff]
      refine ⟨h1, hK'1⟩
    · constructor
      · simp only [coe_union]
        apply Set.PairwiseDisjoint.union h2 hK'2
        intros i hi i' hi' _
        simp only [id_eq]
        obtain h'i : i ⊆ ⋃₀ ↑J := by
          rw [h3]
          exact subset_sUnion_of_subset (↑K) i (fun ⦃a⦄ a => a) hi
        obtain h'i' : i' ⊆ (⋃₀ ↑J)ᶜ := by
          apply le_trans _ (diff_subset_compl j (⋃₀ ↑J))
          rw [hK'3]
          exact subset_sUnion_of_subset (↑K') i' (fun ⦃a⦄ a => a) hi'
        exact Disjoint.mono h'i h'i' (disjoint_compl_right_iff_subset.mpr fun ⦃a⦄ a => a)
      · simp only [cons_eq_insert, coe_insert, sUnion_insert, coe_union]
        rw [← diff_union_self, Set.union_comm, sUnion_union ↑K (K' : Set (Set α)), hK'3, h3]

end AllDiffFinset₀Exist

section AllDiffFinset₀

/-- This is a finset of pairwise disjoint sets in the set semi-ring `C`, such that
`⋃₀ hC.allDiffFinset₀ J hJ = ⋃₀ J`. -/
noncomputable def allDiffFinset₀ [DecidableEq (Set α)] (hC : IsSetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C) := (allDiffFinset₀_props hC J hJ).choose

lemma props_allDiffFinset₀ [DecidableEq (Set α)] (hC : IsSetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C) : (↑(allDiffFinset₀ hC J hJ) ⊆ C) ∧ (PairwiseDisjoint ((allDiffFinset₀ hC J hJ) : Set (Set α)) id) ∧ (⋃₀ (J : Set (Set α))) = (⋃₀ ((allDiffFinset₀ hC J hJ) : Set (Set α)))
 := by
  simp_rw [allDiffFinset₀]
  apply Exists.choose_spec (allDiffFinset₀_props hC J hJ)

lemma pairwiseDisjoint_allDiffFinset₀ [DecidableEq (Set α)]  (hC : IsSetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C) :
    PairwiseDisjoint ↑(allDiffFinset₀ hC J hJ) (id : Set α → Set α) := (props_allDiffFinset₀ hC J hJ).2.1

lemma allDiffFinset₀_subset [DecidableEq (Set α)] (hC : IsSetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C) :
    ↑(allDiffFinset₀ hC J hJ) ⊆ C :=
    (props_allDiffFinset₀ hC J hJ).1

lemma sUnion_allDiffFinset₀ [DecidableEq (Set α)] (hC : IsSetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C) :
    ⋃₀ (allDiffFinset₀ hC J hJ : Set (Set α)) = ⋃₀ J :=
    (props_allDiffFinset₀ hC J hJ).2.2.symm

end AllDiffFinset₀

end IsSetSemiring

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
