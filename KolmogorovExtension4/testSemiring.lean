/-
Copyright (c) 2025 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
import KolmogorovExtension4.AuxLemmas
import Mathlib.MeasureTheory.SetSemiring
/-
  ## Main results

  * `allDiffFinset₀'_props`: In a semiring, write a union of elements of the semiring as a disjoint union of elements of the semiring.
-/

open Finset Set MeasureTheory Order

open scoped NNReal Topology ENNReal

namespace MeasureTheory

namespace IsSetSemiring

-- Goes in SetSemiring.lean

variable {α : Type*} {C : Set (Set α)} {s t : Set α}
    {J : Finset (Set α)}
-- PR #20931
lemma sUnion_diffFinset₀_subsets (hC : IsSetSemiring C) {I : Finset (Set α)} (hs : s ∈ C) (hI : ↑I ⊆ C) :
    ∀ t ∈ (hC.diffFinset₀ hs hI : Set (Set α)), t ⊆ s \ ⋃₀ I := by
  rw [← sUnion_subset_iff, hC.diff_sUnion_eq_sUnion_diffFinset₀ hs hI]

-- PR #20931
lemma sUnion_diffFinset₀_subsets' (hC : IsSetSemiring C) {I : Finset (Set α)} (hs : s ∈ C) (hI : ↑I ⊆ C) :
    ∀ t ∈ (hC.diffFinset₀ hs hI : Set (Set α)), t ⊆ s := by
  rw [← sUnion_subset_iff]
  exact hC.sUnion_diffFinset₀_subset hs hI

end IsSetSemiring

end MeasureTheory


-- goes to Mathlib.Order.CompleteLattice, line 1652

variable [CompleteLattice α]

-- PR #20931
lemma disjoint_of_sSup_disjoint_of_le_of_le {a b : α} {c d : Set α} (hs : ∀ e ∈ c, e ≤ a) (ht : ∀ e ∈ d, e ≤ b)
    (hd : Disjoint a b) (he : ⊥ ∉ c ∨ ⊥ ∉ d) : Disjoint c d := by
  rw [disjoint_iff_forall_ne]
  intros x hx y hy
  rw [Disjoint.ne_iff]
  aesop
  exact Disjoint.mono (hs x hx) (ht y hy) hd

-- PR #20931
lemma disjoint_of_sSup_disjoint {a b : Set α} (hd : Disjoint (sSup a) (sSup b)) (he : ⊥ ∉ a ∨ ⊥ ∉ b)
    : Disjoint a b :=
  disjoint_of_sSup_disjoint_of_le_of_le (fun _ hc => le_sSup hc) (fun _ hc => le_sSup hc) hd he

namespace MeasureTheory

namespace IsSetSemiring

variable {α : Type*} {C : Set (Set α)} {s t : Set α}
    {J : Finset (Set α)}

/- In a `hC : IsSetSemiring C`, for a `J : Finset (Set α)` with `J ⊆ C`, there is for every `x in J` some `K x ⊆ C` finite, such that
    * `⋃ x ∈ J, K x` are pairwise disjoint and do not contan ∅,
    * `⋃ s ∈ K x, s ⊆ x`,
    * `⋃ x ∈ J, x = ⋃ x ∈ J, ⋃ s ∈ K x, s`.
-/
set_option trace.split.failure true


variable [DecidableEq (Set α)]

-- PR #20931
theorem allDiffFinset₀_props (hC : IsSetSemiring C) (h1 : ↑J ⊆ C) :
    ∃ K : Set α → Finset (Set α),
      J.toSet.PairwiseDisjoint K
      ∧ (∀ i ∈ J, (K i).toSet ⊆ C)
      ∧ PairwiseDisjoint (⋃ x ∈ J, (K x).toSet) id
      ∧ (∀ j ∈ J, ⋃₀ K j ⊆ j)
      ∧ (∀ j ∈ J, ∅ ∉ K j)
      ∧ (⋃₀ J.toSet) = ⋃₀ (⋃ x ∈ J, (K x).toSet) := by
  induction J using Finset.cons_induction with
  | empty => simp
  | cons s J hJ hind =>
    rw [cons_eq_insert, coe_insert, Set.insert_subset_iff] at h1
    obtain ⟨h11, h12⟩ := h1
    obtain ⟨K, hK0, ⟨hK1, hK2, hK3, hK4, hK5⟩⟩ := hind h12
    let K' : Finset (Set α) := hC.diffFinset₀ h11 h12
    let K1 : Set α → Finset (Set α) := fun (t : Set α) ↦ if t = s then K' else K t
    have hK1s : K1 s = K' := by simp [K1]
    have hK1_of_ne t (ht : t ≠ s) : K1 t = K t := by simp [K1, ht]
    use K1
    simp only [cons_eq_insert, disjiUnion_eq_biUnion, Finset.biUnion_insert, coe_union, coe_biUnion,
      mem_coe, Set.union_subset_iff, iUnion_subset_iff, Finset.mem_insert, sUnion_subset_iff,
      forall_eq_or_imp, coe_insert, sUnion_insert, exists_and_left, exists_prop]
    -- two simplification rules for induction hypothesis
    have ht1' : ∀ x ∈ J, K1 x = K x := fun x hx ↦ hK1_of_ne _ (fun h_eq ↦ hJ (h_eq ▸ hx))
    have ht2 : (⋃ x ∈ J, (K1 x).toSet) = ⋃ x ∈ J, (K x).toSet := by
      apply iUnion₂_congr
      intros x hx
      exact mod_cast hK1_of_ne _ (ne_of_mem_of_not_mem hx hJ)
    simp only [hK1s]
    refine ⟨?_, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
    · apply Set.Pairwise.insert
      · intro j hj i hi hij
        rw [Function.onFun, ht1' j hj, ht1' i hi]
        exact hK0 hj hi hij
      · intro i hi hsi
        have h7 : Disjoint K'.toSet (K i).toSet := by
          refine disjoint_of_sSup_disjoint_of_le_of_le (hC.sUnion_diffFinset₀_subsets h11 h12) ?_
            (@disjoint_sdiff_left _ (⋃₀ J) s) (Or.inl (hC.empty_not_mem_diffFinset₀ h11 h12))
          simp only [mem_coe, Set.le_eq_subset]
          apply sUnion_subset_iff.mp
          exact (hK3 i hi).trans (subset_sUnion_of_mem hi)
        have h8 : Function.onFun Disjoint K1 s i := by
          refine Finset.disjoint_iff_inter_eq_empty.mpr ?_
          rw [ht1' i hi, hK1s]
          rw [Set.disjoint_iff_inter_eq_empty] at h7
          exact mod_cast h7
        exact ⟨h8, Disjoint.symm h8⟩
    · exact hC.diffFinset₀_subset h11 h12
    · intros i hi
      rw [ht1' i hi]
      exact hK1 i hi
    · simp only [iUnion_iUnion_eq_or_left]
      refine pairwiseDisjoint_union.mpr ⟨?_, ?_, ?_⟩
      · rw [hK1s]
        exact hC.pairwiseDisjoint_diffFinset₀ h11 h12
      · simpa [ht2]
      · simp only [mem_coe, mem_iUnion, exists_prop, ne_eq, id_eq, forall_exists_index, and_imp]
        intros i hi j x hx h3 h4
        -- We show i ⊆ s \ ⋃₀ J
        have ki : i ⊆ s \ ⋃₀ J := by
          apply hC.sUnion_diffFinset₀_subsets h11 h12
          rw [hK1s] at hi
          exact hi
        -- We show j ⊆ ⋃₀ K x ⊆ x ∈ J
        have hx2 : j ⊆ x := by
          rw [ht1' x hx] at h3
          exact subset_trans (subset_sUnion_of_mem h3) (hK3 x hx)
        have kj : j ⊆ ⋃₀ J := hx2.trans <| subset_sUnion_of_mem hx
        apply disjoint_of_subset ki kj
        exact disjoint_sdiff_left
    · exact hC.sUnion_diffFinset₀_subsets' h11 h12
    · intros a ha
      simp_rw [hK1_of_ne _ (ne_of_mem_of_not_mem ha hJ)]
      change ∀ t' ∈ (K a).toSet, t' ⊆ a
      rw [← sUnion_subset_iff]
      exact hK3 a ha
    · refine ⟨hC.empty_not_mem_diffFinset₀ h11 h12, ?_⟩
      intros a ha
      rw [ht1' a ha]
      exact hK4 a ha
    · simp only [iUnion_iUnion_eq_or_left, ht2, sUnion_union, apply_ite, hK1s]
      rw [← hC.diff_sUnion_eq_sUnion_diffFinset₀ h11 h12, ← hK5]
      simp

-- PR #20931
noncomputable def allDiffFinset₀' (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) :=
  (hC.allDiffFinset₀_props hJ).choose

-- PR #20931
lemma allDiffFinset₀'_disjoint (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) :
    J.toSet.PairwiseDisjoint (hC.allDiffFinset₀' hJ) :=
  (Exists.choose_spec (hC.allDiffFinset₀_props hJ)).1

-- PR #20931
lemma allDiffFinset₀'_subsets_semiring (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) (hj : j ∈ J) :
    (allDiffFinset₀' hC hJ j).toSet ⊆ C :=
  (Exists.choose_spec (hC.allDiffFinset₀_props hJ)).2.1 _ hj

-- PR #20931
lemma allDiffFinset₀'_subset_semiring (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) :
    (disjiUnion J (hC.allDiffFinset₀' hJ) (hC.allDiffFinset₀'_disjoint hJ)).toSet ⊆ C := by
  simp only [disjiUnion_eq_biUnion, coe_biUnion, mem_coe, iUnion_subset_iff]
  exact fun _ ↦ allDiffFinset₀'_subsets_semiring hC hJ

-- PR #20931
lemma  allDiffFinset₀'_pairwiseDisjoint' (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) :
    (⋃ x ∈ J, (hC.allDiffFinset₀' hJ x).toSet).PairwiseDisjoint id :=
  (Exists.choose_spec (hC.allDiffFinset₀_props hJ)).2.2.1

-- PR #20931
lemma allDiffFinset₀'_pairwiseDisjoint (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) :
    PairwiseDisjoint (disjiUnion J (hC.allDiffFinset₀' hJ)
      (hC.allDiffFinset₀'_disjoint hJ)).toSet id := by
  simp only [disjiUnion_eq_biUnion, coe_biUnion, mem_coe]
  exact allDiffFinset₀'_pairwiseDisjoint' hC hJ

-- PR #20931
lemma allDiffFinset₀'_pairwiseDisjoints (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) (hj : j ∈ J) :
    PairwiseDisjoint (hC.allDiffFinset₀' hJ j).toSet id := by
  apply PairwiseDisjoint.subset (hC.allDiffFinset₀'_pairwiseDisjoint hJ)
  simp only [disjiUnion_eq_biUnion, coe_biUnion, mem_coe]
  apply subset_iUnion₂_of_subset j hj (by rfl)

-- PR #20931
lemma allDiffFinset₀'_subset (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) (hj : j ∈ J) :
    ⋃₀ hC.allDiffFinset₀' hJ j ⊆ j :=
  (Exists.choose_spec (hC.allDiffFinset₀_props hJ)).2.2.2.1 j hj

-- PR #20931
lemma allDiffFinset₀'_subsets (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) (hj : j ∈ J) :
    ∀ x ∈ (hC.allDiffFinset₀' hJ) j, x ⊆ j :=
  sUnion_subset_iff.mp (hC.allDiffFinset₀'_subset hJ hj)

-- PR #20931
lemma allDiffFinset₀'_empty_not_mem (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) (hj : j ∈ J) :
    ∅ ∉ hC.allDiffFinset₀' hJ j :=
  (Exists.choose_spec (hC.allDiffFinset₀_props hJ)).2.2.2.2.1 j hj

-- PR #20931
lemma allDiffFinset₀'_sUnion (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) :
    (⋃₀ J.toSet) = ⋃₀ (disjiUnion J (hC.allDiffFinset₀' hJ)
      (hC.allDiffFinset₀'_disjoint hJ)).toSet := by
  simp only [disjiUnion_eq_biUnion, coe_biUnion, mem_coe]
  exact (Exists.choose_spec (hC.allDiffFinset₀_props hJ)).2.2.2.2.2

end IsSetSemiring



namespace IsSetRing

variable {α : Type*} {C : Set (Set α)} {s t : Set α}

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

end MeasureTheory
