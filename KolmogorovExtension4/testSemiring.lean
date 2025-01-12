/-
Copyright (c) 2025 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
import KolmogorovExtension4.AuxLemmas
-- import Mathlib.MeasureTheory.SetSemiring
import Mathlib
/-
  ## Main results

  * `allDiffFinset₀'_props`: In a semiring, write a union of elements of the semiring as a disjoint union of elements of the semiring.
-/

open Finset Set MeasureTheory Order

open scoped NNReal Topology ENNReal

namespace MeasureTheory

namespace IsSetSemiring

variable {α : Type*} {C : Set (Set α)} {s t : Set α}
    [DecidableEq (Set α)] {J : Finset (Set α)}


/- In a `hC : IsSetSemiring C`, for a `J : Finset (Set α)` with `J ⊆ C`, there is for every `x in J` some `K x ⊆ C` finite, such that
    * `⋃ x ∈ J, K x` are pairwise disjoint,
    * `⋃ s ∈ K x, s ⊆ x`,
    * `⋃ x ∈ J, x = ⋃ x ∈ J, ⋃ s ∈ K x, s`.
-/
set_option trace.split.failure true

lemma sUnion_diffFinset₀_subsets (hC : IsSetSemiring C) {I : Finset (Set α)} (hs : s ∈ C) (hI : ↑I ⊆ C) :
    ∀ t ∈ (hC.diffFinset₀ hs hI : Set (Set α)), t ⊆ s := by
  rw [← sUnion_subset_iff]
  exact hC.sUnion_diffFinset₀_subset hs hI

theorem allDiffFinset₀_props (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) : ∃ (K : Set α → Finset (Set α)) (hK : (J.toSet).PairwiseDisjoint K), ((disjiUnion J K hK).toSet ⊆ C) ∧
    (PairwiseDisjoint (disjiUnion J K hK).toSet id) ∧ (∀ j ∈ J, ⋃₀ K j ⊆ j ) ∧
    ((⋃₀ J.toSet) = ⋃₀ (disjiUnion J K hK).toSet) := by
  revert hJ
  apply @Finset.cons_induction (Set α) (fun (J : Finset (Set α)) => (↑J ⊆ C) → ∃ (K : Set α → Finset (Set α)) (hK : (J.toSet).PairwiseDisjoint K), ((disjiUnion J K hK).toSet ⊆ C) ∧
    (PairwiseDisjoint (disjiUnion J K hK).toSet id) ∧ (∀ j ∈ J, ⋃₀ K j ⊆ j ) ∧
    ((⋃₀ J.toSet) = ⋃₀ (disjiUnion J K hK).toSet)) _ _ J
  · simp only [coe_empty, Set.empty_subset, disjiUnion_eq_biUnion, Finset.biUnion_empty,
    pairwiseDisjoint_empty, Finset.not_mem_empty, sUnion_subset_iff, mem_coe, IsEmpty.forall_iff,
    implies_true, sUnion_empty, and_self, exists_const, imp_self]
  · intro s J hJ hind h1
    rw [cons_eq_insert, coe_insert, Set.insert_subset_iff] at h1
    obtain ⟨K, hK0, ⟨hK1, hK2, hK3, hK4⟩⟩ := hind h1.2
    clear hind
    rw [disjiUnion_eq_biUnion] at hK1 hK2 hK4
    simp only [coe_biUnion, mem_coe, iUnion_subset_iff] at hK1 hK2 hK4
    let K' := hC.diffFinset₀ h1.1 h1.2
    let K1 := fun (t : Set α) => ite (t = s) K' (K t)
    use K1
    simp only [cons_eq_insert, disjiUnion_eq_biUnion, Finset.biUnion_insert, coe_union, coe_biUnion,
      mem_coe, Set.union_subset_iff, iUnion_subset_iff, Finset.mem_insert, sUnion_subset_iff,
      forall_eq_or_imp, coe_insert, sUnion_insert, exists_and_left, exists_prop]
    -- two simplification rules for induction hypothesis
    have ht1 : ∀ x ∈ J, ((if x = s then K'.toSet else (K x).toSet) = (K x).toSet) := by
      simp only [beq_iff_eq, ite_eq_right_iff]
      exact fun x hx g => False.elim (hJ (g ▸ hx))
    have ht2 : (⋃ x ∈ J, if x = s then K'.toSet else (K x).toSet) = ⋃ x ∈ J, (K x).toSet := by
      apply iUnion₂_congr
      intros x hx
      exact if_neg (ne_of_mem_of_not_mem hx hJ)
    have ht3 : (fun t => if t = s then hC.diffFinset₀ h1.1 h1.2 else K t) = K := by sorry
    simp only [↓reduceIte, K1, K']
    refine ⟨⟨?_,?_⟩, ?_, ?_, ?_, ?_⟩
    · refine hC.diffFinset₀_subset h1.1 h1.2
    · intros i hi
      split
      · exact hC.diffFinset₀_subset h1.1 h1.2
      · exact hK1 i hi
    · refine pairwiseDisjoint_union.mpr ?_
      refine ⟨?_, ?_, ?_⟩
      · exact hC.pairwiseDisjoint_diffFinset₀ h1.1 h1.2
      · simp_rw [apply_ite]
        rw [ht2]
        exact hK2
      · simp only [↓reduceIte, mem_coe, mem_iUnion, exists_prop, ne_eq, id_eq, forall_exists_index,
        and_imp, K1]
        intros i hi j x hx h3 h4
        simp [K'] at ht1

        -- We show i ⊆ s \ ⋃₀ J
        have ki : i ⊆ s \ ⋃₀ J :=
          by
          rw [hC.diff_sUnion_eq_sUnion_diffFinset₀ h1.1 h1.2]
          exact
            subset_sUnion_of_subset (↑(hC.diffFinset₀ h1.1 h1.2)) i (fun ⦃a⦄ a => a) hi
        -- We show j ∈ K x ⊆ x ∈ J
        have hx2 : j ⊆ x := by
          sorry -- apply le_trans (by rfl) (hK3 x hx j h3)
        have kj : j ⊆ ⋃₀ J := by
          apply le_trans hx2
          exact subset_sUnion_of_subset (↑J) x (fun ⦃a⦄ a => a) hx

        apply disjoint_of_subset ki kj
        exact disjoint_sdiff_left

    · constructor
      · exact hC.sUnion_diffFinset₀_subsets h1.1 h1.2
      · intros a ha
        rw [if_neg (ne_of_mem_of_not_mem ha hJ)]
        change ∀ t' ∈ (K a).toSet, t' ⊆ a
        rw [← sUnion_subset_iff]
        exact hK3 a ha
    · apply Set.Pairwise.insert
      ·
        sorry
      · sorry
    · simp only [↓reduceIte, K1, ht2, sUnion_union, apply_ite]
      rw [← hC.diff_sUnion_eq_sUnion_diffFinset₀ h1.1 h1.2]
      sorry
      -- simp only [diff_union_self, K1]

example (s : Set α) (J : Finset (Set α)) : (∀ t ∈ J, t ⊆ s) ↔ ⋃₀ J ⊆ s := by
  exact Iff.symm sUnion_subset_iff

noncomputable def allDiffFinset₀' (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) :=
  (hC.allDiffFinset₀_props hJ).choose

lemma props_allDiffFinset₀ (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) :
    ((J.biUnion (hC.allDiffFinset₀' hJ)).toSet ⊆ C) ∧
    (PairwiseDisjoint (J.biUnion (allDiffFinset₀' hC hJ)).toSet id) ∧
    (∀ j ∈ J, ⋃₀ (hC.allDiffFinset₀' hJ) j ⊆ j ) ∧
    ((⋃₀ J.toSet) = ⋃₀ (J.biUnion (allDiffFinset₀' hC hJ)).toSet) := by
  simp_rw [allDiffFinset₀']
  apply Exists.choose_spec (hC.allDiffFinset₀_props hJ)


lemma allDiffFinset₀'_subset_semiring (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) :
    (J.biUnion (allDiffFinset₀' hC hJ)).toSet ⊆ C :=
    (hC.props_allDiffFinset₀ hJ).1

lemma biUnion_subset_iff {J : Finset (Set α)} {t : Set α} :
  ⋃₀ J ⊆ t ↔ ∀ x ∈ J, x ⊆ t := by
  exact sUnion_subset_iff

lemma allDiffFinset₀'_subsets_semiring (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) : ∀ j ∈ J,
    (allDiffFinset₀' hC hJ j).toSet ⊆ C := by
  intros j hj s hs
  apply hC.allDiffFinset₀'_subset_semiring hJ
  simp only [coe_biUnion, mem_coe, mem_iUnion, exists_prop]
  use j
  exact ⟨hj, hs⟩

lemma allDiffFinset₀'_pairwiseDisjoint (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) :
    (PairwiseDisjoint (J.biUnion (hC.allDiffFinset₀' hJ)).toSet id) := (hC.props_allDiffFinset₀ hJ).2.1

lemma allDiffFinset₀'_pairwiseDisjoints (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) : ∀ j ∈ J,
    (PairwiseDisjoint (hC.allDiffFinset₀' hJ j).toSet id) := by
  intro j hj
  apply PairwiseDisjoint.subset (hC.allDiffFinset₀'_pairwiseDisjoint hJ)
  simp only [coe_biUnion, mem_coe]
  apply subset_iUnion₂_of_subset j hj (by rfl)

example (s : Set (Set α)) (hs : s.PairwiseDisjoint id) (x y : Set α) (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) : Disjoint x y := by
  exact hs hx hy hxy

lemma l1 {J : Finset (Set α)} {K : Set α → Finset (Set α)} {x : Set α} {j : Set α} (hK : (J.toSet).PairwiseDisjoint K) (hj : j ∈ J) (hx : x ∈ K j) : x ∈ (disjiUnion J K hK).toSet := by
  simp only [disjiUnion_eq_biUnion, coe_biUnion, mem_coe, mem_iUnion, exists_prop]
  use j

example (J : Finset (Set α)) (K : Set α → Finset (Set α)) (hK : (J.toSet).PairwiseDisjoint K) (hs : PairwiseDisjoint (disjiUnion J K hK).toSet id) (x y : Set α) (hx : x ∈ (disjiUnion J K hK).toSet) (hy : y ∈ (disjiUnion J K hK).toSet) (hxy : x ≠ y) : Disjoint x y := by
  exact hs hx hy hxy

example (J : Finset (Set α)) (K : Set α → Finset (Set α)) (hK : PairwiseDisjoint J.toSet K) (hs : PairwiseDisjoint (disjiUnion J K hK).toSet id) (x y : Set α) (i j : Set α) (hi : i ∈ J.toSet) (hj : j ∈ J.toSet) (hij : i ≠ j) (hx : x ∈ K i) (hy : y ∈ K j) : Disjoint x y := by
  apply hs (l1 hK hi hx) (l1 hK hj hy)
  intro h
  apply hij
  rw [h] at hx
  exact PairwiseDisjoint.elim_finset hK hi hj y hx hy


lemma allDiffFinset₀'_pairwiseDisjoint' (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) : (J.toSet).PairwiseDisjoint (hC.allDiffFinset₀' hJ) := by
  intro i hi j hj hij
  refine Finset.disjoint_iff_inter_eq_empty.mpr ?_
  rw [← coe_inj, coe_inter, coe_empty]
  apply disjoint_iff_inter_eq_empty.mp
  simp only [disjoint_coe]
  have h1 : ∀ k ∈ J, hC.allDiffFinset₀' hJ k ⊆ (J.biUnion (hC.allDiffFinset₀' hJ)) := by
    exact fun k a => Finset.subset_biUnion_of_mem (hC.allDiffFinset₀' hJ) a
  -- exact
  sorry

  have h : ∀ i ∈ J, ∀ x ∈ (hC.allDiffFinset₀' hJ i), x ∈  (J.biUnion (hC.allDiffFinset₀' hJ)) := by sorry
  obtain h1 := fun x hx1 hx2 => (hC.allDiffFinset₀'_pairwiseDisjoint hJ) (h i x hx1 hx2)



  sorry

lemma allDiffFinset₀'_subset (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) :
    ∀ j ∈ J, ⋃₀ (hC.allDiffFinset₀' hJ) j ⊆ j
    := (hC.props_allDiffFinset₀ hJ).2.2.1


lemma allDiffFinset₀'_subsets (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) :
    ∀ j ∈ J, ∀ x ∈ (hC.allDiffFinset₀' hJ) j, x ⊆ j := by
  intro j hj
  rw [← biUnion_subset_iff]
  exact hC.allDiffFinset₀'_subset hJ j hj

lemma allDiffFinset₀'_sUnion (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) :
    ⋃₀ (J.biUnion (hC.allDiffFinset₀' hJ)).toSet = ⋃₀ J.toSet :=
    (hC.props_allDiffFinset₀ hJ).2.2.2.symm

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
#min_imports
