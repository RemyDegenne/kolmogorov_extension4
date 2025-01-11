/-
Copyright (c) 2025 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
import KolmogorovExtension4.AuxLemmas
import Mathlib.MeasureTheory.SetSemiring

/-
  ## Main results

  * `allDiffFinset₀_props`: In a semiring, write a union of elements of the semiring as a disjoint union of elements of the semiring.
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
theorem allDiffFinset₀_props (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) : ∃ K : Set α → Finset (Set α), ((J.biUnion K).toSet ⊆ C) ∧
    (PairwiseDisjoint (J.biUnion K).toSet id) ∧ (∀ j ∈ J, ⋃₀ K j ⊆ j ) ∧
    ((⋃₀ J.toSet) = ⋃₀ (J.biUnion K).toSet) := by
  revert hJ
  apply @Finset.cons_induction (Set α) (fun (J : Finset (Set α)) => (↑J ⊆ C) → (∃ K : Set α → Finset (Set α), (↑ (J.biUnion K) ⊆ C) ∧ (PairwiseDisjoint (J.biUnion K : Set (Set α)) id)  ∧ (∀ j ∈ J, ⋃₀ K j ⊆ j ) ∧ (⋃₀ J = ⋃₀ (J.biUnion K : Set (Set α))))) _ _ J
  · simp only [coe_empty, Set.empty_subset, Finset.biUnion_empty, pairwiseDisjoint_empty,
    Finset.not_mem_empty, sUnion_subset_iff, mem_coe, IsEmpty.forall_iff, implies_true,
    sUnion_empty, and_self, exists_const, imp_self]
  · intro s J hJ hind h1
    rw [cons_eq_insert, coe_insert, Set.insert_subset_iff] at h1
    obtain ⟨K, ⟨hK1, hK2, hK3, hK4⟩⟩ := hind h1.2
    clear hind
    let K' := hC.diffFinset₀ h1.1 h1.2
    let K1 := fun (t : Set α) => ite (t = s) K' (K t)
    use K1
    simp only [coe_biUnion, mem_coe, iUnion_subset_iff, sUnion_subset_iff, cons_eq_insert,
      Finset.biUnion_insert, coe_union, Set.union_subset_iff, Finset.mem_insert, forall_eq_or_imp,
      coe_insert, sUnion_insert, K1, apply_ite] at *
    -- two simplification rules for induction hypothesis
    have ht1 : ∀ x ∈ J, ((if x = s then K'.toSet else (K x).toSet) = (K x).toSet) := by
      simp only [beq_iff_eq, ite_eq_right_iff]
      exact fun x hx g => False.elim (hJ (g ▸ hx))
    have ht2 : (⋃ x ∈ J, if x = s then K'.toSet else (K x).toSet) = ⋃ x ∈ J, (K x).toSet := by
      apply iUnion₂_congr
      intros x hx
      exact if_neg (ne_of_mem_of_not_mem hx hJ)

    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [↓reduceIte, K1, apply_ite]
      refine ⟨hC.diffFinset₀_subset h1.1 h1.2, ?_⟩
      intros i hi
      split
      · exact hC.diffFinset₀_subset h1.1 h1.2
      · exact hK1 i hi
    · refine pairwiseDisjoint_union.mpr ?_
      refine ⟨?_, ?_, ?_⟩
      · exact hC.pairwiseDisjoint_diffFinset₀ h1.1 h1.2
      · rw [ht2]
        exact hK2
      · simp only [↓reduceIte, mem_coe, mem_iUnion, exists_prop, ne_eq, id_eq, forall_exists_index,
        and_imp, K1]
        intros i hi j x hx h3 h4
        rw [ht1 x hx]  at h3
        -- We show i ⊆ s \ ⋃₀ J
        have ki : i ⊆ s \ ⋃₀ J :=
          by
          rw [hC.diff_sUnion_eq_sUnion_diffFinset₀ h1.1 h1.2]
          exact
            subset_sUnion_of_subset (↑(hC.diffFinset₀ h1.1 h1.2)) i (fun ⦃a⦄ a => a) hi
        -- We show j ∈ K x ⊆ x ∈ J
        have hx2 : j ⊆ x := by
          apply le_trans (by rfl) (hK3 x hx j h3)
        have kj : j ⊆ ⋃₀ J := by
          apply le_trans hx2
          exact subset_sUnion_of_subset (↑J) x (fun ⦃a⦄ a => a) hx

        apply disjoint_of_subset ki kj
        exact disjoint_sdiff_left

    · simp only [↓reduceIte, mem_coe, K1, K']
      constructor
      · exact hC.sUnion_diffFinset₀_subset h1.1 h1.2
      · intros a ha
        rw [if_neg (ne_of_mem_of_not_mem ha hJ), sUnion_subset_iff]
        exact hK3 a ha
    · simp only [↓reduceIte, K1, ht2, sUnion_union]
      rw [← hC.diff_sUnion_eq_sUnion_diffFinset₀ h1.1 h1.2, ← hK4]
      simp only [diff_union_self, K1]

noncomputable def allDiffFinset₀ (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) :=
  (hC.allDiffFinset₀_props hJ).choose

lemma props_allDiffFinset₀ (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) :
    ((J.biUnion (hC.allDiffFinset₀ hJ)).toSet ⊆ C) ∧
    (PairwiseDisjoint (J.biUnion (allDiffFinset₀ hC hJ)).toSet id) ∧
    (∀ j ∈ J, ⋃₀ (hC.allDiffFinset₀ hJ) j ⊆ j ) ∧
    ((⋃₀ J.toSet) = ⋃₀ (J.biUnion (allDiffFinset₀ hC hJ)).toSet) := by
  simp_rw [allDiffFinset₀]
  apply Exists.choose_spec (hC.allDiffFinset₀_props hJ)


lemma allDiffFinset₀_subset_semiring (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) :
    (J.biUnion (allDiffFinset₀ hC hJ)).toSet ⊆ C :=
    (hC.props_allDiffFinset₀ hJ).1

lemma allDiffFinset₀_pairwiseDisjoint (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) :
    (PairwiseDisjoint (J.biUnion (hC.allDiffFinset₀ hJ)).toSet id) := (hC.props_allDiffFinset₀ hJ).2.1

lemma allDiffFinset₀_subset (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) :
    ∀ j ∈ J, ⋃₀ (hC.allDiffFinset₀ hJ) j ⊆ j
    := (hC.props_allDiffFinset₀ hJ).2.2.1

lemma allDiffFinset₀_sUnion (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) :
    ⋃₀ (J.biUnion (hC.allDiffFinset₀ hJ)).toSet = ⋃₀ J.toSet :=
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
