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

-- Goes in SetSemiring.lean

variable {α : Type*} {C : Set (Set α)} {s t : Set α}
    {J : Finset (Set α)}

lemma sUnion_diffFinset₀_subsets (hC : IsSetSemiring C) {I : Finset (Set α)} (hs : s ∈ C) (hI : ↑I ⊆ C) :
    ∀ t ∈ (hC.diffFinset₀ hs hI : Set (Set α)), t ⊆ s \ ⋃₀ I := by
  rw [← sUnion_subset_iff, hC.diff_sUnion_eq_sUnion_diffFinset₀ hs hI]

lemma sUnion_diffFinset₀_subsets' (hC : IsSetSemiring C) {I : Finset (Set α)} (hs : s ∈ C) (hI : ↑I ⊆ C) :
    ∀ t ∈ (hC.diffFinset₀ hs hI : Set (Set α)), t ⊆ s := by
  rw [← sUnion_subset_iff]
  exact hC.sUnion_diffFinset₀_subset hs hI

end IsSetSemiring

end MeasureTheory






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

-- goes to Mathlib.Order.Disjoint

@[simp]
lemma not_disjoint_self [PartialOrder α] [OrderBot α] {x : α} : ¬ (Disjoint x x) ↔ (x ≠ ⊥) := not_iff_not.mpr disjoint_self

lemma disjointSets_of_disjoint [PartialOrder α] [OrderBot α] {a b : α} {J K : Set α} (ha : ∀ c ∈ J, c ≤ a) (hb : ∀ d ∈ K, d ≤ b) (hJK : ⊥ ∉ J ∨ ⊥ ∉ K) (hcd : Disjoint a b) : Disjoint J K := by
  rw [disjoint_iff_forall_ne]
  intros x hx y hy hxy
  obtain h1 : Disjoint x y := by
    exact Disjoint.mono (ha x hx) (hb y hy) hcd
  revert h1
  cases' hJK with hJ hK
  · rw [← hxy]
    exact not_disjoint_self.mpr (ne_of_mem_of_not_mem hx hJ)
  · rw [hxy]
    exact not_disjoint_self.mpr (ne_of_mem_of_not_mem hy hK)


variable [DecidableEq (Set α)]


theorem allDiffFinset₀_props (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) : ∃ (K : Set α → Finset (Set α)), ∃
    (hK : (J.toSet).PairwiseDisjoint K), ((disjiUnion J K hK).toSet ⊆ C) ∧
    (PairwiseDisjoint (disjiUnion J K hK).toSet id) ∧ (∀ j ∈ J, ⋃₀ K j ⊆ j ) ∧
    ( ∀ j ∈ J, ∅ ∉ K j ) ∧ ((⋃₀ J.toSet) = ⋃₀ (disjiUnion J K hK).toSet) := by
  revert hJ
  apply @Finset.cons_induction (Set α) (fun (J : Finset (Set α)) => (↑J ⊆ C) →
  ∃ (K : Set α → Finset (Set α)) (hK : (J.toSet).PairwiseDisjoint K),
  ((disjiUnion J K hK).toSet ⊆ C) ∧ (PairwiseDisjoint (disjiUnion J K hK).toSet id) ∧
  (∀ j ∈ J, ⋃₀ K j ⊆ j ) ∧ ( ∀ j ∈ J, ∅ ∉ K j ) ∧
  ((⋃₀ J.toSet) = ⋃₀ (disjiUnion J K hK).toSet)) _ _ J
  · simp only [coe_empty, Set.empty_subset, disjiUnion_eq_biUnion, Finset.biUnion_empty,
    pairwiseDisjoint_empty, Finset.not_mem_empty, sUnion_subset_iff, mem_coe, IsEmpty.forall_iff,
    implies_true, sUnion_empty, and_self, exists_const, imp_self]
  · intro s J hJ hind h1
    rw [cons_eq_insert, coe_insert, Set.insert_subset_iff] at h1
    obtain ⟨K, hK0, ⟨hK1, hK2, hK3, hK4, hK5⟩⟩ := hind h1.2
    clear hind
    rw [disjiUnion_eq_biUnion] at hK1 hK2 hK5
    simp only [coe_biUnion, mem_coe, iUnion_subset_iff] at hK1 hK2 hK5
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
    have ht1' : ∀ x ∈ J, ((if x = s then K' else (K x)) = (K x)) := by
      simp only [beq_iff_eq, ite_eq_right_iff]
      exact fun x hx g => False.elim (hJ (g ▸ hx))
    have ht2 : (⋃ x ∈ J, if x = s then K'.toSet else (K x).toSet) = ⋃ x ∈ J, (K x).toSet := by
      apply iUnion₂_congr
      intros x hx
      exact if_neg (ne_of_mem_of_not_mem hx hJ)
    simp only [↓reduceIte, K1]
    refine ⟨⟨?_,?_⟩, ?_, ?_, ?_, ?_, ?_⟩
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
          apply hC.sUnion_diffFinset₀_subsets h1.1 h1.2
          simp
          exact hi
        -- We show j ⊆ ⋃₀ K x ⊆ x ∈ J
        have hx2 : j ⊆ x := by
          rw [ht1' x hx] at h3
          apply le_trans (?_) (hK3 x hx)
          exact subset_sUnion_of_subset (↑(K x)) j (fun ⦃a⦄ a => a) h3
        have kj : j ⊆ ⋃₀ J := by
          apply le_trans hx2
          exact subset_sUnion_of_subset (↑J) x (fun ⦃a⦄ a => a) hx

        apply disjoint_of_subset ki kj
        exact disjoint_sdiff_left

    · constructor
      · apply hC.sUnion_diffFinset₀_subsets' h1.1 h1.2
      · intros a ha
        rw [if_neg (ne_of_mem_of_not_mem ha hJ)]
        change ∀ t' ∈ (K a).toSet, t' ⊆ a
        rw [← sUnion_subset_iff]
        exact hK3 a ha
    · refine ⟨hC.empty_not_mem_diffFinset₀ h1.1 h1.2, ?_⟩
      intros a ha
      rw [ht1' a ha]
      exact hK4 a ha
    · apply Set.Pairwise.insert
      · intro j hj i hi hij
        rw [Function.onFun, ht1' j hj, ht1' i hi]
        exact hK0 hj hi hij
      · intro i hi hsi
        have h7 : Disjoint K'.toSet (K i).toSet := by
          refine disjointSets_of_disjoint (hC.sUnion_diffFinset₀_subsets h1.1 h1.2) ?_ (Or.inl (hC.empty_not_mem_diffFinset₀ h1.1 h1.2)) (@disjoint_sdiff_left (α) (⋃₀ J) s)
          simp only [mem_coe, Set.le_eq_subset, K', K1]
          apply sUnion_subset_iff.mp
          apply le_trans (hK3 i hi)
          apply subset_sUnion_of_subset J i (by rfl) hi
        have h8 : Function.onFun Disjoint (fun t => if t = s then K' else K t) s i := by
          refine Finset.disjoint_iff_inter_eq_empty.mpr ?_
          have h4 : (fun t => if t = s then K' else K t) i = K i := by
            exact ht1' i hi
          rw [h4]
          simp only [↓reduceIte, ite_cond_eq_false hsi.symm, K', K1]
          rw [disjoint_iff_inter_eq_empty] at h7
          simp [K'] at h7
          rw [← coe_inter, coe_eq_empty] at h7
          exact h7
        refine ⟨h8, Disjoint.symm h8⟩
    · simp only [↓reduceIte, K1, ht2, sUnion_union, apply_ite]
      rw [← hC.diff_sUnion_eq_sUnion_diffFinset₀ h1.1 h1.2, ← hK5]
      simp only [diff_union_self, K1]


lemma l : ∃ (m : ℕ) (f : ℕ → ℕ), m < f m := by
  use 2
  use fun n => n+1
  linarith

noncomputable def a := l.choose
noncomputable def b := (Exists.choose_spec l).choose

#check b

lemma l1 : a < b a := by
  rw [a,b]
  refine (Exists.choose_spec l).choose_spec


noncomputable def allDiffFinset₀' (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) := (hC.allDiffFinset₀_props hJ).choose

lemma allDiffFinset₀_disjoint (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) : ((J.toSet).PairwiseDisjoint (hC.allDiffFinset₀' hJ)) := by
  exact (Exists.choose_spec (hC.allDiffFinset₀_props hJ)).choose

lemma allDiffFinset₀'_subset_semiring (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) :
    (disjiUnion J (hC.allDiffFinset₀' hJ) (hC.allDiffFinset₀_disjoint hJ)).toSet ⊆ C := by
  exact (Exists.choose_spec (hC.allDiffFinset₀_props hJ)).choose_spec.1

lemma allDiffFinset₀'_subsets_semiring (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) : ∀ j ∈ J,
    (allDiffFinset₀' hC hJ j).toSet ⊆ C := by
  intros j hj s hs
  apply hC.allDiffFinset₀'_subset_semiring hJ
  simp only [disjiUnion_eq_biUnion, coe_biUnion, mem_coe, mem_iUnion, exists_prop]
  use j
  exact ⟨hj, hs⟩

lemma allDiffFinset₀'_pairwiseDisjoint (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) :
    (PairwiseDisjoint (disjiUnion J (hC.allDiffFinset₀' hJ) (hC.allDiffFinset₀_disjoint hJ)).toSet id) := by
  exact (Exists.choose_spec (hC.allDiffFinset₀_props hJ)).choose_spec.2.1

lemma allDiffFinset₀'_pairwiseDisjoints (hC : IsSetSemiring C) (hJ : ↑J ⊆ C) : ∀ j ∈ J,
    (PairwiseDisjoint (hC.allDiffFinset₀' hJ j).toSet id) := by
  intro j hj
  apply PairwiseDisjoint.subset (hC.allDiffFinset₀'_pairwiseDisjoint hJ)
  simp only [disjiUnion_eq_biUnion, coe_biUnion, mem_coe]
  apply subset_iUnion₂_of_subset j hj (by rfl)






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
