import KolmogorovExtension4.AdditiveOfContinuous
import KolmogorovExtension4.CaratheodoryExtension
import KolmogorovExtension4.Projective
import KolmogorovExtension4.RegularityCompacts
import Mathlib.MeasureTheory.Constructions.Polish

open Set

open scoped ENNReal BigOperators

namespace MeasureTheory

def halfOpenIntervals : Set (Set ℝ) :=
  ⋃ (a : ℝ) (b : ℝ), {(Ioc a b)}

lemma is_empty_of_halfOpenInterval_le {a b : ℝ} (hab : b ≤ a) : Ioc a b = ∅ := by
  ext x
  simp only [gt_iff_lt, not_lt, ge_iff_le, mem_Ioc, mem_empty_iff_false, iff_false, not_and, not_le]
  intro h
  linarith

lemma emptyset_is_halfOpenInterval : ∅ ∈ halfOpenIntervals := by
  rw [halfOpenIntervals]
  simp only [gt_iff_lt, not_lt, ge_iff_le, iUnion_singleton_eq_range, mem_iUnion, mem_range]
  refine ⟨0, 0, is_empty_of_halfOpenInterval_le (by rfl)⟩

lemma halfOpenIntervals_mem {a b : ℝ} : Ioc a b ∈ halfOpenIntervals := by
  rw [halfOpenIntervals]
  simp only [gt_iff_lt, not_lt, ge_iff_le, iUnion_singleton_eq_range, mem_iUnion, mem_range]
  refine ⟨a, b, by rfl⟩ 

theorem IsPiSystem.halfOpenIntervals :  ∀ (s : Set ℝ), s ∈ halfOpenIntervals → ∀ (t : Set ℝ), t ∈ halfOpenIntervals → s ∩ t ∈ halfOpenIntervals := by
  intros s hs t ht
  rw [halfOpenIntervals, mem_iUnion₂] at *
  rcases hs with ⟨a, b, hs⟩ 
  rcases ht with ⟨c, d, ht⟩ 
  simp only [gt_iff_lt, not_lt, ge_iff_le, mem_singleton_iff] at hs ht 
  refine ⟨max a c, min b d, ?_⟩ 
  rw [hs, ht]
  simp only [gt_iff_lt, not_lt, ge_iff_le, lt_min_iff, max_lt_iff, not_and, and_imp, le_max_iff, min_le_iff,
    mem_singleton_iff]
  ext x
  simp only [gt_iff_lt, not_lt, ge_iff_le, mem_inter_iff, mem_Ioc, lt_min_iff, max_lt_iff, not_and, and_imp, le_max_iff,
    min_le_iff, le_min_iff]
  tauto

lemma some {A B C : Set ℝ} (hA : C ⊆ A) (hB : C ⊆ B) (hAB : A ∩ B = ∅) : C ⊆ ∅ := by
  intros x hx
  rw [← hAB, mem_inter_iff]
  exact ⟨hA hx, hB hx⟩ 


theorem diff_eq_Union_halfOpenIntervals : ∀ (s) (_ : s ∈ halfOpenIntervals) (t) (_ : t ∈ halfOpenIntervals), ∃ (I : Finset (Set ℝ)) (_h_ss : ↑I ⊆ halfOpenIntervals) (_h_dis : PairwiseDisjoint (I : Set (Set ℝ)) id),
        t \ s = ⋃₀ I := by
  classical 
  intros s hs t ht
  rw [halfOpenIntervals, mem_iUnion₂] at *
  rcases hs with ⟨a, b, hs⟩ 
  rcases ht with ⟨c, d, ht⟩ 
  simp only [gt_iff_lt, not_lt, ge_iff_le, mem_singleton_iff] at hs ht
  by_cases hab : b ≤ a
  · obtain h : s = ∅ := by
      rw [hs]
      exact Ioc_eq_empty_of_le hab
    let I := [Ioc c d].toFinset
    use I
    have h_ss : (I : Set (Set ℝ)) ⊆ halfOpenIntervals := by
      simp only [List.toFinset_cons, gt_iff_lt, not_lt, ge_iff_le, List.toFinset_nil, insert_emptyc_eq,
          Finset.coe_singleton, singleton_subset_iff]
      rw [halfOpenIntervals]
      simp only [gt_iff_lt, not_lt, ge_iff_le, iUnion_singleton_eq_range, mem_iUnion, mem_range]        
      use c
      use d
    use h_ss
    have h_dis : PairwiseDisjoint (I : Set (Set ℝ)) id := by
      simp only [List.toFinset_cons, gt_iff_lt, not_lt, ge_iff_le, List.toFinset_nil, insert_emptyc_eq,
        Finset.coe_singleton, pairwiseDisjoint_singleton]
    use h_dis
    rw [h, ht]
    simp only [gt_iff_lt, not_lt, ge_iff_le, diff_empty, List.toFinset_cons, List.toFinset_nil, insert_emptyc_eq,
      Finset.coe_singleton, sUnion_singleton]
  · push_neg at hab
    let I := [Ioc c (min a d), Ioc (max b c) d].toFinset
    have h_ss : (I : Set (Set ℝ)) ⊆ halfOpenIntervals := by
      simp
      intros A hA
      cases' hA with hA1 hA2
      rw [hA1]
      apply halfOpenIntervals_mem
      rw [hA2]
      apply halfOpenIntervals_mem
    have h_dis : PairwiseDisjoint (I : Set (Set ℝ)) id := by
      rw [PairwiseDisjoint, Set.Pairwise]
      intros A hA B hB hnot
      intros C hCA hCB
      simp only [hCA, hCB, id_eq, le_eq_subset, bot_eq_empty] at *
      apply some hCA hCB
      simp only [ge_iff_le, gt_iff_lt, lt_min_iff, not_and, not_lt, min_le_iff, max_lt_iff, le_max_iff,
        List.toFinset_cons, List.toFinset_nil, insert_emptyc_eq, Finset.mem_singleton, Finset.coe_insert,
        Finset.coe_singleton, mem_singleton_iff, mem_insert_iff] at hA hB
      cases' hA with hA1 hA2
      · have hB' : B = Ioc (max b c) d := by 
          cases' hB with hB1 hB2
          · exfalso
            apply hnot
            rw [hA1, hB1]
          · exact hB2
        rw [hA1, hB']
        ext x
        simp only [ge_iff_le, gt_iff_lt, lt_min_iff, not_and, not_lt, min_le_iff, max_lt_iff, le_max_iff, mem_inter_iff,
          mem_Ioc, le_min_iff, mem_empty_iff_false, iff_false, not_le, and_imp]
        intros _ h2 _ h4 _
        linarith
      · have hB' : B = Ioc c (min a d) := by
          cases' hB with hB1 hB2
          · exact hB1
          · exfalso
            apply hnot
            rw [hA2, hB2]
        rw [hA2, hB']
        ext x
        simp only [ge_iff_le, gt_iff_lt, max_lt_iff, not_and, not_lt, le_max_iff, lt_min_iff, min_le_iff, mem_inter_iff,
          mem_Ioc, le_min_iff, mem_empty_iff_false, iff_false, not_le, and_imp]
        intros h1 _ _ _  h5
        linarith
    use I
    use h_ss
    use h_dis
    rw [hs, ht]
    ext x
    simp only [gt_iff_lt, not_lt, ge_iff_le, mem_diff, mem_Ioc, not_and, not_le, List.toFinset_cons, lt_min_iff,
      min_le_iff, max_lt_iff, le_max_iff, List.toFinset_nil, insert_emptyc_eq, Finset.mem_singleton, Finset.coe_insert,
      Finset.coe_singleton, mem_singleton_iff, sUnion_insert, sUnion_singleton, mem_union, le_min_iff]
    refine ⟨fun ⟨⟨h1,h2⟩,h3⟩ => ?_, fun h => ?_⟩
    simp only [h1, h2, and_true, true_and]
    by_cases a < x
    · right
      exact h3 h
    · push_neg at h
      left
      exact h
    rcases h with (⟨h1, ⟨h2, h3⟩⟩ | ⟨⟨h1, h2⟩, h3⟩ ) 
    simp only [h1, h2, h3, and_true, true_and]
    intro h
    linarith
    simp only [h2, h3, and_self, h1, implies_true]

theorem setSemiring_halfOpenIntervals : SetSemiring halfOpenIntervals :=
  { empty_mem := emptyset_is_halfOpenInterval
    inter_mem := IsPiSystem.halfOpenIntervals
    diff_eq_Union' := diff_eq_Union_halfOpenIntervals}

