/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
module

public import KolmogorovExtension4.CompactSystem
public import Mathlib.MeasureTheory.Measure.AddContent

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} {C R : Set (Set α)} {s : ℕ → Set α}

-- `innerRegular` is defined only for a measure, hence we expand the definition to use it with a
-- content
lemma tendsto_zero_of_regular_addContent (hR : IsSetRing R) (m : AddContent ℝ≥0∞ R)
    (hs : ∀ n, s n ∈ R) (hs_anti : Antitone s) (hs_Inter : (⋂ n, s n) = ∅)
    (hC : IsCompactSystem C) (hCR : C ⊆ R)
    (h_reg : ∀ A (_ : A ∈ R) (ε : ℝ≥0∞) (_ : 0 < ε), ∃ K ∈ C, K ⊆ A ∧ m (A \ K) ≤ ε) :
    Filter.Tendsto (fun n ↦ m (s n)) Filter.atTop (nhds 0) := by
  rcases isEmpty_or_nonempty α with hα | hα
  · simp [Set.eq_empty_of_isEmpty]
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ_sum⟩ := ENNReal.exists_pos_sum_of_countable hε.ne' ℕ
  have h_reg' : ∀ n, ∃ K ∈ C, K ⊆ s n ∧ m (s n \ K) ≤ δ n :=
    fun n ↦ h_reg (s n) (hs n) (δ n) (mod_cast (hδ_pos n))
  choose t ht_mem_C ht_subset ht using h_reg'
  rw [Filter.eventually_atTop]
  have ht_empty : ⋂ n, t n = ∅ := Set.subset_eq_empty (Set.iInter_mono ht_subset) hs_Inter
  let S := hC.support ht_mem_C ht_empty
  have hS := hC.iInter_eq_empty ht_mem_C ht_empty
  have hS_nonempty : Finset.Nonempty (Finset.Iic S) := by simp
  let N := Finset.max' (Finset.Iic S) hS_nonempty
  have ht_empty' : ∀ n, N ≤ n → ⋂ i ≤ n, t i = ∅ := by
    intro n hn
    refine Set.subset_eq_empty ?_ hS
    simp only [Set.subset_iInter_iff]
    intro i hi
    refine Set.biInter_subset_of_mem ?_
    exact (Finset.le_max' (Finset.Iic S) i (by simpa using hi)).trans hn
  refine ⟨N, fun n hn ↦ ?_⟩
  calc m (s n) = m (⋂ i ≤ n, s i) := by
        congr
        exact le_antisymm (le_iInf₂ fun i hi ↦ hs_anti hi)
          (iInf₂_le (κ := fun i ↦ i ≤ n) (f := fun i _ ↦ s i) n le_rfl)
    _ = m ((⋂ i ≤ n, s i) \ (⋂ i ≤ n, t i)) := by simp only [ht_empty' n hn, Set.diff_empty]
    _ ≤ m (⋃ i ≤ n, (s i \ t i)) := by
        refine addContent_mono hR.isSetSemiring ?_ ?_ ?_
        · exact hR.diff_mem (hR.iInter_le_mem hs n) (hR.iInter_le_mem (fun i ↦ hCR (ht_mem_C i)) n)
        · exact hR.iUnion_le_mem (fun i ↦ hR.diff_mem (hs i) (hCR (ht_mem_C i))) n
        · rw [Set.diff_iInter]
          refine Set.iUnion_mono (fun i ↦ ?_)
          by_cases hin : i ≤ n
          · simp only [hin, Set.iInter_true, Set.iUnion_true]
            refine Set.diff_subset_diff ?_ subset_rfl
            exact Set.biInter_subset_of_mem hin
          · simp only [hin, Set.iInter_of_empty, Set.diff_univ, Set.iUnion_of_empty,
              Set.empty_subset]
    _ = m (⋃ i ∈ Finset.range (n + 1), (s i \ t i)) := by simp only [Finset.mem_range_succ_iff]
    _ ≤ ∑ i ∈ Finset.range (n + 1), m (s i \ t i) :=
        addContent_biUnion_le hR (fun i _ ↦ hR.diff_mem (hs i) (hCR (ht_mem_C i)))
    _ ≤ ∑ i ∈ Finset.range (n + 1), (δ i : ℝ≥0∞) := Finset.sum_le_sum (fun i _ ↦ ht i)
    _ ≤ ∑' i, (δ i : ℝ≥0∞) := ENNReal.sum_le_tsum _
    _ ≤ ε := hδ_sum.le

lemma addContent_iUnion_eq_sum_of_regular (hR : IsSetRing R) (m : AddContent ℝ≥0∞ R)
    (hm_ne_top : ∀ s ∈ R, m s ≠ ∞)
    (hC : IsCompactSystem C) (hCR : C ⊆ R)
    (h_reg : ∀ A ∈ R, ∀ ε, 0 < ε → ∃ K ∈ C, K ⊆ A ∧ m (A \ K) ≤ ε)
    ⦃f : ℕ → Set α⦄ (hf : ∀ i, f i ∈ R) (hUf : (⋃ i, f i) ∈ R)
    (h_disj : Pairwise (Function.onFun Disjoint f)) :
    m (⋃ i, f i) = ∑' i, m (f i) := by
  refine addContent_iUnion_eq_sum_of_tendsto_zero hR m hm_ne_top ?_ hf hUf h_disj
  intro s hs hs_anti hs_iInter
  exact tendsto_zero_of_regular_addContent hR m hs hs_anti hs_iInter hC hCR h_reg

end MeasureTheory
