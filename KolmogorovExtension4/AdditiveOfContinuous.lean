/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
import KolmogorovExtension4.Content

open Filter

open scoped ENNReal Topology

namespace MeasureTheory

variable {α : Type*} {C : Set (Set α)}

/-- In a ring of sets, continuity of an additive content at `∅` implies σ-additivity.
This is not true in general in semirings, or without the hypothesis that `m` is finite. See the
examples 7 and 8 in Halmos' book Measure Theory (1974), page 40. -/
theorem sigma_additive_addContent_of_tendsto_zero (hC : IsSetRing C) (m : AddContent C)
    (hm_ne_top : ∀ s ∈ C, m s ≠ ∞)
    (hm_tendsto : ∀ ⦃s : ℕ → Set α⦄ (_ : ∀ n, s n ∈ C),
      Antitone s → (⋂ n, s n) = ∅ → Tendsto (fun n ↦ m (s n)) atTop (𝓝 0))
    ⦃f : ℕ → Set α⦄ (hf : ∀ i, f i ∈ C) (hUf : (⋃ i, f i) ∈ C) (h_disj : Pairwise (Disjoint on f)) :
    m (⋃ i, f i) = ∑' i, m (f i) := by
  -- We use the continuity of `m` at `∅` on the sequence `n ↦ (⋃ i, f i) \ (set.accumulate f n)`
  let s : ℕ → Set α := fun n ↦ (⋃ i, f i) \ Set.Accumulate f n
  have hCs n : s n ∈ C := hC.diff_mem hUf (hC.accumulate_mem hf n)
  have h_tendsto : Tendsto (fun n ↦ m (s n)) atTop (𝓝 0) := by
    refine hm_tendsto hCs ?_ ?_
    · intro i j hij x hxj
      rw [Set.mem_diff] at hxj ⊢
      exact ⟨hxj.1, fun hxi ↦ hxj.2 (Set.monotone_accumulate hij hxi)⟩
    · simp_rw [s, Set.diff_eq]
      rw [Set.iInter_inter_distrib, Set.iInter_const, ← Set.compl_iUnion, Set.iUnion_accumulate]
      exact Set.inter_compl_self _
  have hmsn n : m (s n) = m (⋃ i, f i) - ∑ i in Finset.range (n + 1), m (f i) := by
    rw [addContent_diff_of_ne_top m hC hm_ne_top hUf (hC.accumulate_mem hf n)
      (Set.accumulate_subset_iUnion _), addContent_accumulate m hC h_disj hf n]
  simp_rw [hmsn] at h_tendsto
  have h_tendsto' :
      Tendsto (fun n ↦ ∑ i in Finset.range n, m (f i)) atTop (𝓝 (m (⋃ i, f i))) := by
    refine (Filter.tendsto_add_atTop_iff_nat 1).mp ?_
    rwa [ENNReal.tendsto_atTop_zero_const_sub_iff _ _ (hm_ne_top _ hUf)] at h_tendsto
    intro n
    rw [← addContent_accumulate m hC h_disj hf]
    exact addContent_mono hC.isSetSemiring (hC.accumulate_mem hf n) hUf
      (Set.accumulate_subset_iUnion _)
  exact tendsto_nhds_unique h_tendsto' (ENNReal.tendsto_nat_tsum fun i ↦ m (f i))

theorem sUnion_eq_sum_of_union_eq_add (hC_empty : ∅ ∈ C)
    (hC_union : ∀ {s t : Set α} (_ : s ∈ C) (_ : t ∈ C), s ∪ t ∈ C) (m : Set α → ℝ≥0∞)
    (m_empty : m ∅ = 0)
    (m_add : ∀ {s t : Set α} (_ : s ∈ C) (_ : t ∈ C), Disjoint s t → m (s ∪ t) = m s + m t)
    (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (h_dis : Set.PairwiseDisjoint (I : Set (Set α)) id)
    (h_mem : ⋃₀ ↑I ∈ C) :
    m (⋃₀ I) = ∑ u in I, m u := by
  classical
  induction I using Finset.induction with
  | empty =>
    simp only [Finset.coe_empty, Set.sUnion_empty, Finset.sum_empty, m_empty]
  | @insert s I hsI h =>
    rw [Finset.coe_insert] at *
    rw [Set.insert_subset_iff] at h_ss
    rw [Set.pairwiseDisjoint_insert_of_not_mem] at h_dis
    swap; · exact hsI
    have h_sUnion_mem : ⋃₀ ↑I ∈ C := by
      have (J : Finset (Set α)) : ↑J ⊆ C → ⋃₀ ↑J ∈ C := by
        induction J using Finset.induction with --s J _ h
        | empty => simp only [Finset.coe_empty, Set.empty_subset, Set.sUnion_empty,
            forall_true_left, hC_empty]
        | @insert s I _ h =>
          intro h_insert
          simp only [Finset.coe_insert, Set.sUnion_insert, Set.insert_subset_iff] at h_insert ⊢
          exact hC_union h_insert.1 (h h_insert.2)
      exact this I h_ss.2
    rw [Set.sUnion_insert, m_add h_ss.1 h_sUnion_mem (Set.disjoint_sUnion_right.mpr h_dis.2),
      Finset.sum_insert hsI, h h_ss.2 h_dis.1]
    rwa [Set.sUnion_insert] at h_mem

theorem sUnion_eq_sum_of_union_eq_add' (hC_empty : ∅ ∈ C)
    (hC_union : ∀ {s t : Set α} (_ : s ∈ C) (_ : t ∈ C), s ∪ t ∈ C)
    (m : ∀ s : Set α, s ∈ C → ℝ≥0∞) (m_empty : m ∅ hC_empty = 0)
    (m_add : ∀ {s t : Set α} (hs : s ∈ C) (ht : t ∈ C),
      Disjoint s t → m (s ∪ t) (hC_union hs ht) = m s hs + m t ht)
    (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (h_dis : Set.PairwiseDisjoint (I : Set (Set α)) id)
    (h_mem : ⋃₀ ↑I ∈ C) : m (⋃₀ I) h_mem = ∑ u : I, m u (h_ss u.property) := by
  have h : extend m (⋃₀ ↑I) = ∑ u ∈ I, extend m u :=
    sUnion_eq_sum_of_union_eq_add hC_empty (fun hs ht ↦ hC_union hs ht) (extend m)
      (extend_empty hC_empty m_empty) ?_ I h_ss h_dis h_mem
  · rw [extend_eq m h_mem] at h
    refine h.trans ?_
    simp_rw [← extend_eq m, Finset.univ_eq_attach]
    exact (Finset.sum_attach _ _).symm
  · simp_rw [← extend_eq m] at m_add
    exact m_add

end MeasureTheory
