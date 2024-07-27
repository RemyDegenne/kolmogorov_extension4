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

lemma apply_sdiff_eq_sub_of_apply_union_eq_add (hC : IsSetRing C) (m : ∀ s : Set α, s ∈ C → ℝ≥0∞)
    (hm_ne_top : ∀ {s} (hs : s ∈ C), m s hs ≠ ∞)
    (hm_add : ∀ {s t : Set α} (hs : s ∈ C) (ht : t ∈ C),
      Disjoint s t → m (s ∪ t) (hC.union_mem hs ht) = m s hs + m t ht) :
    ∀ {s t} (hs : s ∈ C) (ht : t ∈ C), t ⊆ s →
      m (s \ t) (hC.diff_mem hs ht) = m s hs - m t ht := by
  intro s t hs ht hst
  have h_union := hm_add ht (hC.diff_mem hs ht) disjoint_sdiff_self_right
  simp_rw [Set.union_diff_self, Set.union_eq_right.mpr hst] at h_union
  rw [h_union, ENNReal.add_sub_cancel_left (hm_ne_top ht)]

lemma apply_accumulate_eq_sum (hC : IsSetRing C) (m : ∀ s : Set α, s ∈ C → ℝ≥0∞)
    (hm_add : ∀ {s t : Set α} (hs : s ∈ C) (ht : t ∈ C),
      Disjoint s t → m (s ∪ t) (hC.union_mem hs ht) = m s hs + m t ht)
    {s : ℕ → Set α} (hs_disj : Pairwise (Disjoint on s)) (hsC : ∀ i, s i ∈ C) (n : ℕ) :
      m (Set.Accumulate s n) (hC.accumulate_mem hsC n) =
        ∑ i in Finset.range (n + 1), m (s i) (hsC i) := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [Finset.sum_range_succ, ← hn]
    simp_rw [Set.accumulate_succ]
    rw [hm_add]
    exact Set.disjoint_accumulate hs_disj (Nat.lt_succ_self n)

/-- In a ring of sets, continuity of an additive function at `∅` implies σ-additivity.
This is not true in general in semirings, or without the hypothesis that `m` is finite. See the
examples 7 and 8 in Halmos' book Measure Theory (1974), page 40. -/
theorem sigma_additive_of_tendsto_zero (hC : IsSetRing C) (m : ∀ s : Set α, s ∈ C → ℝ≥0∞)
    (hm_ne_top : ∀ {s} (hs : s ∈ C), m s hs ≠ ∞)
    (hm_add : ∀ {s t : Set α} (hs : s ∈ C) (ht : t ∈ C),
      Disjoint s t → m (s ∪ t) (hC.union_mem hs ht) = m s hs + m t ht)
    (hm : ∀ ⦃s : ℕ → Set α⦄ (hs : ∀ n, s n ∈ C),
      Antitone s → (⋂ n, s n) = ∅ → Tendsto (fun n ↦ m (s n) (hs n)) atTop (𝓝 0))
    ⦃f : ℕ → Set α⦄ (h : ∀ i, f i ∈ C) (hUf : (⋃ i, f i) ∈ C) (h_disj : Pairwise (Disjoint on f)) :
    m (⋃ i, f i) hUf = ∑' i, m (f i) (h i) := by
  -- extend the properties of `m` to `set.sdiff` and `set.accumulate`
  have hm_diff : ∀ {s t} (hs : s ∈ C) (ht : t ∈ C), t ⊆ s →
      m (s \ t) (hC.diff_mem hs ht) = m s hs - m t ht :=
    apply_sdiff_eq_sub_of_apply_union_eq_add hC m hm_ne_top hm_add
  have hm_acc : ∀ {s : ℕ → Set α} (_ : Pairwise (Disjoint on s)) (h_meas : ∀ i, s i ∈ C) (n : ℕ),
      m (Set.Accumulate s n) (hC.accumulate_mem h_meas n) =
        ∑ i in Finset.range (n + 1), m (s i) (h_meas i) := apply_accumulate_eq_sum hC m hm_add
  have hm_mono : ∀ {s t} (hs : s ∈ C) (ht : t ∈ C), t ⊆ s → m t ht ≤ m s hs := by
    intro s t hs ht hst
    have h_union := hm_add ht (hC.diff_mem hs ht) disjoint_sdiff_self_right
    simp_rw [Set.union_diff_self, Set.union_eq_right.mpr hst] at h_union
    rw [h_union]
    exact le_add_right le_rfl
  -- main proof: we use the continuity of `m` at `∅` on the sequence
  -- `n ↦ (⋃ i, f i) \ (set.accumulate f n)`
  let s : ℕ → Set α := fun n ↦ (⋃ i, f i) \ Set.Accumulate f n
  have hCs : ∀ n, s n ∈ C := fun n ↦ hC.diff_mem hUf (hC.accumulate_mem h n)
  have hs_anti : Antitone s := by
    intro i j hij x hxj
    rw [Set.mem_diff] at hxj ⊢
    exact ⟨hxj.1, fun hxi ↦ hxj.2 (Set.monotone_accumulate hij hxi)⟩
  have hs_Inter : (⋂ n, s n) = ∅ := by
    simp_rw [s, Set.diff_eq]
    rw [Set.iInter_inter_distrib, Set.iInter_const, ← Set.compl_iUnion, Set.iUnion_accumulate]
    exact Set.inter_compl_self _
  have h_tendsto : Tendsto (fun n ↦ m (s n) (hCs n)) atTop (𝓝 0) := hm hCs hs_anti hs_Inter
  have hmsn :
      ∀ n, m (s n) (hCs n) = m (⋃ i, f i) hUf - ∑ i in Finset.range (n + 1), m (f i) (h i) := by
    intro n
    rw [hm_diff hUf (hC.accumulate_mem h n)]
    · congr
      exact hm_acc h_disj _ n
    · exact Set.accumulate_subset_iUnion _
  simp_rw [hmsn] at h_tendsto
  have h_tendsto' :
    Tendsto (fun n ↦ ∑ i in Finset.range n, m (f i) (h i)) atTop (𝓝 (m (⋃ i, f i) hUf)) := by
    refine (Filter.tendsto_add_atTop_iff_nat 1).mp ?_
    rwa [ENNReal.tendsto_atTop_zero_const_sub_iff _ _ (hm_ne_top _)] at h_tendsto
    intro n
    rw [← hm_acc h_disj]
    exact hm_mono _ _ (Set.accumulate_subset_iUnion _)
  exact tendsto_nhds_unique h_tendsto' (ENNReal.tendsto_nat_tsum fun i ↦ m (f i) (h i))

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
  have hCs : ∀ n, s n ∈ C := fun n ↦ hC.diff_mem hUf (hC.accumulate_mem hf n)
  have h_tendsto : Tendsto (fun n ↦ m (s n)) atTop (𝓝 0) := by
    refine hm_tendsto hCs ?_ ?_
    · intro i j hij x hxj
      rw [Set.mem_diff] at hxj ⊢
      exact ⟨hxj.1, fun hxi ↦ hxj.2 (Set.monotone_accumulate hij hxi)⟩
    · simp_rw [s, Set.diff_eq]
      rw [Set.iInter_inter_distrib, Set.iInter_const, ← Set.compl_iUnion, Set.iUnion_accumulate]
      exact Set.inter_compl_self _
  have hmsn : ∀ n, m (s n) = m (⋃ i, f i) - ∑ i in Finset.range (n + 1), m (f i) := by
    intro n
    rw [addContent_diff_of_ne_top m hC hm_ne_top hUf (hC.accumulate_mem hf n)]
    · congr
      exact addContent_accumulate m hC h_disj hf n
    · exact Set.accumulate_subset_iUnion _
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
    (h_mem : ⋃₀ ↑I ∈ C) : m (⋃₀ I) = ∑ u in I, m u := by
  classical
  induction' I using Finset.induction with s I hsI h
  · simp only [Finset.coe_empty, Set.sUnion_empty, Finset.sum_empty, m_empty]
  rw [Finset.coe_insert] at *
  rw [Set.insert_subset_iff] at h_ss
  rw [Set.pairwiseDisjoint_insert_of_not_mem] at h_dis
  swap
  · exact hsI
  have h_sUnion_mem : ⋃₀ ↑I ∈ C :=
    haveI : ∀ J : Finset (Set α), ↑J ⊆ C → ⋃₀ ↑J ∈ C := by
      intro J
      induction' J using Finset.induction with s J _ h
      · simp only [Finset.coe_empty, Set.empty_subset, Set.sUnion_empty, forall_true_left, hC_empty]
      · intro h_insert
        rw [Finset.coe_insert] at h_insert ⊢
        rw [Set.insert_subset_iff] at h_insert
        rw [Set.sUnion_insert]
        exact hC_union h_insert.1 (h h_insert.2)
    this I h_ss.2
  rw [Set.sUnion_insert, m_add h_ss.1 h_sUnion_mem (Set.disjoint_sUnion_right.mpr h_dis.2),
    Finset.sum_insert hsI, h h_ss.2 h_dis.1]
  rw [Set.sUnion_insert] at h_mem
  exact h_sUnion_mem

theorem sUnion_eq_sum_of_union_eq_add' (hC_empty : ∅ ∈ C)
    (hC_union : ∀ {s t : Set α} (_ : s ∈ C) (_ : t ∈ C), s ∪ t ∈ C)
    (m : ∀ s : Set α, s ∈ C → ℝ≥0∞) (m_empty : m ∅ hC_empty = 0)
    (m_add : ∀ {s t : Set α} (hs : s ∈ C) (ht : t ∈ C),
      Disjoint s t → m (s ∪ t) (hC_union hs ht) = m s hs + m t ht)
    (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (h_dis : Set.PairwiseDisjoint (I : Set (Set α)) id)
    (h_mem : ⋃₀ ↑I ∈ C) : m (⋃₀ I) h_mem = ∑ u : I, m u (h_ss u.property) := by
  have h :=
    sUnion_eq_sum_of_union_eq_add hC_empty (fun hs ht ↦ hC_union hs ht) (extend m)
      (extend_empty hC_empty m_empty) ?_ I h_ss h_dis h_mem
  · rw [extend_eq m h_mem] at h
    refine h.trans ?_
    simp_rw [← extend_eq m, Finset.univ_eq_attach]
    exact (Finset.sum_attach _ _).symm
  · simp_rw [← extend_eq m] at m_add
    exact m_add

end MeasureTheory
