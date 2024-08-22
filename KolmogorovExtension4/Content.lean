/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
import KolmogorovExtension4.Semiring
import Mathlib.MeasureTheory.OuterMeasure.Induced
import Mathlib.MeasureTheory.Measure.AddContent

open Set Finset Filter

open scoped ENNReal Topology

namespace MeasureTheory

variable {α : Type*} {C : Set (Set α)} {s t : Set α}

section ExtendContent

/-- Build an `AddContent` from an additive function defined on a semiring. -/
noncomputable def extendContent (hC : IsSetSemiring C) (m : ∀ s : Set α, s ∈ C → ℝ≥0∞)
    (m_empty : m ∅ hC.empty_mem = 0)
    (m_add : ∀ (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (_h_dis : PairwiseDisjoint (I : Set (Set α)) id)
      (h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) h_mem = ∑ u : I, m u (h_ss u.prop)) :
    AddContent C where
  toFun := extend m
  empty' := extend_empty hC.empty_mem m_empty
  sUnion' I h_ss h_dis h_mem := by
    simp_rw [← extend_eq m] at m_add
    rw [m_add I h_ss h_dis h_mem, univ_eq_attach]
    exact sum_attach _ _

theorem extendContent_eq_extend (hC : IsSetSemiring C) (m : ∀ s : Set α, s ∈ C → ℝ≥0∞)
    (m_empty : m ∅ hC.empty_mem = 0)
    (m_add : ∀ (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (_h_dis : PairwiseDisjoint (I : Set (Set α)) id)
      (h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) h_mem = ∑ u : I, m u (h_ss u.prop)) :
    extendContent hC m m_empty m_add = extend m := rfl

theorem extendContent_eq (hC : IsSetSemiring C) (m : ∀ s : Set α, s ∈ C → ℝ≥0∞)
    (m_empty : m ∅ hC.empty_mem = 0)
    (m_add : ∀ (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (_h_dis : PairwiseDisjoint (I : Set (Set α)) id)
      (h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) h_mem = ∑ u : I, m u (h_ss u.prop))
    (hs : s ∈ C) :
    extendContent hC m m_empty m_add s = m s hs := by
  rw [extendContent_eq_extend, extend_eq]

theorem extendContent_eq_top (hC : IsSetSemiring C) (m : ∀ s : Set α, s ∈ C → ℝ≥0∞)
    (m_empty : m ∅ hC.empty_mem = 0)
    (m_add : ∀ (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (_h_dis : PairwiseDisjoint (I : Set (Set α)) id)
      (h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) h_mem = ∑ u : I, m u (h_ss u.prop))
    (hs : s ∉ C) :
    extendContent hC m m_empty m_add s = ∞ := by
  rw [extendContent_eq_extend, extend_eq_top m hs]

protected noncomputable
def AddContent.extend (hC : IsSetSemiring C) (m : AddContent C) : AddContent C where
  toFun := extend (fun x (_ : x ∈ C) ↦ m x)
  empty' := by rw [extend_eq, addContent_empty]; exact hC.empty_mem
  sUnion' I h_ss h_dis h_mem := by
    rw [extend_eq]
    swap; · exact h_mem
    rw [addContent_sUnion h_ss h_dis h_mem]
    refine Finset.sum_congr rfl (fun s hs ↦ ?_)
    rw [extend_eq]
    exact h_ss hs

protected theorem AddContent.extend_eq_extend (hC : IsSetSemiring C) (m : AddContent C) :
    m.extend hC = extend (fun x (_ : x ∈ C) ↦ m x) := rfl

protected theorem AddContent.extend_eq (hC : IsSetSemiring C) (m : AddContent C) (hs : s ∈ C) :
    m.extend hC s = m s := by
  rwa [m.extend_eq_extend, extend_eq]

protected theorem AddContent.extend_eq_top (hC : IsSetSemiring C) (m : AddContent C) (hs : s ∉ C) :
    m.extend hC s = ∞ := by
  rwa [m.extend_eq_extend, extend_eq_top]

end ExtendContent

section TotalSetFunction

section Semiring

variable (hC : IsSetSemiring C) (m : Set α → ℝ≥0∞)
  (m_add : ∀ (I : Finset (Set α)) (_h_ss : ↑I ⊆ C) (_h_dis : PairwiseDisjoint (I : Set (Set α)) id)
    (_h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) = ∑ u in I, m u)

lemma addContent_sUnion_le_sum {m : AddContent C} (hC : IsSetSemiring C)
    (J : Finset (Set α)) (h_ss : ↑J ⊆ C) (h_mem : ⋃₀ ↑J ∈ C) :
    m (⋃₀ ↑J) ≤ ∑ u in J, m u := by
  classical
  rw [← hC.sUnion_allDiffFinset₀ J h_ss, addContent_sUnion]
  rotate_left
  · exact hC.allDiffFinset₀_subset J h_ss
  · exact hC.pairwiseDisjoint_allDiffFinset₀ J h_ss
  · rwa [hC.sUnion_allDiffFinset₀ J h_ss]
  rw [IsSetSemiring.allDiffFinset₀, sum_disjiUnion, ← sum_ordered J]
  refine sum_le_sum fun i _ ↦ sum_addContent_le_of_subset hC ?_ ?_ ?_ ?_
  · exact hC.indexedDiffFinset₀_subset J h_ss i
  · exact hC.pairwiseDisjoint_indexedDiffFinset₀' J h_ss i
  · exact h_ss (ordered_mem i)
  · exact Set.sUnion_subset_iff.mp (hC.sUnion_indexedDiffFinset₀_subset J h_ss i)

lemma addContent_le_sum_of_subset_sUnion {m : AddContent C} (hC : IsSetSemiring C)
    (J : Finset (Set α)) (h_ss : ↑J ⊆ C) (ht : t ∈ C) (htJ : t ⊆ ⋃₀ ↑J) :
    m t ≤ ∑ u in J, m u := by
  -- we can't apply `addContent_mono` and `addContent_sUnion_le_sum` because `⋃₀ ↑J` might not
  -- be in `C`
  classical
  let Jt := J.image (fun u ↦ t ∩ u)
  have ht_eq : t = ⋃₀ Jt := by
    rw [coe_image, sUnion_image, ← inter_iUnion₂, inter_eq_self_of_subset_left]
    rwa [← sUnion_eq_biUnion]
  rw [ht_eq]
  refine (addContent_sUnion_le_sum hC Jt ?_ ?_).trans ?_
  · intro s
    simp only [Jt, coe_image, Set.mem_image, mem_coe, forall_exists_index, and_imp]
    rintro u hu rfl
    exact hC.inter_mem _ ht _ (h_ss hu)
  · rwa [← ht_eq]
  refine (Finset.sum_image_le_of_nonneg fun _ _ ↦ zero_le _).trans (sum_le_sum fun u hu ↦ ?_)
  exact addContent_mono hC (hC.inter_mem _ ht _ (h_ss hu)) (h_ss hu) inter_subset_right

/-- If an `AddContent` is σ-subadditive on a semi-ring of sets, then it is σ-additive. -/
theorem addContent_iUnion_eq_tsum_of_disjoint_of_addContent_iUnion_le {m : AddContent C}
    (hC : IsSetSemiring C)
    (m_subadd : ∀ (f : ℕ → Set α) (hf : ∀ i, f i ∈ C) (hf_Union : ⋃ i, f i ∈ C)
      (_hf_disj : Pairwise (Disjoint on f)), m (⋃ i, f i) ≤ ∑' i, m (f i))
    (f : ℕ → Set α) (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C)
    (hf_disj : Pairwise (Disjoint on f)) :
    m (⋃ i, f i) = ∑' i, m (f i) := by
  refine le_antisymm (m_subadd f hf hf_Union hf_disj) ?_
  refine tsum_le_of_sum_le ENNReal.summable fun I ↦ ?_
  classical
  rw [← Finset.sum_image_of_disjoint addContent_empty (hf_disj.pairwiseDisjoint _)]
  refine sum_addContent_le_of_subset hC (I := I.image f) ?_ ?_ hf_Union ?_
  · simp only [coe_image, Set.image_subset_iff]
    refine (subset_preimage_image f I).trans (preimage_mono ?_)
    rintro i ⟨j, _, rfl⟩
    exact hf j
  · simp only [coe_image]
    intro s hs t ht hst
    rw [Set.mem_image] at hs ht
    obtain ⟨i, _, rfl⟩ := hs
    obtain ⟨j, _, rfl⟩ := ht
    have hij : i ≠ j := by intro h_eq; rw [h_eq] at hst; exact hst rfl
    exact hf_disj hij
  · simp only [Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    exact fun i _ ↦ subset_iUnion _ i

end Semiring

section Ring

lemma addContent_diff_of_ne_top (m : AddContent C) (hC : IsSetRing C)
    (hm_ne_top : ∀ s ∈ C, m s ≠ ∞)
    {s t : Set α} (hs : s ∈ C) (ht : t ∈ C) (hts : t ⊆ s) :
    m (s \ t) = m s - m t := by
  have h_union : m (t ∪ s \ t) = m t + m (s \ t) :=
    addContent_union hC ht (hC.diff_mem hs ht) disjoint_sdiff_self_right
  simp_rw [Set.union_diff_self, Set.union_eq_right.mpr hts] at h_union
  rw [h_union, ENNReal.add_sub_cancel_left (hm_ne_top _ ht)]

lemma addContent_accumulate (m : AddContent C) (hC : IsSetRing C)
    {s : ℕ → Set α} (hs_disj : Pairwise (Disjoint on s)) (hsC : ∀ i, s i ∈ C) (n : ℕ) :
      m (Set.Accumulate s n) = ∑ i in Finset.range (n + 1), m (s i) := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [Finset.sum_range_succ, ← hn, Set.accumulate_succ, addContent_union hC _ (hsC _)]
    · exact Set.disjoint_accumulate hs_disj (Nat.lt_succ_self n)
    · exact hC.accumulate_mem hsC n

/-- If an additive content is σ-additive on a set ring, then the content of a monotone sequence of
sets tends to the content of the union. -/
theorem tendsto_atTop_addContent_iUnion_of_addContent_iUnion_eq_tsum {m : AddContent C}
    (hC : IsSetRing C)
    (m_iUnion : ∀ (f : ℕ → Set α) (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C)
        (_hf_disj : Pairwise (Disjoint on f)), m (⋃ i, f i) = ∑' i, m (f i))
    (f : ℕ → Set α) (hf_mono : Monotone f) (hf : ∀ i, f i ∈ C) (hf_Union : ⋃ i, f i ∈ C) :
    Tendsto (fun n ↦ m (f n)) atTop (𝓝 (m (⋃ i, f i))) := by
  classical
  let g := disjointed f
  have hg_Union : (⋃ i, g i) = ⋃ i, f i := iUnion_disjointed
  simp_rw [← hg_Union,
    m_iUnion g (hC.disjointed_mem hf) (by rwa [hg_Union]) (disjoint_disjointed f)]
  have h : ∀ n, m (f n) = ∑ i in range (n + 1), m (g i) := by
    intro n
    have h1 : f n = ⋃₀ Finset.image g (range (n + 1)) := by
      rw [← Monotone.partialSups_eq hf_mono, ← partialSups_disjointed, ←
        partialSups_eq_sUnion_image g]
    rw [h1, addContent_sUnion]
    · rw [sum_image_of_disjoint addContent_empty ((disjoint_disjointed f).pairwiseDisjoint _)]
    · intro s
      rw [mem_coe, Finset.mem_image]
      rintro ⟨i, _, rfl⟩
      exact hC.disjointed_mem hf i
    · intro s hs t ht hst
      rw [mem_coe, Finset.mem_image] at hs ht
      obtain ⟨i, _, rfl⟩ := hs
      obtain ⟨j, _, rfl⟩ := ht
      have hij : i ≠ j := by intro h_eq; rw [h_eq] at hst; exact hst rfl
      exact disjoint_disjointed f hij
    · rw [← h1]; exact hf n
  simp_rw [h]
  change Tendsto (fun n ↦ (fun k ↦ ∑ i in range k, m (g i)) (n + 1)) atTop (𝓝 (∑' i, m (g i)))
  rw [tendsto_add_atTop_iff_nat (f := (fun k ↦ ∑ i in range k, m (g i))) 1]
  exact ENNReal.tendsto_nat_tsum _

/-- If an additive content is σ-additive on a set ring, then it is σ-subadditive. -/
theorem addContent_iUnion_le_of_addContent_iUnion_eq_tsum {m : AddContent C} (hC : IsSetRing C)
    (m_iUnion : ∀ (f : ℕ → Set α) (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C)
      (_hf_disj : Pairwise (Disjoint on f)), m (⋃ i, f i) = ∑' i, m (f i))
    (f : ℕ → Set α) (hf : ∀ i, f i ∈ C) (hf_Union : ⋃ i, f i ∈ C) :
    m (⋃ i, f i) ≤ ∑' i, m (f i) := by
  classical
  have h_tendsto : Tendsto (fun n ↦ m (partialSups f n)) atTop (𝓝 (m (⋃ i, f i))) := by
    rw [← iSup_eq_iUnion, ← iSup_partialSups_eq]
    refine tendsto_atTop_addContent_iUnion_of_addContent_iUnion_eq_tsum hC m_iUnion (partialSups f)
      (partialSups_monotone f) (hC.partialSups_mem hf) ?_
    rwa [← iSup_eq_iUnion, iSup_partialSups_eq]
  have h_tendsto' : Tendsto (fun n ↦ ∑ i in range (n + 1), m (f i)) atTop (𝓝 (∑' i, m (f i))) := by
    rw [tendsto_add_atTop_iff_nat (f := (fun k ↦ ∑ i in range k, m (f i))) 1]
    exact ENNReal.tendsto_nat_tsum _
  refine le_of_tendsto_of_tendsto' h_tendsto h_tendsto' fun n ↦ ?_
  rw [partialSups_eq_sUnion_image]
  refine (addContent_le_sum_of_subset_sUnion hC.isSetSemiring
    ((Finset.range (n + 1)).image f) (fun s ↦ ?_) ?_ subset_rfl).trans ?_
  · rw [mem_coe, Finset.mem_image]
    rintro ⟨i, _, rfl⟩
    exact hf i
  · rw [← partialSups_eq_sUnion_image]
    exact hC.partialSups_mem hf n
  · exact Finset.sum_image_le_of_nonneg fun _ _ ↦ zero_le _

end Ring

end TotalSetFunction

section PartialSetFunction

end PartialSetFunction

end MeasureTheory
