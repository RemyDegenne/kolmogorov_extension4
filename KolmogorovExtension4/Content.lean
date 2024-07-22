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

section Extend

theorem extend_sUnion_eq_sum (m : ∀ s : Set α, s ∈ C → ℝ≥0∞)
    (m_add :
      ∀ (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (_h_dis : PairwiseDisjoint (I : Set (Set α)) id)
        (h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) h_mem = ∑ u : I, m u (h_ss u.prop))
    (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (h_dis : PairwiseDisjoint (I : Set (Set α)) id)
    (h_mem : ⋃₀ ↑I ∈ C) : extend m (⋃₀ I) = ∑ u in I, extend m u := by
  rw [extend_eq m h_mem, m_add I h_ss h_dis h_mem]
  simp only [univ_eq_attach]
  rw [← sum_attach (s := I)]
  congr with u
  rw [extend_eq m (h_ss u.prop)]

theorem extend_sum_le (m : ∀ s : Set α, s ∈ C → ℝ≥0∞)
    (m_sigma_subadd : ∀ ⦃f : ℕ → Set α⦄ (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C),
      m (⋃ i, f i) hf_Union ≤ ∑' i, m (f i) (hf i))
    ⦃f : ℕ → Set α⦄ (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C) :
    extend m (⋃ i, f i) ≤ ∑' i, extend m (f i) := by
  rw [extend_eq m hf_Union]
  refine (m_sigma_subadd hf hf_Union).trans_eq ?_
  congr with i : 1
  rw [extend_eq m (hf i)]

end Extend

section TotalSetFunction

theorem sum_image_eq_of_disjoint {α ι : Type*} [DecidableEq (Set α)] (m : Set α → ℝ≥0∞)
    (m_empty : m ∅ = 0) (f : ι → Set α) (hf_disj : Pairwise (Disjoint on f)) (I : Finset ι) :
    ∑ s in image f I, m s = ∑ i in I, m (f i) := by
  rw [sum_image']
  intro n hnI
  by_cases hfn : f n = ∅
  · simp only [hfn, m_empty]
    refine (sum_eq_zero fun i hi ↦ ?_).symm
    rw [mem_filter] at hi
    rw [hi.2, m_empty]
  · have : (fun j ↦ f j = f n) = fun j ↦ j = n := by
      ext1 j
      rw [eq_iff_iff]
      refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]⟩
      by_contra hij
      have h_dis : Disjoint (f j) (f n) := hf_disj hij
      rw [h] at h_dis
      rw [Set.disjoint_iff_inter_eq_empty, Set.inter_self] at h_dis
      exact hfn h_dis
    classical
    simp_rw [this]
    simp only [sum_filter, sum_ite_eq', if_pos hnI]

section Semiring

variable (hC : IsSetSemiring C) (m : Set α → ℝ≥0∞)
  (m_add : ∀ (I : Finset (Set α)) (_h_ss : ↑I ⊆ C) (_h_dis : PairwiseDisjoint (I : Set (Set α)) id)
    (_h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) = ∑ u in I, m u)

theorem eq_add_diffFinset₀_of_subset (hs : s ∈ C)
    {I : Finset (Set α)} (hI : ↑I ⊆ C) (hI_ss : ∀ t ∈ I, t ⊆ s)
    (h_dis : PairwiseDisjoint (I : Set (Set α)) id) [DecidableEq (Set α)] :
    m s = ∑ i in I, m i + ∑ i in hC.diffFinset₀ hs hI, m i := by
  classical
  conv_lhs => rw [← hC.sUnion_union_diffFinset₀_of_subset hs hI hI_ss]
  rw [m_add]
  · rw [sum_union]
    exact hC.disjoint_diffFinset₀ hs hI
  · rw [coe_union]
    exact Set.union_subset hI (hC.diffFinset₀_subset hs hI)
  · rw [coe_union]
    exact hC.pairwiseDisjoint_union_diffFinset₀ hs hI h_dis
  · rwa [hC.sUnion_union_diffFinset₀_of_subset hs hI hI_ss]

theorem sum_le_of_additive {J : Finset (Set α)} (h_ss : ↑J ⊆ C)
    (h_dis : PairwiseDisjoint (J : Set (Set α)) id) (ht : t ∈ C) (hJt : ∀ u ∈ J, u ⊆ t) :
    ∑ u in J, m u ≤ m t := by
  classical
  rw [eq_add_diffFinset₀_of_subset hC m m_add ht h_ss hJt h_dis]
  exact le_add_right le_rfl

theorem monotone_of_additive (hs : s ∈ C) (ht : t ∈ C) (hst : s ⊆ t) : m s ≤ m t := by
  have h := sum_le_of_additive hC m m_add (J := {s}) ?_ ?_ ht ?_
  · simpa only [sum_singleton] using h
  · rwa [singleton_subset_set_iff]
  · simp only [coe_singleton, pairwiseDisjoint_singleton]
  · simpa only [Finset.mem_singleton, forall_eq]

theorem monotone_of_additive_of_eq_top (m_top : ∀ (t) (_ : t ∉ C), m t = ∞) (hs : s ∈ C)
    (hst : s ⊆ t) : m s ≤ m t := by
  by_cases ht : t ∈ C
  · exact monotone_of_additive hC m m_add hs ht hst
  · rw [m_top t ht]
    exact le_top

theorem le_sum_of_additive_aux {J : Finset (Set α)} (h_ss : ↑J ⊆ C) (h_mem : ⋃₀ ↑J ∈ C) :
    m (⋃₀ ↑J) ≤ ∑ u in J, m u := by
  classical
  rw [← hC.sUnion_allDiff₀ h_ss, m_add]
  rotate_left
  · exact hC.allDiff₀_subset h_ss
  · exact hC.pairwiseDisjoint_allDiff₀ h_ss
  · rwa [hC.sUnion_allDiff₀ h_ss]
  rw [IsSetSemiring.allDiff₀, sum_disjiUnion, ← sum_ordered J]
  refine sum_le_sum fun i _ ↦ sum_le_of_additive hC m m_add ?_ ?_ ?_ ?_
  · exact hC.indexedDiff₀_subset h_ss i
  · exact hC.pairwiseDisjoint_indexedDiff₀' h_ss i
  · exact ordered_mem' h_ss i
  · exact hC.subset_of_mem_indexedDiff₀ _ _

theorem le_sum_of_additive {J : Finset (Set α)} (h_ss : ↑J ⊆ C) (ht : t ∈ C) (htJ : t ⊆ ⋃₀ ↑J) :
    m t ≤ ∑ u in J, m u := by
  classical
  let Jt := Finset.image (fun u ↦ t ∩ u) J
  have ht_eq : t = ⋃₀ Jt := by
    rw [coe_image, sUnion_image, ← inter_iUnion₂, inter_eq_self_of_subset_left]
    rwa [← sUnion_eq_biUnion]
  rw [ht_eq]
  refine (le_sum_of_additive_aux hC m m_add ?_ ?_).trans ?_
  · intro s
    simp only [Jt, coe_image, Set.mem_image, mem_coe, forall_exists_index, and_imp]
    rintro u hu rfl
    exact hC.inter_mem _ ht _ (h_ss hu)
  · rwa [← ht_eq]
  refine (Finset.sum_image_le J _ m fun _ _ ↦ zero_le _).trans ?_
  refine sum_le_sum fun u hu ↦ ?_
  exact monotone_of_additive hC m m_add (hC.inter_mem _ ht _ (h_ss hu)) (h_ss hu)
    inter_subset_right

theorem sigma_additive_of_sigma_subadditive (m_empty : m ∅ = 0)
    (m_subadd : ∀ (f : ℕ → Set α) (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C)
      (_hf_disj : Pairwise (Disjoint on f)), m (⋃ i, f i) ≤ ∑' i, m (f i))
    (f : ℕ → Set α) (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C)
    (hf_disj : Pairwise (Disjoint on f)) : m (⋃ i, f i) = ∑' i, m (f i) := by
  refine le_antisymm (m_subadd f hf hf_Union hf_disj) ?_
  refine tsum_le_of_sum_le ENNReal.summable fun I ↦ ?_
  classical
  refine le_trans ?_ (sum_le_of_additive hC m m_add (J := I.image f) ?_ ?_ ?_ ?_)
  · rw [sum_image_eq_of_disjoint m m_empty f hf_disj]
  · simp only [coe_image, Set.image_subset_iff]
    refine (subset_preimage_image f I).trans (preimage_mono ?_)
    rintro i ⟨j, _, rfl⟩
    exact hf j
  · simp only [coe_image]
    intro s hs t ht hst
    rw [Set.mem_image] at hs ht
    obtain ⟨i, _, rfl⟩ := hs
    obtain ⟨j, _, rfl⟩ := ht
    have hij : i ≠ j := by intro h_eq; rw [h_eq] at hst ; exact hst rfl
    exact hf_disj hij
  · exact hf_Union
  · simp only [Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    exact fun i _ ↦ subset_iUnion _ i

end Semiring

section Ring

theorem continuous_from_below_of_sigma_additive (hC : IsSetRing C) (m : Set α → ℝ≥0∞)
    (m_empty : m ∅ = 0)
    (m_add :
      ∀ (I : Finset (Set α)) (_h_ss : ↑I ⊆ C) (_h_dis : PairwiseDisjoint (I : Set (Set α)) id)
        (_h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) = ∑ u in I, m u)
    (m_c_add : ∀ (f : ℕ → Set α) (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C)
        (_hf_disj : Pairwise (Disjoint on f)), m (⋃ i, f i) = ∑' i, m (f i))
    (f : ℕ → Set α) (hf_mono : Monotone f) (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C) :
    Tendsto (fun n ↦ m (f n)) atTop (𝓝 (m (⋃ i, f i))) := by
  classical
  let g := disjointed f
  have hg_Union : (⋃ i, g i) = ⋃ i, f i := iUnion_disjointed
  specialize m_c_add g (hC.disjointed_mem hf) _ (disjoint_disjointed f)
  · rwa [hg_Union]
  rw [← hg_Union]
  simp_rw [m_c_add]
  have h : ∀ n, m (f n) = ∑ i in range (n + 1), m (g i) := by
    intro n
    have h1 : f n = ⋃₀ Finset.image g (range (n + 1)) := by
      rw [← Monotone.partialSups_eq hf_mono, ← partialSups_disjointed, ←
        partialSups_eq_sUnion_image g]
    rw [h1, m_add]
    rotate_left
    · intro s
      rw [mem_coe, Finset.mem_image]
      rintro ⟨i, _, rfl⟩
      exact hC.disjointed_mem hf i
    · intro s hs t ht hst
      rw [mem_coe, Finset.mem_image] at hs ht
      obtain ⟨i, _, rfl⟩ := hs
      obtain ⟨j, _, rfl⟩ := ht
      have hij : i ≠ j := by intro h_eq; rw [h_eq] at hst ; exact hst rfl
      exact disjoint_disjointed f hij
    · rw [← h1]; exact hf n
    rw [sum_image_eq_of_disjoint m m_empty g (disjoint_disjointed f)]
  simp_rw [h]
  change Tendsto (fun n ↦ (fun k ↦ ∑ i in range k, m (g i)) (n + 1)) atTop (𝓝 (∑' i, m (g i)))
  rw [tendsto_add_atTop_iff_nat (f := (fun k ↦ ∑ i in range k, m (g i))) 1]
  exact ENNReal.tendsto_nat_tsum _

-- note that the `f i` are not disjoint
theorem sigma_subadditive_of_sigma_additive (hC : IsSetRing C) (m : Set α → ℝ≥0∞)
    (m_empty : m ∅ = 0)
    (m_add :
      ∀ (I : Finset (Set α)) (_h_ss : ↑I ⊆ C) (_h_dis : PairwiseDisjoint (I : Set (Set α)) id)
        (_h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) = ∑ u in I, m u)
    (m_c_add : ∀ (f : ℕ → Set α) (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C)
      (_hf_disj : Pairwise (Disjoint on f)), m (⋃ i, f i) = ∑' i, m (f i))
    (f : ℕ → Set α) (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C) :
    m (⋃ i, f i) ≤ ∑' i, m (f i) := by
  classical
  have h_tendsto : Tendsto (fun n ↦ m (partialSups f n)) atTop (𝓝 (m (⋃ i, f i))) := by
    rw [← iSup_eq_iUnion, ← iSup_partialSups_eq]
    refine continuous_from_below_of_sigma_additive hC m m_empty m_add m_c_add (partialSups f)
      (monotone_partialSups f) (fun n ↦ ?_) ?_
    · rw [partialSups_eq_biSup]
      simp_rw [iSup_eq_iUnion]
      exact hC.iUnion_le_mem hf n
    · rwa [← iSup_eq_iUnion, iSup_partialSups_eq]
  have h_tendsto' :
      Tendsto (fun n ↦ ∑ i in range (n + 1), m (f i)) atTop (𝓝 (∑' i, m (f i))) := by
    change Tendsto (fun n ↦ (fun k ↦ ∑ i in range k, m (f i)) (n + 1)) atTop (𝓝 (∑' i, m (f i)))
    rw [tendsto_add_atTop_iff_nat (f := (fun k ↦ ∑ i in range k, m (f i))) 1]
    exact ENNReal.tendsto_nat_tsum _
  refine le_of_tendsto_of_tendsto' h_tendsto h_tendsto' fun n ↦ ?_
  rw [partialSups_eq_sUnion_image]
  refine (le_sum_of_additive_aux hC.isSetSemiring m m_add ?_ ?_).trans ?_
  · intro s
    rw [mem_coe, Finset.mem_image]
    rintro ⟨i, _, rfl⟩
    exact hf i
  · rw [← partialSups_eq_sUnion_image]
    exact hC.partialSups_mem hf n
  · exact Finset.sum_image_le _ _ _ fun _ _ ↦ zero_le _

end Ring

end TotalSetFunction

section PartialSetFunction

theorem sigma_additive_of_sigma_subadditive' (hC : IsSetSemiring C)
    (m : ∀ s : Set α, s ∈ C → ℝ≥0∞) (m_empty : m ∅ hC.empty_mem = 0)
    (m_add :
      ∀ (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (_h_dis : PairwiseDisjoint (I : Set (Set α)) id)
        (h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) h_mem = ∑ u : I, m u (h_ss u.prop))
    (m_sigma_subadd : ∀ ⦃f : ℕ → Set α⦄ (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C),
      m (⋃ i, f i) hf_Union ≤ ∑' i, m (f i) (hf i))
    (f : ℕ → Set α) (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C)
    (hf_disj : Pairwise (Disjoint on f)) : m (⋃ i, f i) hf_Union = ∑' i, m (f i) (hf i) := by
  simp_rw [← extend_eq m] at m_add m_sigma_subadd ⊢
  refine sigma_additive_of_sigma_subadditive hC (extend m) ?_
    (extend_empty hC.empty_mem m_empty)
    (fun _ h_ss h_mem _ ↦ m_sigma_subadd h_ss h_mem) f hf hf_Union hf_disj
  intro I h_ss h_dis h_mem
  rw [m_add I h_ss h_dis h_mem]
  simp only [univ_eq_attach]
  exact sum_attach _ _

theorem sigma_subadditive_of_sigma_additive' (hC : IsSetRing C)
    (m : ∀ s : Set α, s ∈ C → ℝ≥0∞) (m_empty : m ∅ hC.empty_mem = 0)
    (m_add :
      ∀ (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (_h_dis : PairwiseDisjoint (I : Set (Set α)) id)
        (h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) h_mem = ∑ u : I, m u (h_ss u.prop))
    (m_c_add : ∀ (f : ℕ → Set α) (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C)
      (_hf_disj : Pairwise (Disjoint on f)), m (⋃ i, f i) hf_Union = ∑' i, m (f i) (hf i))
    (f : ℕ → Set α) (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C) :
    m (⋃ i, f i) hf_Union ≤ ∑' i, m (f i) (hf i) := by
  simp_rw [← extend_eq m] at m_add m_c_add ⊢
  refine sigma_subadditive_of_sigma_additive hC (extend m)
    (extend_empty hC.empty_mem m_empty) ?_ m_c_add f hf hf_Union
  intro I h_ss h_dis h_mem
  rw [m_add I h_ss h_dis h_mem]
  simp only [univ_eq_attach]
  exact sum_attach _ _

theorem monotone_of_additive' (hC : IsSetSemiring C) (m : ∀ s : Set α, s ∈ C → ℝ≥0∞)
    (m_add :
      ∀ (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (_h_dis : PairwiseDisjoint (I : Set (Set α)) id)
        (h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) h_mem = ∑ u : I, m u (h_ss u.prop))
    (hs : s ∈ C) (ht : t ∈ C) (hst : s ⊆ t) : m s hs ≤ m t ht := by
  simp_rw [← extend_eq m] at m_add ⊢
  refine monotone_of_additive hC (extend m) ?_ hs ht hst
  intro I h_ss h_dis h_mem
  rw [m_add I h_ss h_dis h_mem]
  simp only [univ_eq_attach]
  exact sum_attach _ _

end PartialSetFunction

theorem AddContent.sigma_subadditive_of_sigma_additive (hC : IsSetRing C) (m : AddContent C)
    (m_c_add :
      ∀ (f : ℕ → Set α) (_hf : ∀ i, f i ∈ C) (_hf_Union : (⋃ i, f i) ∈ C)
        (_hf_disj : Pairwise (Disjoint on f)), m (⋃ i, f i) = ∑' i, m (f i))
    (f : ℕ → Set α) (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C) :
    m (⋃ i, f i) ≤ ∑' i, m (f i) :=
  MeasureTheory.sigma_subadditive_of_sigma_additive hC m addContent_empty m.sUnion' m_c_add f hf
    hf_Union

section ExtendContent

/-- Build an `AddContent` from an additive function defined on a semiring. -/
noncomputable def extendContent (hC : IsSetSemiring C) (m : ∀ s : Set α, s ∈ C → ℝ≥0∞)
    (m_empty : m ∅ hC.empty_mem = 0)
    (m_add :
      ∀ (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (_h_dis : PairwiseDisjoint (I : Set (Set α)) id)
        (h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) h_mem = ∑ u : I, m u (h_ss u.prop)) :
    AddContent C where
  toFun := extend m
  empty' := extend_empty hC.empty_mem m_empty
  sUnion' := by
    simp_rw [← extend_eq m] at m_add
    intro I h_ss h_dis h_mem
    specialize m_add I h_ss h_dis h_mem
    rw [m_add, univ_eq_attach]
    exact sum_attach _ _

theorem extendContent_eq_extend (hC : IsSetSemiring C) (m : ∀ s : Set α, s ∈ C → ℝ≥0∞)
    (m_empty : m ∅ hC.empty_mem = 0)
    (m_add :
      ∀ (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (_h_dis : PairwiseDisjoint (I : Set (Set α)) id)
        (h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) h_mem = ∑ u : I, m u (h_ss u.prop)) :
    ⇑(extendContent hC m m_empty m_add) = extend m :=
  rfl

theorem extendContent_eq (hC : IsSetSemiring C) (m : ∀ s : Set α, s ∈ C → ℝ≥0∞)
    (m_empty : m ∅ hC.empty_mem = 0)
    (m_add :
      ∀ (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (_h_dis : PairwiseDisjoint (I : Set (Set α)) id)
        (h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) h_mem = ∑ u : I, m u (h_ss u.prop))
    (hs : s ∈ C) : extendContent hC m m_empty m_add s = m s hs := by
  rw [extendContent_eq_extend, extend_eq]

theorem extendContent_eq_top (hC : IsSetSemiring C) (m : ∀ s : Set α, s ∈ C → ℝ≥0∞)
    (m_empty : m ∅ hC.empty_mem = 0)
    (m_add :
      ∀ (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (_h_dis : PairwiseDisjoint (I : Set (Set α)) id)
        (h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) h_mem = ∑ u : I, m u (h_ss u.prop))
    (hs : s ∉ C) : extendContent hC m m_empty m_add s = ∞ := by
  rw [extendContent_eq_extend, extend_eq_top m hs]

end ExtendContent

end MeasureTheory
