import Project.Semiring

#align_import content

open Set Finset Filter

open scoped ENNReal BigOperators Topology

namespace MeasureTheory

variable {α : Type _} {C : Set (Set α)} {s t : Set α}

section Extend

theorem extend_sUnion_eq_sum (m : ∀ s : Set α, s ∈ C → ℝ≥0∞)
    (m_add :
      ∀ (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (h_dis : PairwiseDisjoint (I : Set (Set α)) id)
        (h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) h_mem = ∑ u : I, m u (h_ss u.Prop))
    (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (h_dis : PairwiseDisjoint (I : Set (Set α)) id)
    (h_mem : ⋃₀ ↑I ∈ C) : extend m (⋃₀ I) = ∑ u in I, extend m u :=
  by
  rw [extend_eq m h_mem, m_add I h_ss h_dis h_mem]
  have : ∀ (u) (hu : u ∈ I), extend m u = m u (h_ss hu) := fun u hu => extend_eq m (h_ss hu)
  simp_rw [← this, univ_eq_attach]
  exact sum_attach

theorem extend_sum_le (m : ∀ s : Set α, s ∈ C → ℝ≥0∞)
    (m_sigma_subadd :
      ∀ ⦃f : ℕ → Set α⦄ (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C),
        m (⋃ i, f i) hf_Union ≤ ∑' i, m (f i) (hf i))
    ⦃f : ℕ → Set α⦄ (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C) :
    extend m (⋃ i, f i) ≤ ∑' i, extend m (f i) :=
  by
  rw [extend_eq m hf_Union]
  refine' (m_sigma_subadd hf hf_Union).trans_eq _
  congr with i : 1
  rw [extend_eq m (hf i)]

end Extend

section TotalSetFunction

theorem sum_image_eq_of_disjoint {α ι : Type _} [DecidableEq (Set α)] (m : Set α → ℝ≥0∞)
    (m_empty : m ∅ = 0) (f : ι → Set α) (hf_disj : Pairwise (Disjoint on f)) (I : Finset ι) :
    ∑ s in image f I, m s = ∑ i in I, m (f i) :=
  by
  rw [sum_image']
  intro n hnI
  by_cases hfn : f n = ∅
  · simp only [hfn, m_empty]
    refine' (sum_eq_zero fun i hi => _).symm
    rw [mem_filter] at hi 
    rw [hi.2, m_empty]
  · have : (fun j => f j = f n) = fun j => j = n :=
      by
      ext1 j
      rw [eq_iff_iff]
      refine' ⟨fun h => _, fun h => by rw [h]⟩
      by_contra hij
      have h_dis : Disjoint (f j) (f n) := hf_disj hij
      rw [h] at h_dis 
      rw [Set.disjoint_iff_inter_eq_empty, Set.inter_self] at h_dis 
      exact hfn h_dis
    classical
    simp_rw [this]
    simp only [sum_filter, sum_ite_eq', if_pos hnI]

section Semiring

variable (hC : SetSemiring C) (m : Set α → ℝ≥0∞)
  (m_add :
    ∀ (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (h_dis : PairwiseDisjoint (I : Set (Set α)) id)
      (h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) = ∑ u in I, m u)

theorem eq_add_diff₀_of_subset (hs : s ∈ C) (I : Finset (Set α)) (hI : ↑I ⊆ C) (hI_ss : ⋃₀ ↑I ⊆ s)
    (h_dis : PairwiseDisjoint (I : Set (Set α)) id) [DecidableEq (Set α)] :
    m s = ∑ i in I, m i + ∑ i in hC.diff₀ hs I hI, m i := by
  classical
  conv_lhs => rw [hC.eq_sUnion_union_diff₀_of_subset hs I hI hI_ss]
  rw [m_add]
  · rw [sum_union]
    exact hC.disjoint_diff₀ hs I hI
  · rw [coe_union]
    exact Set.union_subset hI (hC.diff₀_subset hs I hI)
  · rw [coe_union]
    exact hC.pairwise_disjoint_union_diff₀ hs I hI h_dis
  · rwa [← hC.eq_sUnion_union_diff₀_of_subset hs I hI hI_ss]

theorem sum_le_of_additive (J : Finset (Set α)) (h_ss : ↑J ⊆ C)
    (h_dis : PairwiseDisjoint (J : Set (Set α)) id) (ht : t ∈ C) (hJt : ⋃₀ ↑J ⊆ t) :
    ∑ u in J, m u ≤ m t := by
  classical
  rw [eq_add_diff₀_of_subset hC m m_add ht J h_ss hJt h_dis]
  exact le_add_right le_rfl

theorem monotone_of_additive (hs : s ∈ C) (ht : t ∈ C) (hst : s ⊆ t) : m s ≤ m t :=
  by
  have h := sum_le_of_additive hC m m_add {s} _ _ ht _
  · simpa only [sum_singleton] using h
  · rwa [singleton_subset_set_iff]
  · simp only [coe_singleton, pairwise_disjoint_singleton]
  · simpa only [coe_singleton, sUnion_singleton]

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (t «expr ∉ » C) -/
theorem monotone_of_additive_of_eq_top (m_top : ∀ (t) (_ : t ∉ C), m t = ∞) (hs : s ∈ C)
    (hst : s ⊆ t) : m s ≤ m t := by
  by_cases ht : t ∈ C
  · exact monotone_of_additive hC m m_add hs ht hst
  · rw [m_top t ht]
    exact le_top

theorem le_sum_of_additive_aux (J : Finset (Set α)) (h_ss : ↑J ⊆ C) (h_mem : ⋃₀ ↑J ∈ C) :
    m (⋃₀ ↑J) ≤ ∑ u in J, m u := by
  classical
  rw [← hC.sUnion_all_diff₀ J h_ss, m_add]
  rotate_left
  · exact hC.all_diff₀_subset J h_ss
  · exact hC.pairwise_disjoint_all_diff₀ J h_ss
  · rwa [hC.sUnion_all_diff₀ J h_ss]
  rw [set_semiring.all_diff₀, sum_disj_Union, ← sum_ordered J]
  refine' sum_le_sum fun i hi => sum_le_of_additive hC m m_add _ _ _ _ _
  · exact hC.indexed_diff₀_subset J h_ss i
  · exact hC.pairwise_disjoint_indexed_diff₀' J h_ss i
  · exact ordered_mem' h_ss i
  · exact hC.sUnion_indexed_diff₀_subset J h_ss i

theorem le_sum_of_additive (J : Finset (Set α)) (h_ss : ↑J ⊆ C) (ht : t ∈ C) (htJ : t ⊆ ⋃₀ ↑J) :
    m t ≤ ∑ u in J, m u := by
  classical
  let Jt := Finset.image (fun u => t ∩ u) J
  have ht_eq : t = ⋃₀ Jt :=
    by
    rw [coe_image, sUnion_image, ← inter_Union₂, inter_eq_self_of_subset_left]
    rwa [← sUnion_eq_bUnion]
  rw [ht_eq]
  refine' (le_sum_of_additive_aux hC m m_add Jt _ _).trans _
  · intro s
    simp only [coe_image, Set.mem_image, mem_coe, forall_exists_index, and_imp]
    rintro u hu rfl
    exact hC.inter_mem _ ht _ (h_ss hu)
  · rwa [← ht_eq]
  refine' (Finset.sum_image_le J _ m fun _ _ => zero_le _).trans _
  refine' sum_le_sum fun u hu => _
  exact
    monotone_of_additive hC m m_add (hC.inter_mem _ ht _ (h_ss hu)) (h_ss hu)
      (inter_subset_right _ _)

theorem countably_additive_of_countably_subadditive (m_empty : m ∅ = 0)
    (m_subadd :
      ∀ (f : ℕ → Set α) (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C)
        (hf_disj : Pairwise (Disjoint on f)), m (⋃ i, f i) ≤ ∑' i, m (f i))
    (f : ℕ → Set α) (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C)
    (hf_disj : Pairwise (Disjoint on f)) : m (⋃ i, f i) = ∑' i, m (f i) :=
  by
  refine' le_antisymm (m_subadd f hf hf_Union hf_disj) _
  refine' tsum_le_of_sum_le ENNReal.summable fun I => _
  classical
  refine' le_trans _ (sum_le_of_additive hC m m_add _ _ _ _ _)
  · exact I.image f
  · rw [sum_image_eq_of_disjoint m m_empty f hf_disj]
    exact le_rfl
  · simp only [coe_image, Set.image_subset_iff]
    refine' (subset_preimage_image f I).trans (preimage_mono _)
    rintro i ⟨j, h, rfl⟩
    exact hf j
  · simp only [coe_image]
    intro s hs t ht hst
    rw [Set.mem_image] at hs ht 
    obtain ⟨i, hi, rfl⟩ := hs
    obtain ⟨j, hj, rfl⟩ := ht
    have hij : i ≠ j := by intro h_eq; rw [h_eq] at hst ; exact hst rfl
    exact hf_disj hij
  · simp only [coe_map, sUnion_image, mem_coe]
    exact hf_Union
  · simp only [coe_image, sUnion_image, mem_coe, Union_subset_iff]
    exact fun i _ => subset_Union _ i

end Semiring

section Ring

theorem continuous_from_below_of_countably_additive (hC : SetRing C) (m : Set α → ℝ≥0∞)
    (m_empty : m ∅ = 0)
    (m_add :
      ∀ (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (h_dis : PairwiseDisjoint (I : Set (Set α)) id)
        (h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) = ∑ u in I, m u)
    (m_c_add :
      ∀ (f : ℕ → Set α) (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C)
        (hf_disj : Pairwise (Disjoint on f)), m (⋃ i, f i) = ∑' i, m (f i))
    (f : ℕ → Set α) (hf_mono : Monotone f) (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C) :
    Tendsto (fun n => m (f n)) atTop (𝓝 (m (⋃ i, f i))) := by
  classical
  let g := disjointed f
  have hg_Union : (⋃ i, g i) = ⋃ i, f i := iUnion_disjointed
  specialize m_c_add g (hC.disjointed_mem hf) _ (disjoint_disjointed f)
  · rwa [hg_Union]
  rw [← hg_Union]
  simp_rw [m_c_add]
  have h : ∀ n, m (f n) = ∑ i in range (n + 1), m (g i) :=
    by
    intro n
    have h1 : f n = ⋃₀ Finset.image g (range (n + 1)) := by
      rw [← Monotone.partialSups_eq hf_mono, ← partialSups_disjointed, ←
        partialSups_eq_sUnion_image g]
    rw [h1, m_add]
    rotate_left
    · intro s
      rw [mem_coe, Finset.mem_image]
      rintro ⟨i, hi, rfl⟩
      exact hC.disjointed_mem hf i
    · intro s hs t ht hst
      rw [mem_coe, Finset.mem_image] at hs ht 
      obtain ⟨i, hi, rfl⟩ := hs
      obtain ⟨j, hj, rfl⟩ := ht
      have hij : i ≠ j := by intro h_eq; rw [h_eq] at hst ; exact hst rfl
      exact disjoint_disjointed f hij
    · rw [← h1]; exact hf n
    rw [sum_image_eq_of_disjoint m m_empty g (disjoint_disjointed f)]
  simp_rw [h]
  change tendsto (fun n => (fun k => ∑ i in range k, m (g i)) (n + 1)) at_top (𝓝 (∑' i, m (g i)))
  rw [tendsto_add_at_top_iff_nat 1]
  exact ENNReal.tendsto_nat_tsum _

-- note that the `f i` are not disjoint
theorem countably_subadditive_of_countably_additive (hC : SetRing C) (m : Set α → ℝ≥0∞)
    (m_empty : m ∅ = 0)
    (m_add :
      ∀ (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (h_dis : PairwiseDisjoint (I : Set (Set α)) id)
        (h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) = ∑ u in I, m u)
    (m_c_add :
      ∀ (f : ℕ → Set α) (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C)
        (hf_disj : Pairwise (Disjoint on f)), m (⋃ i, f i) = ∑' i, m (f i))
    (f : ℕ → Set α) (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C) :
    m (⋃ i, f i) ≤ ∑' i, m (f i) := by
  classical
  have h_tendsto : tendsto (fun n => m (partialSups f n)) at_top (𝓝 (m (⋃ i, f i))) :=
    by
    rw [← supr_eq_Union, ← iSup_partialSups_eq]
    refine'
      continuous_from_below_of_countably_additive hC m m_empty m_add m_c_add (partialSups f)
        (monotone_partialSups f) (fun n => _) _
    · rw [partialSups_eq_biSup]
      simp_rw [supr_eq_Union]
      exact hC.Union_le_mem hf n
    · rwa [← supr_eq_Union, iSup_partialSups_eq]
  have h_tendsto' : tendsto (fun n => ∑ i in range (n + 1), m (f i)) at_top (𝓝 (∑' i, m (f i))) :=
    by
    change tendsto (fun n => (fun k => ∑ i in range k, m (f i)) (n + 1)) at_top (𝓝 (∑' i, m (f i)))
    rw [tendsto_add_at_top_iff_nat 1]
    exact ENNReal.tendsto_nat_tsum _
  refine' le_of_tendsto_of_tendsto' h_tendsto h_tendsto' fun n => _
  rw [partialSups_eq_sUnion_image]
  refine' (le_sum_of_additive_aux hC.set_semiring m m_add _ _ _).trans _
  · intro s
    rw [mem_coe, Finset.mem_image]
    rintro ⟨i, hi, rfl⟩
    exact hf i
  · rw [← partialSups_eq_sUnion_image]
    exact hC.partial_sups_mem hf n
  · exact Finset.sum_image_le _ _ _ fun _ _ => zero_le _

end Ring

end TotalSetFunction

section PartialSetFunction

theorem countably_additive_of_countably_subadditive' (hC : SetSemiring C)
    (m : ∀ s : Set α, s ∈ C → ℝ≥0∞) (m_empty : m ∅ hC.empty_mem = 0)
    (m_add :
      ∀ (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (h_dis : PairwiseDisjoint (I : Set (Set α)) id)
        (h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) h_mem = ∑ u : I, m u (h_ss u.Prop))
    (m_sigma_subadd :
      ∀ ⦃f : ℕ → Set α⦄ (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C),
        m (⋃ i, f i) hf_Union ≤ ∑' i, m (f i) (hf i))
    (f : ℕ → Set α) (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C)
    (hf_disj : Pairwise (Disjoint on f)) : m (⋃ i, f i) hf_Union = ∑' i, m (f i) (hf i) :=
  by
  simp_rw [← extend_eq m] at m_add m_sigma_subadd ⊢
  refine'
    countably_additive_of_countably_subadditive hC (extend m) _ (extend_empty hC.empty_mem m_empty)
      (fun _ h_ss h_mem _ => m_sigma_subadd h_ss h_mem) f hf hf_Union hf_disj
  intro I h_ss h_dis h_mem
  rw [m_add I h_ss h_dis h_mem]
  simp only [univ_eq_attach]
  exact sum_attach

theorem countably_subadditive_of_countably_additive' (hC : SetRing C)
    (m : ∀ s : Set α, s ∈ C → ℝ≥0∞) (m_empty : m ∅ hC.empty_mem = 0)
    (m_add :
      ∀ (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (h_dis : PairwiseDisjoint (I : Set (Set α)) id)
        (h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) h_mem = ∑ u : I, m u (h_ss u.Prop))
    (m_c_add :
      ∀ (f : ℕ → Set α) (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C)
        (hf_disj : Pairwise (Disjoint on f)), m (⋃ i, f i) hf_Union = ∑' i, m (f i) (hf i))
    (f : ℕ → Set α) (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C) :
    m (⋃ i, f i) hf_Union ≤ ∑' i, m (f i) (hf i) :=
  by
  simp_rw [← extend_eq m] at m_add m_c_add ⊢
  refine'
    countably_subadditive_of_countably_additive hC (extend m) (extend_empty hC.empty_mem m_empty) _
      m_c_add f hf hf_Union
  intro I h_ss h_dis h_mem
  rw [m_add I h_ss h_dis h_mem]
  simp only [univ_eq_attach]
  exact sum_attach

theorem monotone_of_additive' (hC : SetSemiring C) (m : ∀ s : Set α, s ∈ C → ℝ≥0∞)
    (m_add :
      ∀ (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (h_dis : PairwiseDisjoint (I : Set (Set α)) id)
        (h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) h_mem = ∑ u : I, m u (h_ss u.Prop))
    (hs : s ∈ C) (ht : t ∈ C) (hst : s ⊆ t) : m s hs ≤ m t ht :=
  by
  simp_rw [← extend_eq m] at m_add ⊢
  refine' monotone_of_additive hC (extend m) _ hs ht hst
  intro I h_ss h_dis h_mem
  rw [m_add I h_ss h_dis h_mem]
  simp only [univ_eq_attach]
  exact sum_attach

end PartialSetFunction

-- named `add_content` because there is already a measure_theory.content, and it satisfies a
--stronger additivity property than the wikipedia content.
/-- An additive content is a finitely additive set-function defined on a set of sets with value 0
at the empty set. -/
structure AddContent (C : Set (Set α)) where
  toFun : Set α → ℝ≥0∞
  empty' : to_fun ∅ = 0
  add' :
    ∀ (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (h_dis : PairwiseDisjoint (I : Set (Set α)) id)
      (h_mem : ⋃₀ ↑I ∈ C), to_fun (⋃₀ I) = ∑ u in I, to_fun u

variable {hC : SetSemiring C}

instance : CoeFun (AddContent C) fun m => Set α → ℝ≥0∞ :=
  ⟨fun μ s => μ.toFun s⟩

@[simp]
theorem addContent_empty {m : AddContent C} : m ∅ = 0 :=
  m.empty'

theorem AddContent.add (m : AddContent C) (I : Finset (Set α)) (h_ss : ↑I ⊆ C)
    (h_dis : PairwiseDisjoint (I : Set (Set α)) id) (h_mem : ⋃₀ ↑I ∈ C) :
    m (⋃₀ I) = ∑ u in I, m u :=
  m.add' I h_ss h_dis h_mem

theorem AddContent.eq_add_diff₀_of_subset (hC : SetSemiring C) (m : AddContent C) (hs : s ∈ C)
    (I : Finset (Set α)) (hI : ↑I ⊆ C) (hI_ss : ⋃₀ ↑I ⊆ s)
    (h_dis : PairwiseDisjoint (I : Set (Set α)) id) [DecidableEq (Set α)] :
    m s = ∑ i in I, m i + ∑ i in hC.diff₀ hs I hI, m i := by
  classical
  conv_lhs => rw [hC.eq_sUnion_union_diff₀_of_subset hs I hI hI_ss]
  rw [m.add]
  · rw [sum_union]
    exact hC.disjoint_diff₀ hs I hI
  · rw [coe_union]
    exact Set.union_subset hI (hC.diff₀_subset hs I hI)
  · rw [coe_union]
    exact hC.pairwise_disjoint_union_diff₀ hs I hI h_dis
  · rwa [← hC.eq_sUnion_union_diff₀_of_subset hs I hI hI_ss]

theorem AddContent.sum_le_of_subset (hC : SetSemiring C) (m : AddContent C) (J : Finset (Set α))
    (h_ss : ↑J ⊆ C) (h_dis : PairwiseDisjoint (J : Set (Set α)) id) (ht : t ∈ C) (hJt : ⋃₀ ↑J ⊆ t) :
    ∑ u in J, m u ≤ m t := by
  classical
  rw [m.eq_add_diff₀_of_subset hC ht J h_ss hJt h_dis]
  exact le_add_right le_rfl

theorem AddContent.mono (m : AddContent C) (hC : SetSemiring C) (hs : s ∈ C) (ht : t ∈ C)
    (hst : s ⊆ t) : m s ≤ m t :=
  by
  have h := m.sum_le_of_subset hC {s} _ _ ht _
  · simpa only [sum_singleton] using h
  · rwa [singleton_subset_set_iff]
  · simp only [coe_singleton, pairwise_disjoint_singleton]
  · simp only [coe_singleton, sUnion_singleton]
    exact hst

theorem addContent_union' (m : AddContent C) (hs : s ∈ C) (ht : t ∈ C) (hst : s ∪ t ∈ C)
    (h_dis : Disjoint s t) : m (s ∪ t) = m s + m t :=
  by
  by_cases hs_empty : s = ∅
  · simp only [hs_empty, Set.empty_union, add_content_empty, zero_add]
  classical
  have h := m.add {s, t} _ _ _
  rotate_left
  · simp only [coe_pair, Set.insert_subset_iff, hs, ht, Set.singleton_subset_iff, and_self_iff]
  · simp only [coe_pair, Set.pairwiseDisjoint_insert, pairwise_disjoint_singleton,
      mem_singleton_iff, Ne.def, id.def, forall_eq, true_and_iff]
    exact fun _ => h_dis
  · simp only [coe_pair, sUnion_insert, sUnion_singleton]
    exact hst
  convert h
  · simp only [coe_pair, sUnion_insert, sUnion_singleton]
  · rw [sum_insert, sum_singleton]
    simp only [Finset.mem_singleton]
    refine' fun hs_eq_t => hs_empty _
    rw [← hs_eq_t] at h_dis 
    exact Disjoint.eq_bot_of_self h_dis

theorem addContent_union (m : AddContent C) (hC : SetRing C) (hs : s ∈ C) (ht : t ∈ C)
    (h_dis : Disjoint s t) : m (s ∪ t) = m s + m t :=
  addContent_union' m hs ht (hC.union_mem hs ht) h_dis

theorem addContent_union_le (m : AddContent C) (hC : SetRing C) (hs : s ∈ C) (ht : t ∈ C) :
    m (s ∪ t) ≤ m s + m t :=
  by
  rw [← union_diff_self, add_content_union m hC hs (hC.diff_mem ht hs)]
  · exact add_le_add le_rfl (m.mono hC.set_semiring (hC.diff_mem ht hs) ht (diff_subset _ _))
  · rw [Set.disjoint_iff_inter_eq_empty, inter_diff_self]

theorem addContent_iUnion_le (m : AddContent C) (hC : SetRing C) {s : ℕ → Set α} (hs : ∀ n, s n ∈ C)
    (n : ℕ) : m (⋃ i ≤ n, s i) ≤ ∑ i in range (n + 1), m (s i) :=
  by
  induction' n with n hn
  · simp only [le_zero_iff, Union_Union_eq_left, Finset.range_one, Finset.sum_singleton, le_refl]
  rw [Set.bUnion_le_succ _ n, Finset.sum_range_succ]
  refine' (add_content_union_le m hC (hC.Union_le_mem hs n) (hs _)).trans _
  exact add_le_add hn le_rfl

theorem addContent_diff (m : AddContent C) (hC : SetRing C) (hs : s ∈ C) (ht : t ∈ C) :
    m s - m t ≤ m (s \ t) :=
  by
  have h : s = s ∩ t ∪ s \ t := by rw [inter_union_diff]
  conv_lhs => rw [h]
  rw [add_content_union m hC (hC.inter_mem hs ht) (hC.diff_mem hs ht) disjoint_inf_sdiff]
  rw [add_comm]
  refine' add_tsub_le_assoc.trans (le_of_eq _)
  rw [tsub_eq_zero_of_le (m.mono hC.set_semiring (hC.inter_mem hs ht) ht (inter_subset_right _ _)),
    add_zero]

theorem AddContent.countably_subadditive_of_countably_additive (hC : SetRing C) (m : AddContent C)
    (m_c_add :
      ∀ (f : ℕ → Set α) (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C)
        (hf_disj : Pairwise (Disjoint on f)), m (⋃ i, f i) = ∑' i, m (f i))
    (f : ℕ → Set α) (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C) :
    m (⋃ i, f i) ≤ ∑' i, m (f i) :=
  countably_subadditive_of_countably_additive hC m addContent_empty m.add m_c_add f hf hf_Union

section ExtendContent

noncomputable def extendContent (hC : SetSemiring C) (m : ∀ s : Set α, s ∈ C → ℝ≥0∞)
    (m_empty : m ∅ hC.empty_mem = 0)
    (m_add :
      ∀ (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (h_dis : PairwiseDisjoint (I : Set (Set α)) id)
        (h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) h_mem = ∑ u : I, m u (h_ss u.Prop)) :
    AddContent C where
  toFun := extend m
  empty' := extend_empty hC.empty_mem m_empty
  add' := by
    simp_rw [← extend_eq m] at m_add 
    intro I h_ss h_dis h_mem
    specialize m_add I h_ss h_dis h_mem
    rw [m_add, univ_eq_attach]
    exact sum_attach

theorem extendContent_eq_extend (hC : SetSemiring C) (m : ∀ s : Set α, s ∈ C → ℝ≥0∞)
    (m_empty : m ∅ hC.empty_mem = 0)
    (m_add :
      ∀ (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (h_dis : PairwiseDisjoint (I : Set (Set α)) id)
        (h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) h_mem = ∑ u : I, m u (h_ss u.Prop)) :
    ⇑(extendContent hC m m_empty m_add) = extend m :=
  rfl

theorem extendContent_eq (hC : SetSemiring C) (m : ∀ s : Set α, s ∈ C → ℝ≥0∞)
    (m_empty : m ∅ hC.empty_mem = 0)
    (m_add :
      ∀ (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (h_dis : PairwiseDisjoint (I : Set (Set α)) id)
        (h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) h_mem = ∑ u : I, m u (h_ss u.Prop))
    (hs : s ∈ C) : extendContent hC m m_empty m_add s = m s hs := by
  rw [extend_content_eq_extend, extend_eq]

theorem extendContent_eq_top (hC : SetSemiring C) (m : ∀ s : Set α, s ∈ C → ℝ≥0∞)
    (m_empty : m ∅ hC.empty_mem = 0)
    (m_add :
      ∀ (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (h_dis : PairwiseDisjoint (I : Set (Set α)) id)
        (h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) h_mem = ∑ u : I, m u (h_ss u.Prop))
    (hs : s ∉ C) : extendContent hC m m_empty m_add s = ∞ := by
  rw [extend_content_eq_extend, extend_eq_top m hs]

end ExtendContent

end MeasureTheory

