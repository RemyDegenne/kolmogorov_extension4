/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
import Mathlib.MeasureTheory.Measure.Trim
import KolmogorovExtension4.Content

open Finset Set MeasureTheory Order

open scoped Classical NNReal Topology ENNReal MeasureTheory

namespace MeasureTheory

variable {α : Type*} {C : Set (Set α)}

namespace OuterMeasure

section IsCaratheodory

variable {m : OuterMeasure α} {s : ℕ → Set α}

lemma isCaratheodory_diff {s t : Set α} (hs : IsCaratheodory m s) (ht : IsCaratheodory m t) :
    IsCaratheodory m (s \ t) := by
  rw [diff_eq]
  exact m.isCaratheodory_inter hs (m.isCaratheodory_compl ht)

lemma isCaratheodory_partialSups (h : ∀ i, m.IsCaratheodory (s i)) (i : ℕ) :
    m.IsCaratheodory (partialSups s i) := by
  induction i with
  | zero => rw [partialSups_zero]; exact h 0
  | succ i hi => rw [partialSups_succ]; exact m.isCaratheodory_union hi (h (i + 1))

lemma isCaratheodory_disjointed (h : ∀ i, m.IsCaratheodory (s i)) (i : ℕ) :
    m.IsCaratheodory (disjointed s i) := by
  induction i with
  | zero => rw [disjointed_zero]; exact h 0
  | succ i _ =>
    rw [disjointed_succ, diff_eq]
    exact m.isCaratheodory_diff (h (i + 1)) (isCaratheodory_partialSups h i)

-- todo: this is an improvement over `isCaratheodory_iUnion_nat`
lemma isCaratheodory_iUnion (h : ∀ i, m.IsCaratheodory (s i)) : m.IsCaratheodory (⋃ i, s i) := by
  rw [← iUnion_disjointed]
  exact OuterMeasure.isCaratheodory_iUnion_nat m (isCaratheodory_disjointed h)
    (disjoint_disjointed _)

end IsCaratheodory

section OfFunction

/-- Same as the definition of `of_function`, except that `f i` belongs to `C`. The hypothesis
`m_top` applies in particular to a function of the form `extend m'`. -/
theorem ofFunction_eq_iInf_mem (s : Set α) (m : Set α → ℝ≥0∞) (m_empty : m ∅ = 0)
    (m_top : ∀ s ∉ C, m s = ∞) :
    OuterMeasure.ofFunction m m_empty s =
      ⨅ (f : ℕ → Set α) (_hf : ∀ i, f i ∈ C) (_ : s ⊆ ⋃ i, f i), ∑' i, m (f i) := by
  rw [OuterMeasure.ofFunction_apply]
  apply le_antisymm
  · refine le_iInf fun f ↦ le_iInf fun _ ↦ le_iInf fun h ↦ ?_
    refine iInf₂_le _ ?_
    exact h
  · simp_rw [le_iInf_iff]
    intro f hf_subset
    refine iInf_le_of_le f ?_
    by_cases hf : ∀ i, f i ∈ C
    · exact iInf_le_of_le hf (iInf_le_of_le hf_subset le_rfl)
    · simp only [hf, not_false_eq_true, iInf_neg, top_le_iff]
      push_neg at hf
      obtain ⟨i, hfi_not_mem⟩ := hf
      have hfi_top : m (f i) = ∞ := m_top _ hfi_not_mem
      exact ENNReal.tsum_eq_top_of_eq_top ⟨i, hfi_top⟩

theorem ofFunction_eq_of_mono_of_subadditive (hC : IsSetSemiring C) (m : Set α → ℝ≥0∞)
    (m_empty : m ∅ = 0) (m_mono : ∀ ⦃s t : Set α⦄ (_hs : s ∈ C) (_ht : t ∈ C), s ⊆ t → m s ≤ m t)
    (m_sigma_subadd : ∀ ⦃f : ℕ → Set α⦄ (_hf : ∀ i, f i ∈ C) (_hf_Union : (⋃ i, f i) ∈ C),
        m (⋃ i, f i) ≤ ∑' i, m (f i))
    (m_top : ∀ s ∉ C, m s = ∞) {s : Set α} (hs : s ∈ C) :
    OuterMeasure.ofFunction m m_empty s = m s := by
  refine le_antisymm (OuterMeasure.ofFunction_le s) ?_
  rw [ofFunction_eq_iInf_mem s m m_empty m_top]
  refine le_iInf fun f ↦ le_iInf fun hf ↦ le_iInf fun hs_subset ↦ ?_
  calc m s = m (s ∩ ⋃ i, f i) := by rw [inter_eq_self_of_subset_left hs_subset]
    _ = m (⋃ i, s ∩ f i) := by rw [inter_iUnion]
    _ ≤ ∑' i, m (s ∩ f i) := by
      refine m_sigma_subadd (fun i ↦ hC.inter_mem _ hs _ (hf i)) ?_
      rwa [← inter_iUnion, inter_eq_self_of_subset_left hs_subset]
    _ ≤ ∑' i, m (f i) := by
      refine tsum_le_tsum (fun i ↦ ?_) ENNReal.summable ENNReal.summable
      exact m_mono (hC.inter_mem _ hs _ (hf i)) (hf i) Set.inter_subset_right

theorem ofFunction_eq_of_add_of_subadditive (hC : IsSetSemiring C) (m : Set α → ℝ≥0∞)
    (m_empty : m ∅ = 0)
    (m_add : ∀ (I : Finset (Set α)) (_ : ↑I ⊆ C) (_ : PairwiseDisjoint (I : Set (Set α)) id)
        (_h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) = ∑ u in I, m u)
    (m_sigma_subadd :  ∀ ⦃f : ℕ → Set α⦄ (_hf : ∀ i, f i ∈ C) (_hf_Union : (⋃ i, f i) ∈ C),
        m (⋃ i, f i) ≤ ∑' i, m (f i))
    (m_top : ∀ s ∉ C, m s = ∞) {s : Set α} (hs : s ∈ C) :
    OuterMeasure.ofFunction m m_empty s = m s :=
  OuterMeasure.ofFunction_eq_of_mono_of_subadditive hC m m_empty
    (fun _ _ ↦ monotone_of_additive hC m m_add) m_sigma_subadd m_top hs

theorem ofFunction_addContent_eq (hC : IsSetSemiring C) (m : AddContent C)
    (m_sigma_subadd : ∀ ⦃f : ℕ → Set α⦄ (_hf : ∀ i, f i ∈ C) (_hf_Union : (⋃ i, f i) ∈ C),
      m (⋃ i, f i) ≤ ∑' i, m (f i))
    (m_top : ∀ s ∉ C, m s = ∞) {s : Set α} (hs : s ∈ C) :
    OuterMeasure.ofFunction m addContent_empty s = m s :=
  OuterMeasure.ofFunction_eq_of_mono_of_subadditive hC m addContent_empty
    (fun _ _ ↦ addContent_mono hC) m_sigma_subadd m_top hs

end OfFunction

end OuterMeasure

theorem inducedOuterMeasure_eq_iInf_mem (hC : ∅ ∈ C) (m : ∀ s : Set α, s ∈ C → ℝ≥0∞)
    (m_empty : m ∅ hC = 0) (s : Set α) :
    inducedOuterMeasure m hC m_empty s =
      ⨅ (f : ℕ → Set α) (hf : ∀ i, f i ∈ C) (_ : s ⊆ ⋃ i, f i), ∑' i, m (f i) (hf i) := by
  rw [inducedOuterMeasure,
    OuterMeasure.ofFunction_eq_iInf_mem s (extend m) _ fun s hs ↦ extend_eq_top m hs]
  simp_rw [← extend_eq m]

theorem inducedOuterMeasure_eq_of_add_of_subadditive (hC : IsSetSemiring C)
    (m : ∀ s : Set α, s ∈ C → ℝ≥0∞) (m_empty : m ∅ hC.empty_mem = 0)
    (m_add : ∀ (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (_h_dis : PairwiseDisjoint (I : Set (Set α)) id)
        (h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) h_mem = ∑ u : I, m u (h_ss u.prop))
    (m_sigma_subadd : ∀ ⦃f : ℕ → Set α⦄ (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C),
        m (⋃ i, f i) hf_Union ≤ ∑' i, m (f i) (hf i))
    {s : Set α} (hs : s ∈ C) :
    inducedOuterMeasure m hC.empty_mem m_empty s = m s hs :=
  (OuterMeasure.ofFunction_eq_of_add_of_subadditive hC (extend m) _ (extend_sUnion_eq_sum m m_add)
      (extend_sum_le m m_sigma_subadd) (fun _ hs ↦ extend_eq_top m hs) hs).trans
    (extend_eq m hs)

theorem caratheodory_semiring_extension' (hC : IsSetSemiring C) (m : Set α → ℝ≥0∞)
    (m_empty : m ∅ = 0)
    (m_add : ∀ (I : Finset (Set α)) (_h_ss : ↑I ⊆ C) (_ : PairwiseDisjoint (I : Set (Set α)) id)
      (_h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) = ∑ u in I, m u)
    (m_top : ∀ s ∉ C, m s = ∞) {s : Set α} (hs : s ∈ C) :
    OuterMeasure.IsCaratheodory (OuterMeasure.ofFunction m m_empty) s := by
  rw [OuterMeasure.isCaratheodory_iff_le']
  intro t
  conv_rhs => rw [OuterMeasure.ofFunction_eq_iInf_mem _ _ m_empty m_top]
  refine le_iInf fun f ↦ le_iInf fun hf ↦ le_iInf fun hf_subset ↦ ?_
  let A : ℕ → Finset (Set α) := fun i ↦ hC.diffFinset (hf i) (hC.inter_mem _ (hf i) _ hs)
  have h_diff_eq_sUnion i : f i \ s = ⋃₀ A i := by simp [A, IsSetSemiring.sUnion_diffFinset]
  have h_m_eq i : m (f i) = m (f i ∩ s) + ∑ u in A i, m u :=
    hC.eq_add_diffFinset_of_subset m m_add (hC.inter_mem _ (hf i) _ hs) (hf i)
      inter_subset_left
  simp_rw [h_m_eq]
  rw [tsum_add ENNReal.summable ENNReal.summable]
  refine add_le_add ?_ ?_
  · refine iInf_le_of_le (fun i ↦ f i ∩ s) <| iInf_le_of_le ?_ le_rfl
    rw [← iUnion_inter]
    exact Set.inter_subset_inter_left _ hf_subset
  · -- todo: explain that business with `e` and `g'`
    let e : ℕ ≃ ℕ × ℕ := (Denumerable.eqv (ℕ × ℕ)).symm
    let g' : ℕ × ℕ → Set α := fun n ↦
      if h : n.2 < (A n.1).card then (A n.1).ordered ⟨n.2, h⟩ else ∅
    have h_sum_sum : ∑' i, ∑ u in A i, m u = ∑' n, m (g' (e n)) := by
      have h1 i : ∑ u in A i, m u = ∑' n, m (g' ⟨i, n⟩) := by
        rw [← sum_ordered]
        let e_fin_range : Fin (A i).card ≃ Finset.range (A i).card :=
          { toFun := fun j ↦ ⟨j, Finset.mem_range.mpr j.2⟩
            invFun := fun j ↦ ⟨j, Finset.mem_range.mp j.2⟩
            left_inv := fun j ↦ by simp only [Subtype.coe_mk, Fin.eta]
            right_inv := fun j ↦ by simp only [Fin.val_mk, Subtype.coe_eta] }
        rw [Fintype.sum_equiv e_fin_range (fun j ↦ m (Finset.ordered (A i) j)) fun j ↦
            m (Finset.ordered (A i) (e_fin_range.symm j))]
        swap; · intro j; simp only [Equiv.symm_apply_apply]
        have : ∑' n, m (g' (i, n)) =
            ∑' n : ((Finset.range (A i).card : Finset ℕ) : Set ℕ), m (g' (i, n)) := by
          rw [tsum_subtype ((Finset.range (A i).card : Finset ℕ) : Set ℕ) fun n ↦ m (g' (i, n))]
          congr with n
          rw [Set.indicator_apply]
          split_ifs with h_lt
          · simp only [h_lt, mem_setOf_eq, if_true]
          · have : ¬ (i, n).snd < (A (i, n).fst).card := by simpa using h_lt
            simp only [this, not_false_eq_true, dif_neg, m_empty, g']
        rw [this, Finset.tsum_subtype' (Finset.range (A i).card) fun n ↦ m (g' (i, n)),
          ← Finset.sum_coe_sort (Finset.range (A i).card)]
        congr with j
        simp only [g']
        rw [dif_pos]
        · congr
        · exact Finset.mem_range.mp j.2
      simp_rw [h1]
      rw [← ENNReal.tsum_prod' (f := fun p ↦ m (g' p)),
        ← tsum_range (fun n ↦ m (g' n)) e.injective, Equiv.range_eq_univ,
        tsum_univ fun n ↦ m (g' n)]
    have h_Union : (⋃ i, g' (e i)) = (⋃ i, f i) \ s := by
      suffices ⋃ x, g' x = ⋃ i, f i \ s by
        rw [iUnion_diff, ← biUnion_range, Equiv.range_eq_univ]
        simpa only [Set.mem_univ, iUnion_true]
      simp only [g', iUnion_dite, iUnion_empty,
        Set.union_empty, h_diff_eq_sUnion]
      ext x
      simp only [← iUnion_ordered, mem_iUnion, Prod.exists]
      constructor
      · rintro ⟨a, b, h, h_mem⟩
        exact ⟨a, ⟨b, h⟩, h_mem⟩
      · rintro ⟨a, ⟨b, h⟩, h_mem⟩
        exact ⟨a, b, h, h_mem⟩
    rw [h_sum_sum]
    refine iInf_le_of_le _ (iInf_le_of_le ?_ le_rfl)
    rw [h_Union]
    exact diff_subset_diff hf_subset subset_rfl

theorem caratheodory_semiring_extension (hC : IsSetSemiring C) (m : ∀ s : Set α, s ∈ C → ℝ≥0∞)
    (m_empty : m ∅ hC.empty_mem = 0)
    (m_add : ∀ (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (_h_dis : PairwiseDisjoint (I : Set (Set α)) id)
        (h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) h_mem = ∑ u : I, m u (h_ss u.prop))
    {s : Set α} (hs : s ∈ C) :
    (inducedOuterMeasure m hC.empty_mem m_empty).IsCaratheodory s :=
  caratheodory_semiring_extension' hC (extend m) _ (extend_sUnion_eq_sum m m_add)
    (fun _ hs ↦ extend_eq_top m hs) hs

/-- Construct a measure from a sigma-subadditive function on a semiring. This
measure is defined on the associated Carathéodory sigma-algebra. -/
noncomputable def Measure.ofAddSubaddCaratheodory (hC : IsSetSemiring C)
    (m : ∀ s : Set α, s ∈ C → ℝ≥0∞) (m_empty : m ∅ hC.empty_mem = 0)
    (m_add : ∀ (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (_h_dis : PairwiseDisjoint (I : Set (Set α)) id)
      (h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) h_mem = ∑ u : I, m u (h_ss u.prop))
    (m_sigma_subadd : ∀ ⦃f : ℕ → Set α⦄ (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C),
      m (⋃ i, f i) hf_Union ≤ ∑' i, m (f i) (hf i)) :
    @Measure α (inducedOuterMeasure m hC.empty_mem m_empty).caratheodory :=
  letI : MeasurableSpace α := (inducedOuterMeasure m hC.empty_mem m_empty).caratheodory
  { inducedOuterMeasure m hC.empty_mem m_empty with
    m_iUnion := fun f hf hd ↦ OuterMeasure.iUnion_eq_of_caratheodory _ hf hd
    trim_le := by
      apply le_inducedOuterMeasure.mpr fun s hs ↦ ?_
      have hs_meas : MeasurableSet[(inducedOuterMeasure m hC.empty_mem m_empty).caratheodory] s := by
        show (inducedOuterMeasure m hC.empty_mem m_empty).IsCaratheodory s
        exact caratheodory_semiring_extension hC m m_empty m_add hs
      rw [OuterMeasure.trim_eq _ hs_meas,
        inducedOuterMeasure_eq_of_add_of_subadditive hC m m_empty m_add m_sigma_subadd hs] }

theorem Measure.ofAddSubaddCaratheodory_eq_inducedOuterMeasure (hC : IsSetSemiring C)
    (m : ∀ s : Set α, s ∈ C → ℝ≥0∞)
    (m_empty : m ∅ hC.empty_mem = 0)
    (m_add : ∀ (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (_h_dis : PairwiseDisjoint (I : Set (Set α)) id)
        (h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) h_mem = ∑ u : I, m u (h_ss u.prop))
    (m_sigma_subadd : ∀ ⦃f : ℕ → Set α⦄ (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C),
        m (⋃ i, f i) hf_Union ≤ ∑' i, m (f i) (hf i))
    (s : Set α) :
    Measure.ofAddSubaddCaratheodory hC m m_empty m_add m_sigma_subadd s
      = inducedOuterMeasure m hC.empty_mem m_empty s := rfl

theorem Measure.ofAddSubaddCaratheodory_eq (hC : IsSetSemiring C) (m : ∀ s : Set α, s ∈ C → ℝ≥0∞)
    (m_empty : m ∅ hC.empty_mem = 0)
    (m_add : ∀ (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (_h_dis : PairwiseDisjoint (I : Set (Set α)) id)
        (h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) h_mem = ∑ u : I, m u (h_ss u.prop))
    (m_sigma_subadd : ∀ ⦃f : ℕ → Set α⦄ (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C),
        m (⋃ i, f i) hf_Union ≤ ∑' i, m (f i) (hf i))
    {s : Set α} (hs : s ∈ C) :
    Measure.ofAddSubaddCaratheodory hC m m_empty m_add m_sigma_subadd s = m s hs :=
  inducedOuterMeasure_eq_of_add_of_subadditive hC m m_empty m_add m_sigma_subadd hs

theorem isCaratheodory_generateFrom (hC : IsSetSemiring C) (m : ∀ s : Set α, s ∈ C → ℝ≥0∞)
    (m_empty : m ∅ hC.empty_mem = 0)
    (m_add : ∀ (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (_h_dis : PairwiseDisjoint (I : Set (Set α)) id)
        (h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) h_mem = ∑ u : I, m u (h_ss u.prop))
    (s : Set α) (hs : MeasurableSet[MeasurableSpace.generateFrom C] s) :
    (inducedOuterMeasure m hC.empty_mem m_empty).IsCaratheodory s := by
  apply MeasurableSpace.generateFrom_induction
  · exact fun _ ↦ caratheodory_semiring_extension hC m m_empty m_add
  · exact OuterMeasure.isCaratheodory_empty _
  · exact fun _ ↦ OuterMeasure.isCaratheodory_compl _
  · exact fun _ hf ↦ OuterMeasure.isCaratheodory_iUnion hf
  · exact hs

/-- Construct a measure from a sigma-subadditive function on a semiring, assuming the semiring
generates a given measurable structure. The measure is defined on this measurable structure. -/
noncomputable def Measure.ofAddSubadd [mα : MeasurableSpace α] (hC : IsSetSemiring C)
    (hC_gen : MeasurableSpace.generateFrom C = mα) (m : ∀ s : Set α, s ∈ C → ℝ≥0∞)
    (m_empty : m ∅ hC.empty_mem = 0)
    (m_add : ∀ (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (_h_dis : PairwiseDisjoint (I : Set (Set α)) id)
        (h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) h_mem = ∑ u : I, m u (h_ss u.prop))
    (m_sigma_subadd : ∀ ⦃f : ℕ → Set α⦄ (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C),
      m (⋃ i, f i) hf_Union ≤ ∑' i, m (f i) (hf i)) :
    Measure α :=
  (Measure.ofAddSubaddCaratheodory hC m m_empty m_add m_sigma_subadd).trim
    (by rw [← hC_gen]; exact isCaratheodory_generateFrom hC m m_empty m_add)

theorem Measure.ofAddSubadd_eq [mα : MeasurableSpace α] (hC : IsSetSemiring C)
    (hC_gen : MeasurableSpace.generateFrom C = mα) (m : ∀ s : Set α, s ∈ C → ℝ≥0∞)
    (m_empty : m ∅ hC.empty_mem = 0)
    (m_add : ∀ (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (_h_dis : PairwiseDisjoint (I : Set (Set α)) id)
        (h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) h_mem = ∑ u : I, m u (h_ss u.prop))
    (m_sigma_subadd : ∀ ⦃f : ℕ → Set α⦄ (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C),
        m (⋃ i, f i) hf_Union ≤ ∑' i, m (f i) (hf i))
    {s : Set α} (hs : s ∈ C) :
    Measure.ofAddSubadd hC hC_gen m m_empty m_add m_sigma_subadd s = m s hs := by
  rw [Measure.ofAddSubadd, trim_measurableSet_eq]
  · exact Measure.ofAddSubaddCaratheodory_eq hC m m_empty m_add m_sigma_subadd hs
  · rw [← hC_gen]; exact MeasurableSpace.measurableSet_generateFrom hs

/-- Construct a measure from a sigma-subadditive content on a semiring, assuming the semiring
generates a given measurable structure. The measure is defined on this measurable structure. -/
noncomputable def Measure.ofAddContent [mα : MeasurableSpace α] (hC : IsSetSemiring C)
    (hC_gen : MeasurableSpace.generateFrom C = mα) (m : AddContent C)
    (m_sigma_subadd : ∀ ⦃f : ℕ → Set α⦄ (_hf : ∀ i, f i ∈ C) (_hf_Union : (⋃ i, f i) ∈ C),
        m (⋃ i, f i) ≤ ∑' i, m (f i)) :
    Measure α :=
  Measure.ofAddSubadd hC hC_gen (fun s _ ↦ m s) addContent_empty (fun I hI hI_disj hI_sUnion ↦
    (addContent_sUnion hI hI_disj hI_sUnion).trans (by rw [Finset.sum_coe_sort]))
    m_sigma_subadd

theorem Measure.ofAddContent_eq [mα : MeasurableSpace α] (hC : IsSetSemiring C)
    (hC_gen : MeasurableSpace.generateFrom C = mα) (m : AddContent C)
    (m_sigma_subadd : ∀ ⦃f : ℕ → Set α⦄ (_hf : ∀ i, f i ∈ C) (_hf_Union : (⋃ i, f i) ∈ C),
        m (⋃ i, f i) ≤ ∑' i, m (f i))
    {s : Set α} (hs : s ∈ C) :
    Measure.ofAddContent hC hC_gen m m_sigma_subadd s = m s :=
  Measure.ofAddSubadd_eq _ _ _ _ _ _ hs

end MeasureTheory
