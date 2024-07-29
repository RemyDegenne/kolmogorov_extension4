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

theorem ofFunction_addContent_eq (hC : IsSetSemiring C) (m : AddContent C)
    (m_sigma_subadd : ∀ ⦃f : ℕ → Set α⦄ (_hf : ∀ i, f i ∈ C) (_hf_Union : (⋃ i, f i) ∈ C),
      m (⋃ i, f i) ≤ ∑' i, m (f i))
    (m_top : ∀ s ∉ C, m s = ∞) {s : Set α} (hs : s ∈ C) :
    OuterMeasure.ofFunction m addContent_empty s = m s := by
  refine le_antisymm (OuterMeasure.ofFunction_le s) ?_
  rw [ofFunction_eq_iInf_mem s m addContent_empty m_top]
  refine le_iInf fun f ↦ le_iInf fun hf ↦ le_iInf fun hs_subset ↦ ?_
  calc m s = m (s ∩ ⋃ i, f i) := by rw [inter_eq_self_of_subset_left hs_subset]
    _ = m (⋃ i, s ∩ f i) := by rw [inter_iUnion]
    _ ≤ ∑' i, m (s ∩ f i) := by
      refine m_sigma_subadd (fun i ↦ hC.inter_mem _ hs _ (hf i)) ?_
      rwa [← inter_iUnion, inter_eq_self_of_subset_left hs_subset]
    _ ≤ ∑' i, m (f i) := by
      refine tsum_le_tsum (fun i ↦ ?_) ENNReal.summable ENNReal.summable
      exact addContent_mono hC (hC.inter_mem _ hs _ (hf i)) (hf i) Set.inter_subset_right

end OfFunction

end OuterMeasure

theorem inducedOuterMeasure_eq_iInf_mem (hC : ∅ ∈ C) (m : ∀ s : Set α, s ∈ C → ℝ≥0∞)
    (m_empty : m ∅ hC = 0) (s : Set α) :
    inducedOuterMeasure m hC m_empty s =
      ⨅ (f : ℕ → Set α) (hf : ∀ i, f i ∈ C) (_ : s ⊆ ⋃ i, f i), ∑' i, m (f i) (hf i) := by
  rw [inducedOuterMeasure,
    OuterMeasure.ofFunction_eq_iInf_mem s (extend m) _ fun s hs ↦ extend_eq_top m hs]
  simp_rw [← extend_eq m]

theorem inducedOuterMeasure_addContent_of_subadditive (hC : IsSetSemiring C) (m : AddContent C)
    (m_sigma_subadd : ∀ ⦃f : ℕ → Set α⦄ (_hf : ∀ i, f i ∈ C) (_hf_Union : (⋃ i, f i) ∈ C),
      m (⋃ i, f i) ≤ ∑' i, m (f i))
    {s : Set α} (hs : s ∈ C) :
    inducedOuterMeasure (fun x _ ↦ m x) hC.empty_mem addContent_empty s = m s := by
  suffices inducedOuterMeasure (fun x _ ↦ m x) hC.empty_mem addContent_empty s = m.extend hC s by
    rwa [m.extend_eq hC hs] at this
  refine Eq.trans ?_ (OuterMeasure.ofFunction_addContent_eq hC (m.extend hC) ?_ ?_ hs)
  · rw [inducedOuterMeasure]
    congr
  · intro f hf hf_mem
    rw [m.extend_eq hC hf_mem]
    refine (m_sigma_subadd hf hf_mem).trans_eq ?_
    congr with i
    rw [m.extend_eq hC (hf i)]
  · exact fun _ ↦ m.extend_eq_top _

theorem caratheodory_semiring_extension' (hC : IsSetSemiring C) (m : AddContent C)
    (m_top : ∀ s ∉ C, m s = ∞) {s : Set α} (hs : s ∈ C) :
    (OuterMeasure.ofFunction m addContent_empty).IsCaratheodory s := by
  rw [OuterMeasure.isCaratheodory_iff_le']
  intro t
  conv_rhs => rw [OuterMeasure.ofFunction_eq_iInf_mem _ _ addContent_empty m_top]
  refine le_iInf fun f ↦ le_iInf fun hf ↦ le_iInf fun hf_subset ↦ ?_
  let A : ℕ → Finset (Set α) := fun i ↦ hC.diffFinset (hf i) (hC.inter_mem _ (hf i) _ hs)
  have h_diff_eq_sUnion i : f i \ s = ⋃₀ A i := by simp [A, IsSetSemiring.sUnion_diffFinset]
  have h_m_eq i : m (f i) = m (f i ∩ s) + ∑ u in A i, m u :=
    hC.eq_add_diffFinset_of_subset m (fun _ ↦ addContent_sUnion) (hC.inter_mem _ (hf i) _ hs) (hf i)
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
            simp only [this, not_false_eq_true, dif_neg, addContent_empty, g']
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

theorem caratheodory_semiring_extension (hC : IsSetSemiring C) (m : AddContent C)
    {s : Set α} (hs : s ∈ C) :
    (inducedOuterMeasure (fun x _ ↦ m x) hC.empty_mem addContent_empty).IsCaratheodory s :=
  caratheodory_semiring_extension' hC (m.extend hC) (fun _ ↦ m.extend_eq_top hC) hs

theorem isCaratheodory_generateFrom (hC : IsSetSemiring C) (m : AddContent C)
    (s : Set α) (hs : MeasurableSet[MeasurableSpace.generateFrom C] s) :
    (inducedOuterMeasure (fun x _ ↦ m x) hC.empty_mem addContent_empty).IsCaratheodory s := by
  apply MeasurableSpace.generateFrom_induction
  · exact fun _ ↦ caratheodory_semiring_extension hC m
  · exact OuterMeasure.isCaratheodory_empty _
  · exact fun _ ↦ OuterMeasure.isCaratheodory_compl _
  · exact fun _ hf ↦ OuterMeasure.isCaratheodory_iUnion hf
  · exact hs

/-- Construct a measure from a sigma-subadditive function on a semiring. This
measure is defined on the associated Carathéodory sigma-algebra. -/
noncomputable def Measure.ofAddContentCaratheodory (hC : IsSetSemiring C)
    (m : AddContent C)
    (m_sigma_subadd : ∀ ⦃f : ℕ → Set α⦄ (_hf : ∀ i, f i ∈ C) (_hf_Union : (⋃ i, f i) ∈ C),
      m (⋃ i, f i) ≤ ∑' i, m (f i)) :
    @Measure α (inducedOuterMeasure (fun x _ ↦ m x) hC.empty_mem addContent_empty).caratheodory :=
  letI : MeasurableSpace α :=
    (inducedOuterMeasure (fun x _ ↦ m x) hC.empty_mem addContent_empty).caratheodory
  { inducedOuterMeasure (fun x _ ↦ m x) hC.empty_mem addContent_empty with
    m_iUnion := fun f hf hd ↦ OuterMeasure.iUnion_eq_of_caratheodory _ hf hd
    trim_le := by
      apply le_inducedOuterMeasure.mpr fun s hs ↦ ?_
      have hs_meas : MeasurableSet[(inducedOuterMeasure (fun x _ ↦ m x) hC.empty_mem
          addContent_empty).caratheodory] s := by
        show (inducedOuterMeasure (fun x _ ↦ m x) hC.empty_mem addContent_empty).IsCaratheodory s
        exact caratheodory_semiring_extension hC m hs
      rw [OuterMeasure.trim_eq _ hs_meas,
        inducedOuterMeasure_addContent_of_subadditive hC m m_sigma_subadd hs] }

theorem Measure.ofAddContentCaratheodory_eq_inducedOuterMeasure (hC : IsSetSemiring C)
    (m : AddContent C)
    (m_sigma_subadd : ∀ ⦃f : ℕ → Set α⦄ (_hf : ∀ i, f i ∈ C) (_hf_Union : (⋃ i, f i) ∈ C),
        m (⋃ i, f i) ≤ ∑' i, m (f i))
    (s : Set α) :
    Measure.ofAddContentCaratheodory hC m m_sigma_subadd s
      = inducedOuterMeasure (fun x _ ↦ m x) hC.empty_mem addContent_empty s := rfl

theorem Measure.ofAddContentCaratheodory_eq (hC : IsSetSemiring C) (m : AddContent C)
    (m_sigma_subadd : ∀ ⦃f : ℕ → Set α⦄ (_hf : ∀ i, f i ∈ C) (_hf_Union : (⋃ i, f i) ∈ C),
        m (⋃ i, f i)≤ ∑' i, m (f i))
    {s : Set α} (hs : s ∈ C) :
    Measure.ofAddContentCaratheodory hC m m_sigma_subadd s = m s :=
  inducedOuterMeasure_addContent_of_subadditive hC m  m_sigma_subadd hs

/-- Construct a measure from a sigma-subadditive content on a semiring, assuming the semiring
generates a given measurable structure. The measure is defined on this measurable structure. -/
noncomputable def Measure.ofAddContent [mα : MeasurableSpace α] (hC : IsSetSemiring C)
    (hC_gen : MeasurableSpace.generateFrom C = mα) (m : AddContent C)
    (m_sigma_subadd : ∀ ⦃f : ℕ → Set α⦄ (_hf : ∀ i, f i ∈ C) (_hf_Union : (⋃ i, f i) ∈ C),
      m (⋃ i, f i) ≤ ∑' i, m (f i)) :
    Measure α :=
  (Measure.ofAddContentCaratheodory hC m m_sigma_subadd).trim
    (by rw [← hC_gen]; exact isCaratheodory_generateFrom hC m)

theorem Measure.ofAddContent_eq [mα : MeasurableSpace α] (hC : IsSetSemiring C)
    (hC_gen : MeasurableSpace.generateFrom C = mα) (m : AddContent C)
    (m_sigma_subadd : ∀ ⦃f : ℕ → Set α⦄ (_hf : ∀ i, f i ∈ C) (_hf_Union : (⋃ i, f i) ∈ C),
        m (⋃ i, f i) ≤ ∑' i, m (f i))
    {s : Set α} (hs : s ∈ C) :
    Measure.ofAddContent hC hC_gen m m_sigma_subadd s = m s := by
  rw [Measure.ofAddContent, trim_measurableSet_eq]
  · exact Measure.ofAddContentCaratheodory_eq hC m m_sigma_subadd hs
  · rw [← hC_gen]; exact MeasurableSpace.measurableSet_generateFrom hs

end MeasureTheory
