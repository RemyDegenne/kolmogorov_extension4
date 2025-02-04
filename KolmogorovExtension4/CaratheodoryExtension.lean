/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
import Mathlib.MeasureTheory.Measure.Trim
import KolmogorovExtension4.Content

open Set

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} {C : Set (Set α)}

namespace OuterMeasure

section OfFunction

theorem ofFunction_addContent_eq (hC : IsSetSemiring C) (m : AddContent C)
    (m_sigma_subadd : ∀ ⦃f : ℕ → Set α⦄ (_hf : ∀ i, f i ∈ C) (_hf_Union : (⋃ i, f i) ∈ C),
      m (⋃ i, f i) ≤ ∑' i, m (f i))
    (m_top : ∀ s ∉ C, m s = ∞) {s : Set α} (hs : s ∈ C) :
    OuterMeasure.ofFunction m addContent_empty s = m s := by
  refine le_antisymm (OuterMeasure.ofFunction_le s) ?_
  rw [ofFunction_eq_iInf_mem _ _ m_top]
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

theorem inducedOuterMeasure_addContent_of_subadditive (hC : IsSetSemiring C) (m : AddContent C)
    (m_sigma_subadd : ∀ ⦃f : ℕ → Set α⦄ (_hf : ∀ i, f i ∈ C) (_hf_Union : (⋃ i, f i) ∈ C),
      m (⋃ i, f i) ≤ ∑' i, m (f i))
    {s : Set α} (hs : s ∈ C) :
    inducedOuterMeasure (fun x _ ↦ m x) hC.empty_mem addContent_empty s = m s := by
  suffices inducedOuterMeasure (fun x _ ↦ m x) hC.empty_mem addContent_empty s = m.extend hC s by
    rwa [m.extend_eq hC hs] at this
  refine Eq.trans ?_ (OuterMeasure.ofFunction_addContent_eq hC (m.extend hC) ?_ ?_ hs)
  · congr
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
  conv_rhs => rw [OuterMeasure.ofFunction_eq_iInf_mem _ _ m_top]
  refine le_iInf fun f ↦ le_iInf fun hf ↦ le_iInf fun hf_subset ↦ ?_
  let A : ℕ → Finset (Set α) := fun i ↦ hC.disjointOfDiff (hf i) (hC.inter_mem _ (hf i) _ hs)
  have h_diff_eq_sUnion i : f i \ s = ⋃₀ A i := by simp [A, IsSetSemiring.sUnion_disjointOfDiff]
  classical
  have h_m_eq i : m (f i) = m (f i ∩ s) + ∑ u ∈ A i, m u :=
    eq_add_disjointOfDiff_of_subset hC (hC.inter_mem _ (hf i) _ hs) (hf i) inter_subset_left
  simp_rw [h_m_eq]
  rw [tsum_add ENNReal.summable ENNReal.summable]
  refine add_le_add ?_ ?_
  · refine iInf_le_of_le (fun i ↦ f i ∩ s) <| iInf_le_of_le ?_ le_rfl
    rw [← iUnion_inter]
    exact Set.inter_subset_inter_left _ hf_subset
  · apply le_trans <| (OuterMeasure.ofFunction m addContent_empty).mono
      <| (iUnion_diff s f) ▸ diff_subset_diff_left hf_subset
    simp only [OuterMeasure.measureOf_eq_coe, A]
    apply le_trans <| measure_iUnion_le (μ := OuterMeasure.ofFunction m addContent_empty) (fun i ↦ f i \ s)
    refine ENNReal.tsum_le_tsum fun i ↦ ?_
    simp_rw [sUnion_eq_biUnion] at h_diff_eq_sUnion
    rw [h_diff_eq_sUnion]
    exact (measure_biUnion_finset_le (A i) id).trans
      (Finset.sum_le_sum <| fun b _ ↦ OuterMeasure.ofFunction_le (m_empty := addContent_empty) b)

theorem caratheodory_semiring_extension (hC : IsSetSemiring C) (m : AddContent C)
    {s : Set α} (hs : s ∈ C) :
    (inducedOuterMeasure (fun x _ ↦ m x) hC.empty_mem addContent_empty).IsCaratheodory s :=
  caratheodory_semiring_extension' hC (m.extend hC) (fun _ ↦ m.extend_eq_top hC) hs

theorem isCaratheodory_inducedOuterMeasure (hC : IsSetSemiring C) (m : AddContent C)
    (s : Set α) (hs : MeasurableSet[MeasurableSpace.generateFrom C] s) :
    (inducedOuterMeasure (fun x _ ↦ m x) hC.empty_mem addContent_empty).IsCaratheodory s := by
  induction hs with
  | basic u hu => exact caratheodory_semiring_extension hC m hu
  | empty => exact OuterMeasure.isCaratheodory_empty _
  | compl t _ h => exact OuterMeasure.isCaratheodory_compl _ h
  | iUnion f _ h => exact OuterMeasure.isCaratheodory_iUnion _ h

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
    (by rw [← hC_gen]; exact isCaratheodory_inducedOuterMeasure hC m)

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
