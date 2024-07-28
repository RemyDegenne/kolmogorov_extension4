/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
import KolmogorovExtension4.AuxLemmas
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.MetricSpace.Polish

open Set MeasureTheory

open scoped ENNReal Topology NNReal

section Misc

variable {α : Type*}

namespace Set

-- actually not used anymore
theorem monotone_iUnion {s : ℕ → Set α} (hs : Monotone s) (n : ℕ) : (⋃ m ≤ n, s m) = s n := by
  apply subset_antisymm
  · exact iUnion_subset fun m ↦ iUnion_subset fun hm ↦ hs hm
  · exact subset_iUnion_of_subset n (subset_iUnion_of_subset le_rfl subset_rfl)

-- actually not used anymore
theorem antitone_iInter {s : ℕ → Set α} (hs : Antitone s) (n : ℕ) : (⋂ m ≤ n, s m) = s n := by
  apply subset_antisymm
  · exact iInter_subset_of_subset n (iInter_subset _ le_rfl)
  · exact subset_iInter fun i ↦ subset_iInter fun hin ↦ hs hin

theorem eq_iInter_iInter {s : ℕ → Set α} : (⋂ n, s n) = ⋂ (n : ℕ) (m : ℕ) (_ : m ≤ n), s m := by
  ext x; simp only [Set.mem_iInter]; exact ⟨fun h _ k _ ↦ h k, fun h i ↦ h i i le_rfl⟩

end Set

namespace ENNReal

theorem tendsto_atTop_zero_iff_of_antitone (f : ℕ → ℝ≥0∞) (hf : Antitone f) :
    Filter.Tendsto f Filter.atTop (𝓝 0) ↔ ∀ ε, 0 < ε → ∃ n : ℕ, f n ≤ ε := by
  rw [ENNReal.tendsto_atTop_zero]
  refine ⟨fun h ↦ fun ε hε ↦ ?_, fun h ↦ fun ε hε ↦ ?_⟩
  · obtain ⟨n, hn⟩ := h ε hε
    exact ⟨n, hn n le_rfl⟩
  · obtain ⟨n, hn⟩ := h ε hε
    exact ⟨n, fun m hm ↦ (hf hm).trans hn⟩

theorem tendsto_atTop_of_antitone (f : ℕ → ℝ≥0∞) (hf : Antitone f) :
    Filter.Tendsto f Filter.atTop (𝓝 0) ↔ ∀ ε, 0 < ε → ∃ n : ℕ, f n < ε := by
  rw [ENNReal.tendsto_atTop_zero_iff_of_antitone f hf]
  constructor <;> intro h ε hε
  have hε' : (min 1 (ε / 2)) > 0 := by
    simp only [ge_iff_le, gt_iff_lt, lt_min_iff, zero_lt_one, div_pos_iff, ne_eq, and_true,
      true_and]
    simp only [two_ne_top, not_false_eq_true, and_true]
    intro g
    exact hε.ne g.symm
  · obtain ⟨n, hn⟩ := h (min 1 (ε / 2)) hε'
    · refine ⟨n, hn.trans_lt ?_⟩
      by_cases hε_top : ε = ∞
      · rw [hε_top]
        exact (min_le_left _ _).trans_lt ENNReal.one_lt_top
      refine (min_le_right _ _).trans_lt ?_
      rw [ENNReal.div_lt_iff (Or.inr hε.ne') (Or.inr hε_top)]
      conv_lhs => rw [← mul_one ε]
      rw [ENNReal.mul_lt_mul_left hε.ne' hε_top]
      norm_num
  · obtain ⟨n, hn⟩ := h ε hε
    exact ⟨n, hn.le⟩

end ENNReal

end Misc

variable {α : Type*}

namespace MeasureTheory

variable [MeasurableSpace α]

/-- Some version of continuity of a measure in the emptyset using a decreasing sequence of sets. -/
theorem tendsto_zero_measure_of_antitone (μ : Measure α) [IsFiniteMeasure μ] {s : ℕ → Set α}
    (hs1 : ∀ n, MeasurableSet (s n)) (hs2 : Antitone s) (hs3 : (⋂ n, s n) = ∅) :
    Filter.Tendsto (fun n ↦ μ (s n)) Filter.atTop (𝓝 0) := by
  convert MeasureTheory.tendsto_measure_iInter hs1 hs2 _
  · rw [hs3]
    exact measure_empty.symm
  · exact ⟨0, measure_ne_top μ _⟩

theorem tendsto_zero_measure_of_antitone' (μ : Measure α) [IsFiniteMeasure μ] {s : ℕ → Set α}
    (hs1 : ∀ n, MeasurableSet (s n)) (hs2 : Antitone s) (hs3 : (⋂ n, s n) = ∅)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ n, μ (s n) < ε :=
  (ENNReal.tendsto_atTop_of_antitone (fun n ↦ μ (s n))
    (fun _ _ h12 ↦ measure_mono (hs2 h12))).mp (tendsto_zero_measure_of_antitone μ hs1 hs2 hs3)
    ε hε

/-- Some version of continuity of a measure in the emptyset using the intersection along a set of
sets. -/
theorem continuous_at_emptyset_inter (μ : Measure α) [IsFiniteMeasure μ] (S : ℕ → Set α)
    (hS2 : ∀ n, MeasurableSet (S n)) (hS3 : ⋂ n, S n = ∅) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ m, μ (⋂ n ≤ m, S n) < ε := by
  let s m := (Accumulate (fun n ↦ (S n)ᶜ) m)ᶜ
  have hs_anti : Antitone s := by
    intro i j hij
    simp only [compl_le_compl_iff_le, le_eq_subset, s]
    exact monotone_accumulate hij
  have hs_iInter : ⋂ n, s n = ∅ := by
    simp only [s]
    rw [← hS3, ← compl_iUnion, iUnion_accumulate, compl_iUnion]
    simp_rw [compl_compl]
  have hs_meas n : MeasurableSet (s n) := (MeasurableSet.accumulate (fun m ↦ (hS2 m).compl) n).compl
  suffices ∃ m, μ (s m) < ε by
    obtain ⟨m, hm⟩ := this
    refine ⟨m, ?_⟩
    simpa [s, accumulate_def] using hm
  suffices Filter.Tendsto (fun m ↦ μ (s m)) Filter.atTop (𝓝 0) by
    rw [ENNReal.tendsto_atTop_of_antitone] at this
    · exact this ε hε
    · exact fun _ _ h ↦ measure_mono (hs_anti h)
  convert tendsto_measure_iInter hs_meas hs_anti ⟨0, measure_ne_top μ _⟩
  simp [hs_iInter]

end MeasureTheory

section Topology

namespace UniformSpace

lemma _root_.MeasurableSet.ball {_ : MeasurableSpace α} (x : α)
    {s : Set (α × α)} (hs : MeasurableSet s) :
    MeasurableSet (UniformSpace.ball x s) := measurable_prod_mk_left hs

/-- Given a family of sets `s' n` and a family of entourages `V n` of the diagonal, the
intersection over `n` of the `V n`-neighborhood of `s' n`. Designed to be relatively compact
when the `s' n` are finite and `V n` tends to the diagonal. -/
def interUnionBalls (s' : ℕ → Set α) (V : ℕ → Set (α × α)) : Set α :=
  ⋂ n, ⋃ x ∈ s' n, UniformSpace.ball x (Prod.swap ⁻¹' V n)

theorem totallyBounded_interUnionBalls [UniformSpace α] {p : ℕ → Prop} {U : ℕ → Set (α × α)}
    (H : (uniformity α).HasBasis p U) (s' : ℕ → Finset α) :
    TotallyBounded (interUnionBalls (fun n ↦ ↑(s' n)) U) := by
  rw [Filter.HasBasis.totallyBounded_iff H]
  intro i _
  let A := interUnionBalls (fun n ↦ (s' n : Set α)) U
  have hA2 : A ⊆ ⋃ x ∈ s' i, UniformSpace.ball x (Prod.swap ⁻¹' U i) :=
    fun x hx ↦ Set.mem_iInter.1 hx i
  refine ⟨s' i, Finset.finite_toSet (s' i), ?_⟩
  simp only [Finset.mem_coe]
  simp only [UniformSpace.ball] at hA2
  intro x hx
  let B x := Prod.mk x ⁻¹' (Prod.swap ⁻¹' U i)
  let C x := {y : α | (y, x) ∈ U i}
  have h : B = C := by ext x y; rfl
  change x ∈ ⋃ x ∈ s' i, C x
  rw [← h]
  exact hA2 hx

/-- The construction `interUnionBalls` is used to have a relatively compact set. -/
theorem isCompact_closure_interUnionBalls [UniformSpace α] {p : ℕ → Prop} {U : ℕ → Set (α × α)}
    (H : (uniformity α).HasBasis p U) [CompleteSpace α] (s' : ℕ → Finset α) :
    IsCompact (closure (interUnionBalls (fun n ↦ (s' n : Set α)) U)) := by
  rw [isCompact_iff_totallyBounded_isComplete]
  refine ⟨TotallyBounded.closure ?_, isClosed_closure.isComplete⟩
  exact totallyBounded_interUnionBalls H s'

theorem _root_.MeasureTheory.measure_compl_interUnionBalls_le {_ : MeasurableSpace α}
    (μ : Measure α) (s' : ℕ → Set α) (V : ℕ → Set (α × α)) :
    μ (UniformSpace.interUnionBalls s' V)ᶜ ≤
      ∑' n, μ (⋃ x ∈ s' n, UniformSpace.ball x (Prod.swap ⁻¹' V n))ᶜ := by
  rw [UniformSpace.interUnionBalls, Set.compl_iInter]
  exact measure_iUnion_le _

theorem _root_.MeasureTheory.measure_compl_interUnionBalls_lt {_ : MeasurableSpace α} (ε : ℝ≥0∞)
    (μ : Measure α) (s' : ℕ → Set α)
    (V : ℕ → Set (α × α)) (δ : ℕ → ℝ≥0∞)
    (hδ1 : ∀ n, μ (⋃ x ∈ s' n, UniformSpace.ball x (Prod.swap ⁻¹' V n))ᶜ ≤ δ n)
    (hδ3 : ∑' n, δ n < ε) :
    μ (UniformSpace.interUnionBalls s' V)ᶜ < ε :=
  ((measure_compl_interUnionBalls_le μ s' V).trans
    (ENNReal.tsum_le_tsum fun n ↦ hδ1 n)).trans_lt hδ3

end UniformSpace

end Topology

namespace MeasureTheory

variable [MeasurableSpace α] {μ : Measure α}

theorem innerRegularWRT_isCompact_closure_iff [TopologicalSpace α] [R1Space α] :
    μ.InnerRegularWRT (IsCompact ∘ closure) IsClosed ↔ μ.InnerRegularWRT IsCompact IsClosed := by
  constructor <;> intro h A hA r hr
  · rcases h hA r hr with ⟨K, ⟨hK1, hK2, hK3⟩⟩
    exact ⟨closure K, closure_minimal hK1 hA, hK2, hK3.trans_le (measure_mono subset_closure)⟩
  · rcases h hA r hr with ⟨K, ⟨hK1, hK2, hK3⟩⟩
    refine ⟨closure K, closure_minimal hK1 hA, ?_, ?_⟩
    · simpa only [closure_closure, Function.comp_apply] using hK2.closure
    · exact hK3.trans_le (measure_mono subset_closure)

lemma innerRegularWRT_isCompact_isClosed_iff_innerRegularWRT_isCompact_closure
    [TopologicalSpace α] [R1Space α] :
    μ.InnerRegularWRT (fun s ↦ IsCompact s ∧ IsClosed s) IsClosed
      ↔ μ.InnerRegularWRT (IsCompact ∘ closure) IsClosed := by
  constructor <;> intro h A hA r hr
  · obtain ⟨K, hK1, ⟨hK2, _⟩, hK4⟩ := h hA r hr
    refine ⟨K, hK1, ?_, hK4⟩
    simp only [closure_closure, Function.comp_apply]
    exact hK2.closure
  · obtain ⟨K, hK1, hK2, hK3⟩ := h hA r hr
    refine ⟨closure K, closure_minimal hK1 hA, ?_, ?_⟩
    · simpa only [isClosed_closure, and_true]
    · exact hK3.trans_le (measure_mono subset_closure)

lemma innerRegularWRT_isCompact_isClosed_iff [TopologicalSpace α] [R1Space α] :
    μ.InnerRegularWRT (fun s ↦ IsCompact s ∧ IsClosed s) IsClosed
      ↔ μ.InnerRegularWRT IsCompact IsClosed :=
  innerRegularWRT_isCompact_isClosed_iff_innerRegularWRT_isCompact_closure.trans
    innerRegularWRT_isCompact_closure_iff

theorem innerRegularWRT_of_exists_compl_lt {p q : Set α → Prop} (hpq : ∀ A B, p A → q B → p (A ∩ B))
    (hμ : ∀ ε, 0 < ε → ∃ K, p K ∧ μ Kᶜ < ε) :
    μ.InnerRegularWRT p q := by
  intro A hA r hr
  obtain ⟨K, hK, hK_subset, h_lt⟩ : ∃ K, p K ∧ K ⊆ A ∧ μ (A \ K) < μ A - r := by
    obtain ⟨K', hpK', hK'_lt⟩ := hμ (μ A - r) (tsub_pos_of_lt hr)
    refine ⟨K' ∩ A, hpq K' A hpK' hA, inter_subset_right, ?_⟩
    · refine (measure_mono fun x ↦ ?_).trans_lt hK'_lt
      simp only [diff_inter_self_eq_diff, mem_diff, mem_compl_iff, and_imp, imp_self, imp_true_iff]
  refine ⟨K, hK_subset, hK, ?_⟩
  have h_lt' : μ A - μ K < μ A - r := le_measure_diff.trans_lt h_lt
  exact lt_of_tsub_lt_tsub_left h_lt'

theorem innerRegularWRT_isCompact_closure_of_univ [TopologicalSpace α]
    (hμ : ∀ ε, 0 < ε → ∃ K, IsCompact (closure K) ∧ μ (Kᶜ) < ε) :
    μ.InnerRegularWRT (IsCompact ∘ closure) IsClosed := by
  refine innerRegularWRT_of_exists_compl_lt (fun s t hs ht ↦ ?_) hμ
  have : IsCompact (closure s ∩ t) := hs.inter_right ht
  refine this.of_isClosed_subset isClosed_closure ?_
  refine (closure_inter_subset_inter_closure _ _).trans_eq ?_
  rw [IsClosed.closure_eq ht]

theorem inner_regular_isCompact_is_closed_of_complete_countable' [UniformSpace α] [CompleteSpace α]
    [SecondCountableTopology α] [(uniformity α).IsCountablyGenerated]
    [OpensMeasurableSpace α] (P : Measure α) [IsFiniteMeasure P] (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ K, IsCompact (closure K) ∧ P Kᶜ < ε := by
  cases isEmpty_or_nonempty α
  case inl =>
    refine ⟨∅, by simp, ?_⟩
    rw [← Set.univ_eq_empty_iff.mpr]
    · simpa only [compl_univ, measure_empty, ENNReal.coe_pos] using hε
    · assumption
  case inr =>
    let seq := TopologicalSpace.denseSeq α
    have hseq_dense : DenseRange seq := TopologicalSpace.denseRange_denseSeq α
    obtain ⟨t : ℕ → Set (α × α),
        hto : ∀ i, t i ∈ (uniformity α).sets ∧ IsOpen (t i) ∧ SymmetricRel (t i),
        h_basis : (uniformity α).HasAntitoneBasis t⟩ :=
      (@uniformity_hasBasis_open_symmetric α _).exists_antitone_subbasis
    let f : ℕ → ℕ → Set α := fun n m ↦ UniformSpace.ball (seq m) (t n)
    have h_univ n : (⋃ m, f n m) = univ := hseq_dense.iUnion_uniformity_ball (hto n).1
    have h3 n (ε : ℝ≥0∞) (hε : 0 < ε) : ∃ m, P (⋃ m' ≤ m, f n m')ᶜ < ε := by
      simp only [compl_iUnion]
      refine continuous_at_emptyset_inter P _ (fun m ↦ ?_) ?_ hε
      · exact ((IsOpen.measurableSet (hto n).2.1).ball _).compl
      · rw [← compl_iUnion, h_univ, compl_univ]
    choose! s' s'bound using h3
    rcases ENNReal.exists_seq_pos_lt ε hε with ⟨δ, hδ1, hδ2⟩
    classical
    let u : ℕ → Finset α := fun n ↦ Finset.image seq (Finset.range (s' n (δ n) + 1))
    let A := UniformSpace.interUnionBalls (fun n ↦ (u n : Set α)) t
    refine ⟨A, UniformSpace.isCompact_closure_interUnionBalls h_basis.toHasBasis u, ?_⟩
    refine measure_compl_interUnionBalls_lt ε P (fun n ↦ ↑(u n)) t δ (fun n ↦ ?_) hδ2
    have h'' n : Prod.swap ⁻¹' t n = t n := SymmetricRel.eq (hto n).2.2
    simp only [Finset.mem_coe, compl_iUnion, h'', Finset.mem_image, Finset.mem_range, iInter_exists,
      biInter_and', iInter_iInter_eq_right, ge_iff_le, u, Nat.lt_succ_iff]
    simp only [compl_iUnion] at s'bound
    exact (s'bound n (δ n) (hδ1 n)).le

theorem innerRegularWRT_isCompact_closure_of_complete_countable [UniformSpace α] [CompleteSpace α]
    [SecondCountableTopology α] [(uniformity α).IsCountablyGenerated]
    [OpensMeasurableSpace α] (P : Measure α) [IsFiniteMeasure P] :
    P.InnerRegularWRT (IsCompact ∘ closure) IsClosed :=
  innerRegularWRT_isCompact_closure_of_univ
    (inner_regular_isCompact_is_closed_of_complete_countable' P)

theorem innerRegularWRT_isCompact_isClosed_of_complete_countable [UniformSpace α] [CompleteSpace α]
    [SecondCountableTopology α] [(uniformity α).IsCountablyGenerated]
    [OpensMeasurableSpace α] (P : Measure α) [IsFiniteMeasure P] :
    P.InnerRegularWRT (fun s ↦ IsCompact s ∧ IsClosed s) IsClosed := by
  rw [innerRegularWRT_isCompact_isClosed_iff_innerRegularWRT_isCompact_closure]
  exact innerRegularWRT_isCompact_closure_of_univ
    (inner_regular_isCompact_is_closed_of_complete_countable' P)

theorem innerRegularWRT_isCompact_of_complete_countable [UniformSpace α] [CompleteSpace α]
    [SecondCountableTopology α] [(uniformity α).IsCountablyGenerated]
    [OpensMeasurableSpace α] (P : Measure α) [IsFiniteMeasure P] :
    P.InnerRegularWRT IsCompact IsClosed := by
  rw [← innerRegularWRT_isCompact_closure_iff]
  exact innerRegularWRT_isCompact_closure_of_complete_countable P

theorem innerRegularWRT_isCompact_isClosed_isOpen_of_complete_countable [PseudoEMetricSpace α]
    [CompleteSpace α] [SecondCountableTopology α] [OpensMeasurableSpace α]
    (P : Measure α) [IsFiniteMeasure P] :
    P.InnerRegularWRT (fun s ↦ IsCompact s ∧ IsClosed s) IsOpen :=
  (innerRegularWRT_isCompact_isClosed_of_complete_countable P).trans
    (Measure.InnerRegularWRT.of_pseudoMetrizableSpace P)

theorem innerRegularWRT_isCompact_isOpen_of_complete_countable [PseudoEMetricSpace α]
    [CompleteSpace α] [SecondCountableTopology α] [OpensMeasurableSpace α]
    (P : Measure α) [IsFiniteMeasure P] :
    P.InnerRegularWRT IsCompact IsOpen :=
  (innerRegularWRT_isCompact_of_complete_countable P).trans
    (Measure.InnerRegularWRT.of_pseudoMetrizableSpace P)

lemma InnerRegularCompactLTTop_of_complete_countable [PseudoEMetricSpace α]
    [CompleteSpace α] [SecondCountableTopology α] [BorelSpace α]
    (P : Measure α) [IsFiniteMeasure P] :
    P.InnerRegularCompactLTTop := by
  refine ⟨Measure.InnerRegularWRT.measurableSet_of_isOpen ?_ ?_⟩
  · exact innerRegularWRT_isCompact_isOpen_of_complete_countable P
  · exact fun s t hs_compact ht_open ↦ hs_compact.inter_right ht_open.isClosed_compl

theorem innerRegular_isCompact_isClosed_measurableSet_of_complete_countable [PseudoEMetricSpace α]
    [CompleteSpace α] [SecondCountableTopology α] [BorelSpace α]
    (P : Measure α) [IsFiniteMeasure P] :
    P.InnerRegularWRT (fun s ↦ IsCompact s ∧ IsClosed s) MeasurableSet := by
  suffices P.InnerRegularWRT (fun s ↦ IsCompact s ∧ IsClosed s)
      fun s ↦ MeasurableSet s ∧ P s ≠ ∞ by
    convert this
    simp only [eq_iff_iff, iff_self_and]
    exact fun _ ↦ measure_ne_top P _
  refine Measure.InnerRegularWRT.measurableSet_of_isOpen ?_ ?_
  · exact innerRegularWRT_isCompact_isClosed_isOpen_of_complete_countable P
  · rintro s t ⟨hs_compact, hs_closed⟩ ht_open
    rw [diff_eq]
    exact ⟨hs_compact.inter_right ht_open.isClosed_compl,
      hs_closed.inter (isClosed_compl_iff.mpr ht_open)⟩

/-- On a Polish space, any finite measure is regular with respect to compact and closed sets. -/
theorem PolishSpace.innerRegular_isCompact_measurableSet [TopologicalSpace α] [PolishSpace α]
    [BorelSpace α] (μ : Measure α) [IsFiniteMeasure μ] :
    μ.InnerRegularWRT (fun s ↦ IsCompact s ∧ IsClosed s) MeasurableSet := by
  letI := upgradePolishSpace α
  exact innerRegular_isCompact_isClosed_measurableSet_of_complete_countable μ

end MeasureTheory
