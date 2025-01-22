/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Order.CompletePartialOrder
import Mathlib

open Finset Set MeasureTheory Order Filter

open scoped ENNReal NNReal Topology

-- PR #15294
lemma Finset.sUnion_disjiUnion {α β : Type*} {f : α → Finset (Set β)} (I : Finset α)
    (hf : (I : Set α).PairwiseDisjoint f) :
    ⋃₀ (I.disjiUnion f hf : Set (Set β)) = ⋃ a ∈ I, ⋃₀ ↑(f a) := by
  ext
  simp only [coe_disjiUnion, mem_coe, Set.mem_sUnion, Set.mem_iUnion, exists_prop]
  tauto

/-- Subadditivity of the sum over a finset. -/
lemma Finset.sum_image_le_of_nonneg {ι α β : Type*} [DecidableEq α]
    [OrderedAddCommMonoid β] [SMulPosMono ℕ β]
    {J : Finset ι} {g : ι → α} {f : α → β} (hf : ∀ u ∈ J.image g, 0 ≤ f u) :
    ∑ u ∈ J.image g, f u ≤ ∑ u in J, f (g u) := by
  rw [sum_comp f g]
  refine sum_le_sum fun a hag ↦ ?_
  obtain ⟨i, hi, hig⟩ := Finset.mem_image.mp hag
  conv_lhs => rw [← one_nsmul (f a)]
  refine smul_le_smul_of_nonneg_right ?_ (hf a hag)
  rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, card_pos]
  exact ⟨i, mem_filter.mpr ⟨hi, hig⟩⟩


lemma Finset.sum_image_le_of_nonneg' {ι α : Type*} [DecidableEq α]
    {J : Finset ι} {g : ι → α} {f : α → ℝ≥0∞} (hf : ∀ u ∈ J.image g, 0 ≤ f u) :
    ∑ u in J.image g, f u ≤ ∑ u in J, f (g u) := by
  rw [sum_comp f g]
  refine sum_le_sum fun a hag ↦ ?_
  obtain ⟨i, hi, hig⟩ := Finset.mem_image.mp hag
  conv_lhs => rw [← one_nsmul (f a)]
  refine smul_le_smul_of_nonneg_right ?_ (hf a hag)
  rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, card_pos]
  exact ⟨i, mem_filter.mpr ⟨hi, hig⟩⟩

-- PR #15294
@[to_additive]
lemma Finset.prod_image_of_disjoint {α β : Type*} [PartialOrder α] [OrderBot α] [DecidableEq α]
    [CommMonoid β] {g : α → β}
    (hg_bot : g ⊥ = 1) {f : ι → α} {I : Finset ι} (hf_disj : (I : Set ι).PairwiseDisjoint f) :
    ∏ s in I.image f, g s = ∏ i in I, g (f i) := by
  rw [prod_image']
  intro n hnI
  by_cases hfn : f n = ⊥
  · simp only [hfn, hg_bot]
    refine (prod_eq_one fun i hi ↦ ?_).symm
    rw [mem_filter] at hi
    rw [hi.2, hg_bot]
  · classical
    suffices filter (fun j ↦ f j = f n) I = filter (fun j ↦ j = n) I by
      simp only [this, prod_filter, prod_ite_eq', if_pos hnI]
    refine filter_congr (fun j hj ↦ ?_)
    refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]⟩
    by_contra hij
    have h_dis : Disjoint (f j) (f n) := hf_disj hj hnI hij
    rw [h] at h_dis
    exact hfn (disjoint_self.mp h_dis)

section Accumulate

variable {α : Type*}

theorem MeasurableSet.accumulate {_ : MeasurableSpace α} {s : ℕ → Set α}
    (hs : ∀ n, MeasurableSet (s n)) (n : ℕ) : MeasurableSet (Set.Accumulate s n) :=
  MeasurableSet.biUnion (Set.to_countable _) fun n _ ↦ hs n

theorem Set.disjoint_accumulate {s : ℕ → Set α} (hs : Pairwise (Function.onFun Disjoint s)) {i j : ℕ}
    (hij : i < j) : Disjoint (Set.Accumulate s i) (s j) := by
  rw [Set.accumulate_def]
  induction i with
  | zero => simp only [Nat.zero_eq, nonpos_iff_eq_zero, iUnion_iUnion_eq_left]; exact hs hij.ne
  | succ i hi =>
    rw [Set.biUnion_le_succ s i]
    exact Disjoint.union_left (hi ((Nat.lt_succ_self i).trans hij)) (hs hij.ne)

@[simp]
theorem Set.accumulate_succ (s : ℕ → Set α) (n : ℕ) :
    Set.Accumulate s (n + 1) = Set.Accumulate s n ∪ s (n + 1) := Set.biUnion_le_succ s n

@[simp]
lemma accumulate_zero_nat (s : ℕ → Set α) : Set.Accumulate s 0 = s 0 := by simp [Set.accumulate_def]

end Accumulate

namespace NNReal

/-- Given x > 0, there is a sequence of positive reals summing to x. -/
theorem exists_seq_pos_summable_eq (x : ℝ≥0) (hx : 0 < x) :
    ∃ f : ℕ → ℝ≥0, (∀ n, 0 < f n) ∧ Summable f ∧ ∑' n, f n = x := by
  have h : ∑' n : ℕ, x / 2 / 2 ^ n = x := by
    rw [NNReal.eq_iff, NNReal.coe_tsum]
    push_cast
    exact tsum_geometric_two' x
  refine ⟨fun n : ℕ ↦ x / 2 / 2 ^ n, fun n ↦ by positivity, ?_, h⟩
  by_contra h1
  rw [tsum_eq_zero_of_not_summable h1] at h
  exact hx.ne h

/-- Given x > 0, there is a sequence of positive reals summing to something less than x. -/
theorem exists_seq_pos_summable_lt (x : ℝ≥0) (hx : 0 < x) :
    ∃ f : ℕ → ℝ≥0, (∀ n, 0 < f n) ∧ Summable f ∧ ∑' n, f n < x := by
  obtain ⟨f, hf⟩ := NNReal.exists_seq_pos_summable_eq (x / 2) (half_pos hx)
  refine ⟨f, hf.1, hf.2.1, ?_⟩
  rw [hf.2.2]
  exact NNReal.half_lt_self (ne_of_gt hx)

end NNReal

namespace ENNReal

/-- Given some x > 0, there is a sequence of positive reals summing to x. -/
theorem exists_seq_pos_eq (x : ℝ≥0∞) (hx : 0 < x) :
    ∃ f : ℕ → ℝ≥0∞, (∀ n, 0 < f n) ∧ ∑' n, f n = x := by
  by_cases hx_top : x = ∞
  · use fun _ ↦ ∞
    simp [forall_const, ENNReal.tsum_top, hx_top, and_self]
  suffices ∃ f : ℕ → ℝ≥0, (∀ n, 0 < f n) ∧ Summable f ∧ ∑' n, f n = x.toNNReal by
    obtain ⟨f, hf_pos, hf_sum, hf_eq⟩ := this
    refine ⟨fun n ↦ f n, ?_, ?_⟩
    · exact fun n ↦ ENNReal.coe_pos.mpr (hf_pos n)
    · rw [← ENNReal.coe_tsum hf_sum, hf_eq, coe_toNNReal hx_top]
  exact NNReal.exists_seq_pos_summable_eq x.toNNReal (toNNReal_pos hx.ne' hx_top)

/-- Given some x > 0, there is a sequence of positive reals summing to something less than x. -/
theorem exists_seq_pos_lt (x : ℝ≥0∞) (hx : 0 < x) :
    ∃ f : ℕ → ℝ≥0∞, (∀ n, 0 < f n) ∧ ∑' n, f n < x := by
  by_cases hx_top : x = ∞
  · obtain ⟨f, hf_pos, hf_eq⟩ : ∃ f : ℕ → ℝ≥0∞, (∀ n, 0 < f n) ∧ ∑' n, f n = 1 :=
      exists_seq_pos_eq 1 zero_lt_one
    refine ⟨f, hf_pos, ?_⟩
    simp only [hf_eq, hx_top, one_lt_top]
  · obtain ⟨f, hf⟩ := ENNReal.exists_seq_pos_eq (x / 2) (ENNReal.half_pos hx.ne')
    refine ⟨f, hf.1, ?_⟩
    rw [hf.2]
    exact ENNReal.half_lt_self hx.ne' hx_top

theorem tendsto_atTop_zero_const_sub_iff (f : ℕ → ℝ≥0∞) (a : ℝ≥0∞) (ha : a ≠ ∞)
    (hfa : ∀ n, f n ≤ a) :
    Tendsto (fun n ↦ a - f n) atTop (𝓝 0) ↔ Tendsto (fun n ↦ f n) atTop (𝓝 a) := by
  rw [ENNReal.tendsto_atTop_zero, ENNReal.tendsto_atTop ha]
  refine ⟨fun h ε hε ↦ ?_, fun h ε hε ↦ ?_⟩ <;> obtain ⟨N, hN⟩ := h ε hε
  · refine ⟨N, fun n hn ↦ ⟨?_, (hfa n).trans (le_add_right le_rfl)⟩⟩
    specialize hN n hn
    rw [tsub_le_iff_right] at hN ⊢
    rwa [add_comm]
  · refine ⟨N, fun n hn ↦ ?_⟩
    have hN_left := (hN n hn).1
    rw [tsub_le_iff_right] at hN_left ⊢
    rwa [add_comm]

theorem tendsto_atTop_zero_iff_of_antitone (f : ℕ → ℝ≥0∞) (hf : Antitone f) :
    Filter.Tendsto f Filter.atTop (𝓝 0) ↔ ∀ ε, 0 < ε → ∃ n : ℕ, f n ≤ ε := by
  rw [ENNReal.tendsto_atTop_zero]
  refine ⟨fun h ↦ fun ε hε ↦ ?_, fun h ↦ fun ε hε ↦ ?_⟩
  · obtain ⟨n, hn⟩ := h ε hε
    exact ⟨n, hn n le_rfl⟩
  · obtain ⟨n, hn⟩ := h ε hε
    exact ⟨n, fun m hm ↦ (hf hm).trans hn⟩

theorem tendsto_atTop_zero_iff_of_antitone' (f : ℕ → ℝ≥0∞) (hf : Antitone f) :
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

namespace Finset

variable {α β : Type*}

lemma mem_map_univ_asEmbedding {α β : Type*} [Fintype α] {p : β → Prop}
    (e : α ≃ Subtype p) {b : β} :
    b ∈ Finset.map e.asEmbedding univ ↔ p b := by
  rw [mem_map]
  simp only [Finset.mem_univ, Equiv.asEmbedding_apply, Function.comp_apply, exists_true_left,
    true_and]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨a, rfl⟩ := h
    exact (e a).prop
  · obtain ⟨a, ha⟩ := e.surjective ⟨b, h⟩
    refine ⟨a, ?_⟩
    rw [ha]

/-- An ordering of the elements of a finset. -/
noncomputable def ordered (J : Finset α) : Fin J.card ↪ α :=
  J.equivFin.symm.asEmbedding

lemma ordered_mem {J : Finset α} (n : Fin J.card) : J.ordered n ∈ J := by
  simp_rw [Finset.ordered]; exact coe_mem _

lemma map_ordered (J : Finset α) : Finset.map J.ordered (univ : Finset (Fin J.card)) = J := by
  ext; simp_rw [Finset.ordered, Finset.mem_map_univ_asEmbedding]

lemma sum_ordered [AddCommMonoid β] (J : Finset α) (m : α → β) :
    ∑ i : Fin J.card, m (J.ordered i) = ∑ u in J, m u := by
  conv_rhs => rw [← map_ordered J]
  rw [sum_map]

/-- The n first elements in `J.ordered`. -/
noncomputable def finsetLT (J : Finset α) : Fin J.card → Finset α :=
  fun n ↦ (Finset.filter (fun j : Fin J.card ↦ j < n) univ).map J.ordered

@[simp]
lemma mem_finsetLT (J : Finset α) (n : Fin J.card) (s : α) :
    s ∈ finsetLT J n ↔ ∃ m < n, s = J.ordered m := by
  rw [finsetLT, mem_map]
  simp only [mem_filter, Finset.mem_univ, true_and, Equiv.asEmbedding_apply,
    Function.comp_apply, exists_prop]
  simp_rw [@eq_comm _ _ s]

lemma ordered_mem_finsetLT (J : Finset α) {n m : Fin J.card} (hnm : n < m) :
    J.ordered n ∈ finsetLT J m := by rw [mem_finsetLT _ _]; exact ⟨n, hnm, rfl⟩

@[simp]
lemma finsetLT_zero {J : Finset α} (hJ : 0 < J.card) : finsetLT J ⟨0, hJ⟩ = ∅ := by
  rw [finsetLT]
  simp only [univ_eq_attach, map_eq_empty, filter_eq_empty_iff]
  intro n _
  rw [not_lt, ← Fin.eta n n.2, Fin.mk_le_mk]
  exact zero_le'

lemma finsetLT_mono (J : Finset α) : Monotone (finsetLT J) := by
  intro n m hnm s
  rw [finsetLT, mem_map]
  rintro ⟨i, hi, rfl⟩
  refine ordered_mem_finsetLT J ?_
  rw [mem_filter] at hi
  exact hi.2.trans_le hnm

lemma finsetLT_subset (J : Finset α) (n : Fin J.card) : finsetLT J n ⊆ J := by
  intro u; rw [finsetLT, mem_map]; rintro ⟨i, _, rfl⟩; exact ordered_mem i

lemma biUnion_finsetLT (J : Finset α) (n : Fin J.card) :
    ⋃ i ≤ n, (finsetLT J i : Set α) = finsetLT J n := by
  ext x
  simp only [mem_iUnion, mem_coe, mem_finsetLT, exists_prop]
  exact ⟨fun ⟨i, hin, ⟨m, hmi, h⟩⟩ ↦ ⟨m, hmi.trans_le hin, h⟩,
    fun ⟨m, hmn, h⟩ ↦ ⟨n, le_rfl, m, hmn, h⟩⟩

section FinsetSet

variable {C : Set (Set α)} {J : Finset (Set α)}

lemma iUnion_ordered (J : Finset (Set α)) : (⋃ i, J.ordered i) = ⋃₀ J := by
  conv_rhs => rw [← map_ordered J]
  simp_rw [sUnion_eq_biUnion, coe_map, Set.biUnion_image]
  simp only [mem_coe, Finset.mem_univ, iUnion_true]

lemma finsetLT_subset' (J : Finset (Set α)) (hJ : ↑J ⊆ C) (n : Fin J.card) :
    ↑(finsetLT J n) ⊆ C :=
  (Finset.coe_subset.mpr (finsetLT_subset J n)).trans hJ

lemma sUnion_finsetLT_eq_biUnion (J : Finset (Set α)) (n : Fin J.card) :
    ⋃₀ (finsetLT J n : Set (Set α)) = ⋃ i < n, J.ordered i := by
  ext
  simp_rw [mem_sUnion, mem_coe, mem_finsetLT, mem_iUnion]
  constructor
  · rintro ⟨t, ⟨m, hmn, rfl⟩, hat⟩
    exact ⟨m, hmn, hat⟩
  · rintro ⟨m, hmn, hat⟩
    exact ⟨J.ordered m, ⟨m, hmn, rfl⟩, hat⟩

end FinsetSet

end Finset


/- namespace MeasureTheory

namespace IsProjectiveMeasureFamily

variable {ι : Type*} {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
  {P : ∀ J : Finset ι, Measure (Π j : J, α j)}

lemma isConstant_of_univ (hP : IsProjectiveMeasureFamily P) :
    (∃ a, ∀ J, P J univ = a) := by
  classical
  by_cases h : Nonempty ι
  · let default := Classical.choice h
    use P {default} univ
    intro J
    let I := insert default J





    sorry
  · rw [isempty_] at h
    have h1 : Inhabited ι := by simp
    use P {default} univ


lemma isConstant_of_univ' (hP : IsProjectiveMeasureFamily P) :
    (∃ a, (fun J => P J univ) = Function.const _ a) := by
  sorry


def IsProjectiveMeasureFamily1 (P : ∀ J : Finset ι, Measure (∀ j : J, α j)) : Prop :=
  ∀ (I J : Finset ι) (hJI : J ⊆ I),
    P J = (P I).map (Finset.restrict₂ hJI)




end IsProjectiveMeasureFamily

end MeasureTheory
-/

#min_imports
