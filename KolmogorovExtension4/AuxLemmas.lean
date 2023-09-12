import Mathlib.MeasureTheory.Measure.OuterMeasure
import Mathlib.Logic.Denumerable

open Finset Set Filter

open scoped BigOperators ENNReal Topology

theorem bInter_diff_bUnion_subset {ι α : Type _} (A B : ι → Set α) (s : Set ι) :
    ((⋂ i ∈ s, A i) \ ⋃ i ∈ s, B i) ⊆ ⋂ i ∈ s, A i \ B i := by
  intro x
  simp only [mem_diff, mem_iInter, mem_iUnion, exists_prop, not_exists, not_and, and_imp]
  intro h1 h2 i hi
  exact ⟨h1 i hi, h2 i hi⟩

theorem Finset.sum_image_le {ι α β : Type _} [DecidableEq α] [OrderedSemiring β] (J : Finset ι)
    (g : ι → α) (f : α → β) (hf : ∀ u ∈ J.image g, 0 ≤ f u) :
    ∑ u in J.image g, f u ≤ ∑ u in J, f (g u) := by
  rw [sum_comp f g]
  refine sum_le_sum fun a hag => ?_
  let hag' := hag
  rw [Finset.mem_image] at hag' 
  obtain ⟨i, hi, hig⟩ := hag'
  suffices 1 ≤ (J.filter (fun j => g j = a)).card by
    conv_lhs => rw [← one_smul ℕ (f a)]
    simp_rw [nsmul_eq_mul]
    exact mul_le_mul (Nat.mono_cast this) le_rfl (hf a hag) (Nat.cast_nonneg _)
  rw [Nat.succ_le_iff, card_pos]
  refine ⟨i, ?_⟩
  rw [mem_filter]
  exact ⟨hi, hig⟩

theorem partialSups_eq_sUnion_image {α : Type _} [DecidableEq (Set α)] (f : ℕ → Set α) (n : ℕ) :
    partialSups f n = ⋃₀ ↑(Finset.image f (range (n + 1))) := by
  ext1 s
  simp only [partialSups_eq_biSup, iSup_eq_iUnion, Set.mem_sUnion, mem_iUnion, exists_prop, mem_coe,
  Finset.mem_image, Finset.mem_range, exists_exists_and_eq_and, Nat.lt_succ_iff]

theorem monotone_partialSups {α : Type _} [SemilatticeSup α] (f : ℕ → α) :
    Monotone fun n => partialSups f n := fun n _ hnm =>
  partialSups_le f n _ fun _ hm'n => le_partialSups_of_le _ (hm'n.trans hnm)

/-- todo: this has to be somewhere in mathlib -/
theorem Set.bUnion_le_succ {α : Type _} (s : ℕ → Set α) (n : ℕ) :
    (⋃ i ≤ n.succ, s i) = (⋃ i ≤ n, s i) ∪ s n.succ := by 
  simp_rw [← Nat.lt_succ_iff];
  exact Set.biUnion_lt_succ s (n + 1)

theorem Set.bInter_le_succ {α : Type _} (s : ℕ → Set α) (n : ℕ) :
    (⋂ i ≤ n.succ, s i) = (⋂ i ≤ n, s i) ∩ s n.succ := by 
  simp_rw [← Nat.lt_succ_iff];
  exact Set.biInter_lt_succ s (n + 1)

theorem ENNReal.tendsto_atTop_zero_const_sub_iff (f : ℕ → ℝ≥0∞) (a : ℝ≥0∞) (ha : a ≠ ∞)
    (hfa : ∀ n, f n ≤ a) :
    Tendsto (fun n => a - f n) atTop (𝓝 0) ↔ Tendsto (fun n => f n) atTop (𝓝 a) := by
  rw [ENNReal.tendsto_atTop_zero, ENNReal.tendsto_atTop ha]
  refine ⟨fun h ε hε => ?_, fun h ε hε => ?_⟩ <;> obtain ⟨N, hN⟩ := h ε hε
  · refine ⟨N, fun n hn => ⟨?_, (hfa n).trans (le_add_right le_rfl)⟩⟩
    specialize hN n hn
    rw [tsub_le_iff_right] at hN ⊢
    rwa [add_comm]
  · refine ⟨N, fun n hn => ?_⟩
    have hN_left := (hN n hn).1
    rw [tsub_le_iff_right] at hN_left ⊢
    rwa [add_comm]

section Accumulate

variable {α : Type _}

theorem MeasurableSet.accumulate {_ : MeasurableSpace α} {s : ℕ → Set α}
    (hs : ∀ n, MeasurableSet (s n)) (n : ℕ) : MeasurableSet (Set.Accumulate s n) :=
  MeasurableSet.biUnion (Set.to_countable _) fun n _ => hs n

theorem Set.accumulate_subset_iUnion (s : ℕ → Set α) (n : ℕ) : Set.Accumulate s n ⊆ ⋃ i, s i := by
  simp_rw [Set.accumulate_def, Set.iUnion_subset_iff]; exact fun i _ => Set.subset_iUnion s i

theorem Set.disjoint_accumulate {s : ℕ → Set α} (hs : Pairwise (Disjoint on s)) {i j : ℕ}
    (hij : i < j) : Disjoint (Set.Accumulate s i) (s j) := by
  rw [Set.accumulate_def]
  induction' i with i hi
  · simp only [Nat.zero_eq, nonpos_iff_eq_zero, iUnion_iUnion_eq_left]
    exact hs hij.ne
  · rw [Set.bUnion_le_succ s i]
    exact Disjoint.union_left (hi ((Nat.lt_succ_self i).trans hij)) (hs hij.ne)

theorem Set.accumulate_succ (s : ℕ → Set α) (n : ℕ) :
    Set.Accumulate s (n + 1) = Set.Accumulate s n ∪ s (n + 1) :=
  Set.bUnion_le_succ s n

end Accumulate

variable {α β : Type*} 

namespace Set


lemma rangeFactorization_bijective_of_injective {f : α → β} (hf : Function.Injective f) :
    Function.Bijective (rangeFactorization f) := by
  refine ⟨?_, surjective_onto_range⟩
  intros x y h1
  have h2 : (rangeFactorization f x : β) = (rangeFactorization f y : β) := by rw [h1]
  simp only [rangeFactorization_coe] at h2 
  apply hf h2

end Set

namespace Equiv

lemma of_range_injective {f : α → β} (hf : Function.Injective f) : α ≃ (range f) :=
  ofBijective (rangeFactorization f) (rangeFactorization_bijective_of_injective hf)

end Equiv


namespace Denumerable

variable {α β : Type*} 

open Function Set

lemma Denumerable.ofNat_surjective [h : Denumerable α] :
    Surjective (Denumerable.ofNat α) := by
  intro x
  use Encodable.encode x
  simp only [decode_eq_ofNat, Option.some.injEq, ofNat_encode]

lemma Denumerable.ofNat_injective [h : Denumerable α] :
    Injective (Denumerable.ofNat α) := by
  refine HasLeftInverse.injective ?_
  use Encodable.encode
  exact Denumerable.encode_ofNat

lemma l1 (s : Set α) (hs : Denumerable s) :
    s ≃ (range (fun i => (Denumerable.ofNat s i))) := by
  let f := fun (i : ℕ) => (Denumerable.ofNat s i)
  haveI hr : ℕ ≃ (range f)  :=  by
    have hf : Injective f := Denumerable.ofNat_injective
    exact Equiv.of_range_injective hf
  obtain hD : Denumerable (range f) := Denumerable.mk' (id hr.symm)
  apply Denumerable.equiv₂

lemma Denumerable.range_coe_ofNat [hs : Denumerable α] :
    range (fun i => (Denumerable.ofNat α i)) = Set.univ := by
  let f := fun (i : ℕ) => (Denumerable.ofNat α i)
  have hfS : Surjective f := Denumerable.ofNat_surjective
  rw [← Set.image_univ_of_surjective hfS]
  simp only [decode_eq_ofNat, Option.some.injEq, image_univ]

lemma l3a {s : Set β} (f : α → s) :
    ((range (fun x => f x)) : Set β) = Subtype.val '' (range f) := by
  rw [← range_comp]
  rfl

lemma l4 {s : Set α} [hs : Denumerable s] :
    ((range (fun i => (Denumerable.ofNat s i))) : Set α) = s := by
  conv_rhs
  => conv => {rw [← Subtype.coe_image_univ s]}
  have h : ((range (fun i => (Denumerable.ofNat s i))) : Set α)
      = Subtype.val '' (range (fun i => (Denumerable.ofNat s i))) :=
    l3a (fun i => (Denumerable.ofNat s i))
  rw [h]
  apply congrArg (Set.image Subtype.val)
  exact Denumerable.range_coe_ofNat

end Denumerable





