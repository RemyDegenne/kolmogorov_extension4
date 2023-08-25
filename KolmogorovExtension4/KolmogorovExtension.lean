import KolmogorovExtension4.AdditiveOfContinuous
import KolmogorovExtension4.CaratheodoryExtension
import KolmogorovExtension4.Projective
import KolmogorovExtension4.RegularityCompacts
import Mathlib.MeasureTheory.Constructions.Polish

open Set

open scoped ENNReal BigOperators

section isClosed_proj

open Filter

open scoped Topology Filter

variable {ι : Type _} {α : ι → Type _} [∀ i, TopologicalSpace (α i)] {s : Set (∀ i, α i)}

theorem continuous_cast {α β : Type _} [tα : TopologicalSpace α] [tβ : TopologicalSpace β]
    (h : α = β) (ht : HEq tα tβ) : Continuous fun x : α => cast h x := by
  subst h
  convert continuous_id
  rw [← heq_iff_eq]
  exact ht.symm

theorem isClosed_proj (hs_compact : IsCompact s) (hs_closed : IsClosed s) (i : ι) :
    IsClosed ((fun x : ∀ j, α j => x i) '' s) := by
  set πi : (∀ j, α j) → α i := fun x : ∀ j, α j => x i
  set π : (∀ j, α j) → ∀ j : { k // k ≠ i }, α j := fun x (j : { k // k ≠ i }) => x j
  have hπi_cont : Continuous πi := continuous_apply _
  have hπ_cont : Continuous π := continuous_pi fun j => continuous_apply _
  -- we want to use `is_closed_proj_of_is_compact`, which states that the projection from `X × Y`
  -- to `Y` is a closed map when `X` is a compact space.
  -- Here, `X = ↥(π '' s)` and `Y = α i`.
  let X := ↥(π '' s)
  have : CompactSpace X := by
    refine' isCompact_iff_compactSpace.mp _
    refine' IsCompact.image hs_compact _
    exact continuous_pi fun j => continuous_apply _
  classical
  let XY : Set (∀ j, α j) := {x | π x ∈ π '' s}
  let from_X_prod_Y : X × α i → ∀ j, α j := fun p j =>
    if h : j = i then by refine' cast _ p.2; rw [h] else (p.1 : ∀ j : { k // k ≠ i }, α j) ⟨j, h⟩
  have fXY_eq_of_ne :
    ∀ (p j) (h : j ≠ i), from_X_prod_Y p j = (p.1 : ∀ j : { k // k ≠ i }, α j) ⟨j, h⟩ := by
    intro p j h
    simp only [h, not_false_iff, dif_neg]
  have hπ_fXY : ∀ p, π (from_X_prod_Y p) = p.1 := by
    intro p
    ext1 j
    simp only
    have : (j : ι) ≠ i := j.2
    rw [dif_neg this]
  have hπi_fXY : ∀ p, πi (from_X_prod_Y p) = p.2 := by
    intro p
    simp only [ne_eq, cast_eq, dite_true]
  have continuous_from_X_prod_Y : Continuous from_X_prod_Y := by
    simp only
    refine' continuous_pi fun j => _
    split_ifs with h
    · refine' (continuous_cast _ _).comp continuous_snd
      rw [h]
    · exact (Continuous.comp (continuous_apply _) continuous_subtype_val).comp continuous_fst
  have h_mem : ∀ p, from_X_prod_Y p ∈ XY := by
    intro p
    simp only [mem_image, mem_setOf_eq]
    obtain ⟨y, hy_mem_s, hy_eq⟩ := p.1.2
    refine' ⟨y, hy_mem_s, hy_eq.trans _⟩
    simp only [ne_eq]
    rw [hπ_fXY]
    rfl
  let e : XY ≃ₜ X × α i :=
    { toFun := fun x => ⟨⟨π x, x.2⟩, πi x⟩
      invFun := fun p => ⟨from_X_prod_Y p, h_mem p⟩
      left_inv := fun x => by
        ext j
        simp only [Subtype.coe_mk]
        split_ifs with h
        · rw [← heq_iff_eq]
          refine' HEq.trans (cast_heq (_ : α i = α j) _) _
          rw [h]
        · congr
      right_inv := fun p => by
        simp only [Subtype.coe_mk]
        ext
        · refine' Subtype.ext _
          rw [Subtype.coe_mk, hπ_fXY]
        · rfl
      continuous_toFun := by
        refine' Continuous.prod_mk _ _
        · exact Continuous.subtype_mk (hπ_cont.comp continuous_subtype_val) _
        · exact hπi_cont.comp continuous_subtype_val
      continuous_invFun := Continuous.subtype_mk continuous_from_X_prod_Y _ }
  have hs_subset : s ⊆ XY := fun x hx => ⟨x, hx, rfl⟩
  have h_image_eq : πi '' s = Prod.snd '' (e '' (coe ⁻¹' s)) :=
    by
    ext1 x
    simp only [πi, mem_image, mem_set_of_eq, Subtype.coe_mk, Homeomorph.homeomorph_mk_coe,
      Equiv.coe_fn_mk, mem_preimage, SetCoe.exists, exists_and_left, Prod.exists, Prod.mk.inj_iff,
      exists_and_right, exists_eq_right, Subtype.mk_eq_mk, exists_prop, exists_exists_and_eq_and]
    constructor
    · rintro ⟨y, hy_mem, hy⟩
      exact ⟨y, hy_mem, ⟨y, hy_mem, ⟨⟨⟨y, hy_mem, rfl⟩, rfl⟩, hy⟩⟩⟩
    · rintro ⟨y, hy_mem, ⟨z, hz_mem, h⟩⟩
      exact ⟨z, hz_mem, h.2⟩
  rw [h_image_eq]
  refine' isClosedMap_snd_of_compactSpace _ _
  rw [Homeomorph.isClosed_image]
  exact IsClosed.preimage continuous_subtype_val hs_closed

end isClosed_proj

namespace MeasureTheory

-- this is horrible
theorem todo (ε : ℝ≥0∞) (n : ℕ) : ∑ i in Finset.range (n + 1), ε / 2 ^ (i + 2) ≤ ε / 2 := by
  simp_rw [div_eq_mul_inv, mul_comm ε]
  rw [← Finset.sum_mul]
  refine' mul_le_mul _ le_rfl (zero_le _) (by norm_num)
  have h := sum_geometric_two_le (n + 1)
  simp only [one_div, inv_pow] at h 
  have h' : ∑ i in Finset.range (n + 1), ((2 : ℝ≥0∞) ^ i)⁻¹ ≤ 2 := by
    refine' (le_of_eq_of_le _ (ENNReal.ofReal_le_ofReal h)).trans_eq _
    swap
    · simp only [ENNReal.ofReal_ofNat]
    rw [ENNReal.ofReal_sum_of_nonneg fun i _ => _]
    swap
    · simp only [Finset.mem_range, inv_nonneg, ge_iff_le]
      exact fun _ _ ↦ pow_nonneg zero_le_two _
    congr with i : 1
    rw [← ENNReal.ofReal_inv_of_pos]
    swap
    · simp only [gt_iff_lt, zero_lt_two, pow_pos]
    rw [ENNReal.ofReal_pow]
    swap; · exact zero_le_two
    simp only [ENNReal.ofReal_ofNat]
  simp_rw [pow_add]
  norm_num
  calc
    (∑ i in Finset.range (n + 1), ((2 : ℝ≥0∞) ^ i * 4)⁻¹) * 2 =
        (∑ i in Finset.range (n + 1), ((2 : ℝ≥0∞) ^ i)⁻¹ * 4⁻¹) * 2 := by
      congr with i : 1
      rw [ENNReal.mul_inv (Or.inr _) (Or.inr _)]
      · exact ENNReal.coe_ne_top
      · norm_num
    _ = (∑ x : ℕ in Finset.range (n + 1), ((2 : ℝ≥0∞) ^ x)⁻¹) * 4⁻¹ * 2 := by rw [← Finset.sum_mul]
    _ ≤ 2 * 4⁻¹ * 2 := by simp_rw [mul_assoc]; refine' ENNReal.mul_right_mono h'
    _ = 1 :=-- `norm_num` does not work correctly in `ℝ≥0∞` :(
    by
      rw [mul_comm, ← mul_assoc]
      norm_num
      rw [ENNReal.mul_inv_cancel]
      · norm_num
      · exact ENNReal.coe_ne_top

variable {ι : Type _} {α : ι → Type _} [∀ i, MeasurableSpace (α i)]
  {P : ∀ J : Finset ι, Measure (∀ j : J, α j)}

section KolFunDef

variable {s t : Set (∀ i, α i)}

/-- We will show that this is an additive set function that defines a measure. -/
noncomputable def kolmogorovFun (P : ∀ J : Finset ι, Measure (∀ j : J, α j)) (s : Set (∀ i, α i))
    (hs : s ∈ cylinders α) : ℝ≥0∞ :=
  P (cylinders.finset hs) (cylinders.set hs)

theorem kolmogorovFun_congr_set (hs : s ∈ cylinders α) (h_eq : s = t) :
    kolmogorovFun P s hs = kolmogorovFun P t (by rwa [h_eq] at hs ) := by congr

variable [Nonempty (∀ i, α i)]

theorem kolmogorovFun_congr (hP : IsProjectiveMeasureFamily P) {s : Set (∀ i, α i)}
    (hs : s ∈ cylinders α) {I : Finset ι} {S : Set (∀ i : I, α i)} (hs_eq : s = cylinder I S)
    (hS : MeasurableSet S) : kolmogorovFun P s hs = P I S := by
  refine' kolmogorovFun_congr_aux2 hP (cylinders.measurableSet hs) hS _
  exact (cylinders.eq_cylinder hs).symm.trans hs_eq

theorem kolmogorovFun_empty (hP : IsProjectiveMeasureFamily P) :
    kolmogorovFun P ∅ (empty_mem_cylinders α) = 0 := by
  rw [kolmogorovFun_congr hP (empty_mem_cylinders α) (cylinder_empty ∅).symm MeasurableSet.empty,
    measure_empty]

theorem kolmogorovFun_union (hP : IsProjectiveMeasureFamily P) (hs : s ∈ cylinders α)
    (ht : t ∈ cylinders α) (hst : Disjoint s t) :
    kolmogorovFun P (s ∪ t) (union_mem_cylinders hs ht) =
      kolmogorovFun P s hs + kolmogorovFun P t ht := by
  rw [mem_cylinders] at hs ht 
  obtain ⟨I, S, hS, hs_eq⟩ := hs
  obtain ⟨J, T, hT, ht_eq⟩ := ht
  classical
  let S' := (fun f : ∀ i : (I ∪ J : Finset ι), α i =>
    fun j : I => f ⟨j, Finset.mem_union_left J j.prop⟩) ⁻¹' S
  let T' := (fun f : ∀ i : (I ∪ J : Finset ι), α i =>
    fun j : J => f ⟨j, Finset.mem_union_right I j.prop⟩) ⁻¹' T
  have hS' : MeasurableSet S' := by
    refine' measurableSet_preimage _ hS
    rw [measurable_pi_iff]
    exact fun j => measurable_pi_apply _
  have hT' : MeasurableSet T' := by
    refine' measurableSet_preimage _ hT
    rw [measurable_pi_iff]
    exact fun j => measurable_pi_apply _
  have h_eq1 : s = cylinder (I ∪ J) S' := by rw [hs_eq]; exact cylinder_eq_cylinder_union I S J
  have h_eq2 : t = cylinder (I ∪ J) T' := by rw [ht_eq]; exact cylinder_eq_cylinder_union J T I
  have h_eq3 : s ∪ t = cylinder (I ∪ J) (S' ∪ T') := by
    rw [hs_eq, ht_eq]; exact union_cylinder _ _ _ _
  rw [kolmogorovFun_congr hP hs h_eq1 hS', kolmogorovFun_congr hP ht h_eq2 hT',
    kolmogorovFun_congr hP _ h_eq3 (hS'.union hT'), measure_union _ hT']
  rwa [hs_eq, ht_eq, disjoint_cylinder_iff] at hst 

theorem kolmogorovFun_additive (hP : IsProjectiveMeasureFamily P) (I : Finset (Set (∀ i, α i)))
    (h_ss : ↑I ⊆ cylinders α) (h_dis : PairwiseDisjoint (I : Set (Set (∀ i, α i))) id)
    (h_mem : ⋃₀ ↑I ∈ cylinders α) :
    kolmogorovFun P (⋃₀ I) h_mem = ∑ u : I, kolmogorovFun P u (h_ss u.prop) := by
  refine' sUnion_eq_sum_of_union_eq_add' _ _ _ _ _ I h_ss h_dis h_mem
  · exact empty_mem_cylinders α
  · exact union_mem_cylinders
  · exact kolmogorovFun_empty hP
  · exact kolmogorovFun_union hP

/-- `kolmogorovFun` as an additive content. -/
noncomputable def kolContent (hP : IsProjectiveMeasureFamily P) : AddContent (cylinders α) :=
  extendContent setSemiringCylinders (kolmogorovFun P) (kolmogorovFun_empty hP)
    (kolmogorovFun_additive hP)

theorem kolContent_eq (hP : IsProjectiveMeasureFamily P) (hs : s ∈ cylinders α) :
    kolContent hP s = kolmogorovFun P s hs := by rw [kolContent, extendContent_eq]

theorem kolContent_ne_top [∀ J, IsFiniteMeasure (P J)] (hP : IsProjectiveMeasureFamily P)
    (hs : s ∈ cylinders α) : kolContent hP s ≠ ∞ := by
  rw [kolContent_eq hP hs]; exact measure_ne_top _ _

theorem kolContent_congr (hP : IsProjectiveMeasureFamily P) (hs : s ∈ cylinders α) {I : Finset ι}
    {S : Set (∀ i : I, α i)} (hs_eq : s = cylinder I S) (hS : MeasurableSet S) :
    kolContent hP s = P I S := by rw [kolContent_eq, kolmogorovFun_congr hP hs hs_eq hS]

theorem kolContent_mono (hP : IsProjectiveMeasureFamily P) (hs : s ∈ cylinders α)
    (ht : t ∈ cylinders α) (hst : s ⊆ t) : kolContent hP s ≤ kolContent hP t :=
  (kolContent hP).mono setSemiringCylinders hs ht hst

theorem kolContent_iUnion_le (hP : IsProjectiveMeasureFamily P) ⦃s : ℕ → Set (∀ i : ι, α i)⦄
    (hs : ∀ n, s n ∈ cylinders α) (n : ℕ) :
    kolContent hP (⋃ i ≤ n, s i) ≤ ∑ i in Finset.range (n + 1), kolContent hP (s i) :=
  addContent_iUnion_le (kolContent hP) setRing_cylinders hs n

theorem kolContent_diff (hP : IsProjectiveMeasureFamily P) (hs : s ∈ cylinders α)
    (ht : t ∈ cylinders α) : kolContent hP s - kolContent hP t ≤ kolContent hP (s \ t) :=
  addContent_diff (kolContent hP) setRing_cylinders hs ht

end KolFunDef

section ContinuityAtEmpty

local notation "Js" => cylinders.finset

local notation "As" => cylinders.set

section AllProj

/-- All indices in `ι` that are constrained by the condition `∀ n, s n ∈ cylinders α`. That is, the
union of all indices in the bases of the cylinders. -/
def allProj {s : ℕ → Set (∀ i, α i)} (hs : ∀ n, s n ∈ cylinders α) : Set ι :=
  ⋃ n, Js (hs n)

theorem subset_allProj {s : ℕ → Set (∀ i, α i)} (hs : ∀ n, s n ∈ cylinders α) (n : ℕ) :
    ↑(Js (hs n)) ⊆ allProj hs :=
  subset_iUnion (fun i ↦ (Js (hs i) : Set ι)) n

theorem exists_nat_proj {s : ℕ → Set (∀ i, α i)} (hs : ∀ n, s n ∈ cylinders α) (i : ι)
    (hi : i ∈ allProj hs) : ∃ n : ℕ, i ∈ Js (hs n) := by
  simpa only [allProj, mem_iUnion, Finset.mem_coe] using hi

/-- The smallest `n` such that `i ∈ Js (hs n)`. That is, the first `n` such that `i` belongs to the
finset defining the cylinder for `s n`. -/
def indexProj {s : ℕ → Set (∀ i, α i)} (hs : ∀ n, s n ∈ cylinders α) (i : allProj hs)
    [DecidablePred fun n => ↑i ∈ Js (hs n)] : ℕ :=
  Nat.find (exists_nat_proj hs i i.2)

theorem mem_indexProj {s : ℕ → Set (∀ i, α i)} (hs : ∀ n, s n ∈ cylinders α) (i : allProj hs)
    [DecidablePred fun n => ↑i ∈ Js (hs n)] : (i : ι) ∈ Js (hs (indexProj hs i)) :=
  Nat.find_spec (exists_nat_proj hs i i.2)

theorem indexProj_le {s : ℕ → Set (∀ i, α i)} (hs : ∀ n, s n ∈ cylinders α) (n : ℕ)
    [∀ i, DecidablePred fun n => i ∈ Js (hs n)] (i : Js (hs n)) :
    indexProj hs ⟨i, subset_allProj hs n i.2⟩ ≤ n :=
  Nat.find_le i.2

end AllProj

variable [∀ i, TopologicalSpace (α i)] [∀ i, OpensMeasurableSpace (α i)]
  [∀ i, TopologicalSpace.SecondCountableTopology (α i)] [∀ I, IsFiniteMeasure (P I)]

theorem exists_compact
    (hP_inner : ∀ J, (P J).InnerRegular (fun s => IsCompact s ∧ IsClosed s) MeasurableSet)
    (J : Finset ι) (A : Set (∀ i : J, α i)) (hA : MeasurableSet A) (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ K, IsCompact K ∧ IsClosed K ∧ K ⊆ A ∧ P J (A \ K) ≤ ε := by
  by_cases hPA : P J A = 0
  · refine' ⟨∅, isCompact_empty, isClosed_empty, empty_subset _, _⟩
    rw [diff_empty, hPA]
    exact zero_le ε
  have h : P J A - ε < P J A := ENNReal.sub_lt_self (measure_ne_top _ _) hPA hε.ne'
  obtain ⟨K, hKA, ⟨hK_compact, hK_closed⟩, h_lt⟩ := hP_inner J hA (P J A - ε) h
  refine' ⟨K, hK_compact, hK_closed, hKA, _⟩
  rw [measure_diff hKA hK_closed.measurableSet (measure_ne_top (P J) _)]
  have h_le := h_lt.le
  rw [tsub_le_iff_left] at h_le ⊢
  rwa [add_comm]

def innerCompact
    (hP_inner : ∀ J, (P J).InnerRegular (fun s => IsCompact s ∧ IsClosed s) MeasurableSet)
    (J : Finset ι) (A : Set (∀ i : J, α i)) (hA : MeasurableSet A) (ε : ℝ≥0∞) (hε : 0 < ε) :
    Set (∀ i : J, α i) :=
  (exists_compact hP_inner J A hA ε hε).choose

theorem isCompact_innerCompact
    (hP_inner : ∀ J, (P J).InnerRegular (fun s => IsCompact s ∧ IsClosed s) MeasurableSet)
    (J : Finset ι) (A : Set (∀ i : J, α i)) (hA : MeasurableSet A) (ε : ℝ≥0∞) (hε : 0 < ε) :
    IsCompact (innerCompact hP_inner J A hA ε hε) :=
  (exists_compact hP_inner J A hA ε hε).choose_spec.1

theorem isClosed_innerCompact
    (hP_inner : ∀ J, (P J).InnerRegular (fun s => IsCompact s ∧ IsClosed s) MeasurableSet)
    (J : Finset ι) (A : Set (∀ i : J, α i)) (hA : MeasurableSet A) (ε : ℝ≥0∞) (hε : 0 < ε) :
    IsClosed (innerCompact hP_inner J A hA ε hε) :=
  (exists_compact hP_inner J A hA ε hε).choose_spec.2.1

theorem innerCompact_subset
    (hP_inner : ∀ J, (P J).InnerRegular (fun s => IsCompact s ∧ IsClosed s) MeasurableSet)
    (J : Finset ι) (A : Set (∀ i : J, α i)) (hA : MeasurableSet A) (ε : ℝ≥0∞) (hε : 0 < ε) :
    innerCompact hP_inner J A hA ε hε ⊆ A :=
  (exists_compact hP_inner J A hA ε hε).choose_spec.2.2.1

theorem measurableSet_innerCompact
    (hP_inner : ∀ J, (P J).InnerRegular (fun s => IsCompact s ∧ IsClosed s) MeasurableSet)
    (J : Finset ι) (A : Set (∀ i : J, α i)) (hA : MeasurableSet A) (ε : ℝ≥0∞) (hε : 0 < ε) :
    MeasurableSet (innerCompact hP_inner J A hA ε hε) :=
  (isClosed_innerCompact hP_inner J A hA ε hε).measurableSet

theorem measure_diff_innerCompact
    (hP_inner : ∀ J, (P J).InnerRegular (fun s => IsCompact s ∧ IsClosed s) MeasurableSet)
    (J : Finset ι) (A : Set (∀ i : J, α i)) (hA : MeasurableSet A) (ε : ℝ≥0∞) (hε : 0 < ε) :
    P J (A \ innerCompact hP_inner J A hA ε hε) ≤ ε :=
  (exists_compact hP_inner J A hA ε hε).choose_spec.2.2.2

theorem measure_innerCompact_ge
    (hP_inner : ∀ J, (P J).InnerRegular (fun s => IsCompact s ∧ IsClosed s) MeasurableSet)
    (J : Finset ι) (A : Set (∀ i : J, α i)) (hA : MeasurableSet A) (ε : ℝ≥0∞) (hε : 0 < ε) :
    P J A - ε ≤ P J (innerCompact hP_inner J A hA ε hε) := by
  rw [tsub_le_iff_left, ← tsub_le_iff_right]
  refine' le_trans _ (measure_diff_innerCompact hP_inner J A hA ε hε)
  rw [tsub_le_iff_left, add_comm]
  nth_rw 2 [← inter_eq_right_iff_subset.mpr (innerCompact_subset hP_inner J A hA ε hε)]
  rw [measure_diff_add_inter _ (measurableSet_innerCompact hP_inner J A hA ε hε)]

theorem nonempty_innerCompact
    (hP_inner : ∀ J, (P J).InnerRegular (fun s => IsCompact s ∧ IsClosed s) MeasurableSet)
    (J : Finset ι) (A : Set (∀ i : J, α i)) (hA : MeasurableSet A) (ε : ℝ≥0∞) (hε : 0 < ε)
    (h : ε < P J A) : (innerCompact hP_inner J A hA ε hε).Nonempty := by
  suffices 0 < P J (innerCompact hP_inner J A hA ε hε) by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h 
    rw [h, measure_empty] at this 
    exact lt_irrefl _ this
  refine' lt_of_lt_of_le _ (measure_innerCompact_ge hP_inner J A hA ε hε)
  rwa [lt_tsub_iff_left, add_zero]

/-- A set of `Π i : allProj hs, α i`, preimage of the cylinder with compact base which is an `ε`
approximation of `s n`. -/
def cylCompact'
    (hP_inner : ∀ J, (P J).InnerRegular (fun s => IsCompact s ∧ IsClosed s) MeasurableSet)
    {s : ℕ → Set (∀ i, α i)} (hs : ∀ n, s n ∈ cylinders α) (ε : ℝ≥0∞) (hε : 0 < ε) (n : ℕ) :
    Set (∀ i : allProj hs, α i) :=
  (fun (f : ∀ i : allProj hs, α i) (i : Js (hs n)) => f ⟨i, subset_allProj hs _ i.2⟩) ⁻¹'
    innerCompact hP_inner (Js (hs n)) (As (hs n)) (cylinders.measurableSet _) ε hε

theorem preimage_cylCompact'_subset
    (hP_inner : ∀ J, (P J).InnerRegular (fun s => IsCompact s ∧ IsClosed s) MeasurableSet)
    {s : ℕ → Set (∀ i, α i)} (hs : ∀ n, s n ∈ cylinders α) (ε : ℝ≥0∞) (hε : 0 < ε) (n : ℕ) :
    (fun (f : ∀ i, α i) (i : allProj hs) => f i) ⁻¹' cylCompact' hP_inner hs ε hε n ⊆ s n := by
  intro x h
  rw [cylinders.eq_cylinder (hs n), mem_cylinder]
  simp only [mem_preimage, cylCompact', mem_cylinder] at h 
  exact innerCompact_subset _ _ _ _ _ _ h

theorem isClosed_cylCompact'
    (hP_inner : ∀ J, (P J).InnerRegular (fun s => IsCompact s ∧ IsClosed s) MeasurableSet)
    {s : ℕ → Set (∀ i, α i)} (hs : ∀ n, s n ∈ cylinders α) (ε : ℝ≥0∞) (hε : 0 < ε) (n : ℕ) :
    IsClosed (cylCompact' hP_inner hs ε hε n) := by
  refine (isClosed_innerCompact hP_inner _ _ _ _ _).preimage ?_
  rw [continuous_pi_iff]
  intro i
  apply continuous_apply

section CylCompact

variable {s : ℕ → Set (∀ i, α i)}

/-- A set of `Π i, α i`, preimage of the cylinder with compact base which is an `ε`
approximation of `s n`. Preimage of `cyl_compact'` by the projection from `Π i, α i` to
`Π i : allProj hs, α i`. -/
def cylCompact
    (hP_inner : ∀ J, (P J).InnerRegular (fun s => IsCompact s ∧ IsClosed s) MeasurableSet)
    (hs : ∀ n, s n ∈ cylinders α) (ε : ℝ≥0∞) (hε : 0 < ε) (n : ℕ) : Set (∀ i, α i) :=
  cylinder (Js (hs n))
    (innerCompact hP_inner (Js (hs n)) (As (hs n)) (cylinders.measurableSet _) ε hε)

theorem cylCompact_subset
    (hP_inner : ∀ J, (P J).InnerRegular (fun s => IsCompact s ∧ IsClosed s) MeasurableSet)
    (hs : ∀ n, s n ∈ cylinders α) (ε : ℝ≥0∞) (hε : 0 < ε) (n : ℕ) :
    cylCompact hP_inner hs ε hε n ⊆ s n := by
  intro x hx
  rw [cylinders.eq_cylinder (hs n), mem_cylinder]
  simp only [mem_preimage, cylCompact, mem_cylinder] at hx 
  exact innerCompact_subset _ _ _ _ _ _ hx

theorem cylCompact_eq_preimage_cylCompact'
    (hP_inner : ∀ J, (P J).InnerRegular (fun s => IsCompact s ∧ IsClosed s) MeasurableSet)
    (hs : ∀ n, s n ∈ cylinders α) (ε : ℝ≥0∞) (hε : 0 < ε) (n : ℕ) :
    cylCompact hP_inner hs ε hε n =
      (fun (f : ∀ i, α i) (i : allProj hs) => f i) ⁻¹' cylCompact' hP_inner hs ε hε n :=
  rfl

theorem preimage_cylCompact_subset
    (hP_inner : ∀ J, (P J).InnerRegular (fun s => IsCompact s ∧ IsClosed s) MeasurableSet)
    (hs : ∀ n, s n ∈ cylinders α) (ε : ℝ≥0∞) (hε : 0 < ε) (n : ℕ) :
    cylCompact hP_inner hs ε hε n ⊆ s n :=
  preimage_cylCompact'_subset hP_inner hs ε hε n

theorem isClosed_cylCompact
    (hP_inner : ∀ J, (P J).InnerRegular (fun s => IsCompact s ∧ IsClosed s) MeasurableSet)
    (hs : ∀ n, s n ∈ cylinders α) (ε : ℝ≥0∞) (hε : 0 < ε) (n : ℕ) :
    IsClosed (cylCompact hP_inner hs ε hε n) := by
  refine (isClosed_innerCompact hP_inner _ _ _ _ _).preimage ?_
  rw [continuous_pi_iff]
  intro i
  apply continuous_apply

theorem diff_eq_cylCompact
    (hP_inner : ∀ J, (P J).InnerRegular (fun s => IsCompact s ∧ IsClosed s) MeasurableSet)
    (hs : ∀ n, s n ∈ cylinders α) (ε : ℝ≥0∞) (hε : 0 < ε) (n : ℕ) :
    s n \
        cylinder (Js (hs n))
          (As (hs n) \
            innerCompact hP_inner (Js (hs n)) (As (hs n)) (cylinders.measurableSet _) ε hε) =
      cylCompact hP_inner hs ε hε n := by
  ext1 x
  rw [mem_diff, cylCompact, mem_cylinder, mem_cylinder]
  simp only [mem_diff, not_and, not_not_mem]
  refine' ⟨fun h => h.2 _, fun h => ⟨_, fun _ => h⟩⟩
  · have h' := h.1
    rwa [cylinders.eq_cylinder (hs n)] at h' 
  · rw [cylinders.eq_cylinder (hs n), mem_cylinder]
    exact innerCompact_subset _ _ _ _ ε _ h

theorem cylCompact_mem_cylinders
    (hP_inner : ∀ J, (P J).InnerRegular (fun s => IsCompact s ∧ IsClosed s) MeasurableSet)
    (hs : ∀ n, s n ∈ cylinders α) (ε : ℝ≥0∞) (hε : 0 < ε) (n : ℕ) :
    cylCompact hP_inner hs ε hε n ∈ cylinders α :=
  cylinder_mem_cylinders _ _ (measurableSet_innerCompact _ _ _ _ _ _)

end CylCompact

variable {s : ℕ → Set (∀ i, α i)}

/-- Intersection of `cyl_compact i (ε / 2 ^ (i + 2))` for `i ≤ n`. These cylinders have compact
bases and are `ε / 2 ^ (i + 2)` approximations of `s i`.
`C n` is a closed, nonempty cylinder. -/
def c (hP_inner : ∀ J, (P J).InnerRegular (fun s => IsCompact s ∧ IsClosed s) MeasurableSet)
    (hs : ∀ n, s n ∈ cylinders α) (ε : ℝ≥0∞) (hε : 0 < ε) (n : ℕ) : Set (∀ i, α i) :=
  ⋂ i ≤ n,
    cylCompact hP_inner hs (ε / 2 ^ (i + 2)) (ENNReal.div_pos_iff.mpr ⟨hε.ne', by norm_num⟩) i

theorem c_subset_cylCompact
    (hP_inner : ∀ J, (P J).InnerRegular (fun s => IsCompact s ∧ IsClosed s) MeasurableSet)
    (hs : ∀ n, s n ∈ cylinders α) (ε : ℝ≥0∞) (hε : 0 < ε) (n i : ℕ) (hi : i ≤ n) :
    c hP_inner hs ε hε n ⊆
      cylCompact hP_inner hs (ε / 2 ^ (i + 2)) (ENNReal.div_pos_iff.mpr ⟨hε.ne', by norm_num⟩) i :=
  biInter_subset_of_mem hi

theorem c_subset
    (hP_inner : ∀ J, (P J).InnerRegular (fun s => IsCompact s ∧ IsClosed s) MeasurableSet)
    (hs : ∀ n, s n ∈ cylinders α) (ε : ℝ≥0∞) (hε : 0 < ε) (n : ℕ) : c hP_inner hs ε hε n ⊆ s n :=
  (c_subset_cylCompact hP_inner hs ε hε n n le_rfl).trans (cylCompact_subset hP_inner hs _ _ n)

theorem diff_subset_c
    (hP_inner : ∀ J, (P J).InnerRegular (fun s => IsCompact s ∧ IsClosed s) MeasurableSet)
    (hs : ∀ n, s n ∈ cylinders α) (hs_anti : Antitone s) (ε : ℝ≥0∞) (hε : 0 < ε) (n : ℕ) :
    (s n \
        ⋃ i ≤ n,
          cylinder (Js (hs i))
            (As (hs i) \
              innerCompact hP_inner (Js (hs i)) (As (hs i)) (cylinders.measurableSet _)
                (ε / 2 ^ (i + 2)) (ENNReal.div_pos_iff.mpr ⟨hε.ne', by norm_num⟩))) ⊆
      c hP_inner hs ε hε n := by
  have hsn_eq_Inter : s n = ⋂ i ≤ n, s i := le_antisymm (le_iInf₂ fun i hi => hs_anti hi)
    (iInf₂_le (κ := fun i ↦ i ≤ n) (f := fun i _ ↦ s i) n le_rfl)
  rw [hsn_eq_Inter]
  refine' (bInter_diff_bUnion_subset _ _ _).trans_eq _
  simp_rw [c]
  refine iInter_congr fun i ↦ ?_
  refine iInter_congr fun _ ↦ ?_
  exact diff_eq_cylCompact hP_inner hs (ε / 2 ^ (i + 2))
    (ENNReal.div_pos_iff.mpr ⟨hε.ne', by norm_num⟩) i

theorem c_mem_cylinders
    (hP_inner : ∀ J, (P J).InnerRegular (fun s => IsCompact s ∧ IsClosed s) MeasurableSet)
    (hs : ∀ n, s n ∈ cylinders α) (ε : ℝ≥0∞) (hε : 0 < ε) (n : ℕ) :
    c hP_inner hs ε hε n ∈ cylinders α := by
  refine' iInter_le_mem_cylinders (fun i => _) n
  exact
    cylCompact_mem_cylinders hP_inner hs (ε / 2 ^ (i + 2))
      (ENNReal.div_pos_iff.mpr ⟨hε.ne', by norm_num⟩) i

theorem isClosed_c
    (hP_inner : ∀ J, (P J).InnerRegular (fun s => IsCompact s ∧ IsClosed s) MeasurableSet)
    (hs : ∀ n, s n ∈ cylinders α) (ε : ℝ≥0∞) (hε : 0 < ε) (n : ℕ) :
    IsClosed (c hP_inner hs ε hε n) :=
  isClosed_biInter fun i _ => isClosed_cylCompact hP_inner hs _ _ i

/-- Intersection of `cyl_compact i (ε / 2 ^ (i + 2))` for `i ≤ n`. These cylinders have compact
bases and are `ε / 2 ^ (i + 2)` approximations of `s i`.
`C' n` is nonempty and closed. -/
def c' (hP_inner : ∀ J, (P J).InnerRegular (fun s => IsCompact s ∧ IsClosed s) MeasurableSet)
    (hs : ∀ n, s n ∈ cylinders α) (ε : ℝ≥0∞) (hε : 0 < ε) (n : ℕ) : Set (∀ i : allProj hs, α i) :=
  ⋂ i ≤ n,
    cylCompact' hP_inner hs (ε / 2 ^ (i + 2)) (ENNReal.div_pos_iff.mpr ⟨hε.ne', by norm_num⟩) i

theorem c'_subset_cylCompact'
    (hP_inner : ∀ J, (P J).InnerRegular (fun s => IsCompact s ∧ IsClosed s) MeasurableSet)
    (hs : ∀ n, s n ∈ cylinders α) (ε : ℝ≥0∞) (hε : 0 < ε) (n i : ℕ) (hi : i ≤ n) :
    c' hP_inner hs ε hε n ⊆
      cylCompact' hP_inner hs (ε / 2 ^ (i + 2)) (ENNReal.div_pos_iff.mpr ⟨hε.ne', by norm_num⟩) i :=
  biInter_subset_of_mem hi

theorem isClosed_c'
    (hP_inner : ∀ J, (P J).InnerRegular (fun s => IsCompact s ∧ IsClosed s) MeasurableSet)
    (hs : ∀ n, s n ∈ cylinders α) (ε : ℝ≥0∞) (hε : 0 < ε) (n : ℕ) :
    IsClosed (c' hP_inner hs ε hε n) :=
  isClosed_biInter fun i _ => isClosed_cylCompact' hP_inner hs _ _ i

theorem c_eq_preimage_c'
    (hP_inner : ∀ J, (P J).InnerRegular (fun s => IsCompact s ∧ IsClosed s) MeasurableSet)
    (hs : ∀ n, s n ∈ cylinders α) (ε : ℝ≥0∞) (hε : 0 < ε) (n : ℕ) :
    c hP_inner hs ε hε n = (fun f (i : allProj hs) => f i) ⁻¹' c' hP_inner hs ε hε n := by
  rw [c, c']; simp_rw [preimage_iInter]; congr

abbrev iC (hP_inner : ∀ J, (P J).InnerRegular (fun s => IsCompact s ∧ IsClosed s) MeasurableSet)
    (hs : ∀ n, s n ∈ cylinders α) (ε : ℝ≥0∞) (hε : 0 < ε)
    [∀ i : allProj hs, DecidablePred fun n => ↑i ∈ Js (hs n)] (i : allProj hs) :=
  innerCompact hP_inner (Js (hs (indexProj hs i))) (As (hs (indexProj hs i)))
    (cylinders.measurableSet _) (ε / 2 ^ (indexProj hs i + 2))
    (ENNReal.div_pos_iff.mpr ⟨hε.ne', by norm_num⟩)

/-- A set of `Π i : allProj hs, α i` such that for all `i`, `x i` belongs to the projection of the
compact cylinder approximating `s (indexProj hs i)` with precision
`ε / 2 ^ ((indexProj hs i) + 2)`.
TODO: explain where that monster comes from.
It is compact, satisfies that `C' n ∩ piInnerCompact` is nonempty for all `n` and it contains
`⋂ n, C' n`. It thus suffices to show that `⋂ n, (C' n ∩ piInnerCompact)` is nonempty in order
to obtain that `⋂ n, C' n` is nonempty. The advantage of doing so is that `C' n ∩ piInnerCompact`
is compact for all `n`, while `C' n` is only closed. Compactness is crucial to be able to apply
`is_compact.nonempty_Inter_of_sequence_nonempty_compact_closed`. -/
def piInnerCompact
    (hP_inner : ∀ J, (P J).InnerRegular (fun s => IsCompact s ∧ IsClosed s) MeasurableSet)
    (hs : ∀ n, s n ∈ cylinders α) (ε : ℝ≥0∞) (hε : 0 < ε)
    [∀ i : allProj hs, DecidablePred fun n => ↑i ∈ Js (hs n)] : Set (∀ i : allProj hs, α i) :=
  {x : ∀ i : allProj hs, α i |
    ∀ i,
      x i ∈
        (fun a : ∀ j : Js (hs (indexProj hs i)), α j => a ⟨i, mem_indexProj hs i⟩) ''
          iC hP_inner hs ε hε i}

theorem isCompact_piInnerCompact
    (hP_inner : ∀ J, (P J).InnerRegular (fun s => IsCompact s ∧ IsClosed s) MeasurableSet)
    (hs : ∀ n, s n ∈ cylinders α) (ε : ℝ≥0∞) (hε : 0 < ε)
    [∀ i : allProj hs, DecidablePred fun n => ↑i ∈ Js (hs n)] :
    IsCompact (piInnerCompact hP_inner hs ε hε) :=
  isCompact_pi_infinite fun _ =>
    (isCompact_innerCompact hP_inner _ _ _ _ _).image (continuous_apply _)

theorem piInnerCompact_eq_pi_univ
    (hP_inner : ∀ J, (P J).InnerRegular (fun s => IsCompact s ∧ IsClosed s) MeasurableSet)
    (hs : ∀ n, s n ∈ cylinders α) (ε : ℝ≥0∞) (hε : 0 < ε)
    [∀ i : allProj hs, DecidablePred fun n => ↑i ∈ Js (hs n)] :
    piInnerCompact hP_inner hs ε hε =
      pi univ fun i =>
        (fun a : ∀ j : Js (hs (indexProj hs i)), α j => a ⟨i, mem_indexProj hs i⟩) ''
          iC hP_inner hs ε hε i := by
  ext1 x; simp only [piInnerCompact, mem_univ_pi]; rfl

theorem isClosed_piInnerCompact
    (hP_inner : ∀ J, (P J).InnerRegular (fun s => IsCompact s ∧ IsClosed s) MeasurableSet)
    (hs : ∀ n, s n ∈ cylinders α) (ε : ℝ≥0∞) (hε : 0 < ε)
    [∀ i : allProj hs, DecidablePred fun n => ↑i ∈ Js (hs n)] :
    IsClosed (piInnerCompact hP_inner hs ε hε) := by
  rw [piInnerCompact_eq_pi_univ]
  refine' isClosed_set_pi fun i _ => _
  exact isClosed_proj (isCompact_innerCompact _ _ _ _ _ _) (isClosed_innerCompact _ _ _ _ _ _) _

theorem nonempty_piInnerCompact
    (hP_inner : ∀ J, (P J).InnerRegular (fun s => IsCompact s ∧ IsClosed s) MeasurableSet)
    (hs : ∀ n, s n ∈ cylinders α) {ε : ℝ≥0∞} (hε : 0 < ε)
    (hs_ge : ∀ n, ε ≤ P (Js (hs n)) (As (hs n)))
    [∀ i : allProj hs, DecidablePred fun n => ↑i ∈ Js (hs n)] :
    (piInnerCompact hP_inner hs ε hε).Nonempty := by
  have hε_ne_top : ε ≠ ∞ := ne_top_of_le_ne_top (measure_ne_top _ _) (hs_ge 0)
  have h := fun i : allProj hs =>
    nonempty_innerCompact hP_inner (Js (hs (indexProj hs i))) (As (hs (indexProj hs i)))
      (cylinders.measurableSet _) (ε / 2 ^ (indexProj hs i + 2))
      (ENNReal.div_pos_iff.mpr ⟨hε.ne', by norm_num⟩) ?_
  swap;
  · refine' lt_of_lt_of_le _ (hs_ge (indexProj hs i))
    rw [ENNReal.div_lt_iff]
    · conv_lhs => rw [← mul_one ε]
      rw [ENNReal.mul_lt_mul_left hε.ne' hε_ne_top]
      norm_cast
      refine' one_lt_two.trans _
      conv_lhs => rw [← pow_one 2]
      rw [pow_lt_pow_iff (one_lt_two : 1 < 2)]
      norm_num
    · left; norm_num
    · left
      simp only [ne_eq, ENNReal.pow_eq_top_iff, add_eq_zero, and_false, not_false_eq_true, and_true]
  let b i := (h i).some
  have hb_mem : ∀ i, b i ∈ iC hP_inner hs ε hε i := fun i => (h i).choose_spec
  let a : ∀ i : allProj hs, α i := fun i => b i ⟨i, mem_indexProj hs i⟩
  refine' ⟨a, _⟩
  simp only [piInnerCompact, mem_image, SetCoe.forall, mem_setOf_eq]
  exact fun j hj => ⟨b ⟨j, hj⟩, hb_mem _, rfl⟩

theorem iInter_c'_subset_piInnerCompact
    (hP_inner : ∀ J, (P J).InnerRegular (fun s => IsCompact s ∧ IsClosed s) MeasurableSet)
    (hs : ∀ n, s n ∈ cylinders α) (ε : ℝ≥0∞) (hε : 0 < ε)
    [∀ i : allProj hs, DecidablePred fun n => ↑i ∈ Js (hs n)] :
    (⋂ n, c' hP_inner hs ε hε n) ⊆ piInnerCompact hP_inner hs ε hε :=
  by
  intro x hx
  rw [mem_iInter] at hx 
  rw [piInnerCompact]
  simp only [mem_image, SetCoe.forall, mem_setOf_eq]
  intro i hi
  specialize hx (indexProj hs ⟨i, hi⟩)
  have hx' :=
    c'_subset_cylCompact' hP_inner hs ε hε (indexProj hs ⟨i, hi⟩) (indexProj hs ⟨i, hi⟩) le_rfl
      hx
  rw [cylCompact', mem_preimage] at hx' 
  exact ⟨fun i : Js (hs (indexProj hs ⟨i, hi⟩)) => x ⟨i, subset_allProj hs _ i.2⟩, hx', rfl⟩

variable [Nonempty (∀ i, α i)]

theorem kolContent_c (hP : IsProjectiveMeasureFamily P)
    (hP_inner : ∀ J, (P J).InnerRegular (fun s => IsCompact s ∧ IsClosed s) MeasurableSet)
    (hs : ∀ n, s n ∈ cylinders α) (hs_anti : Antitone s) {ε : ℝ≥0∞} (hε : 0 < ε)
    (hs_ge : ∀ n, ε ≤ kolContent hP (s n)) (n : ℕ) : ε / 2 ≤ kolContent hP (c hP_inner hs ε hε n) :=
  by
  have hε_ne_top : ε ≠ ∞ := by
    refine' ne_top_of_le_ne_top _ (hs_ge 0)
    rw [kolContent_eq hP (hs 0)]
    exact measure_ne_top _ _
  let J n := Js (hs n)
  let A n := As (hs n)
  have hA_meas : ∀ n, MeasurableSet (A n) := fun n => cylinders.measurableSet (hs n)
  let K n :=
    innerCompact hP_inner (J n) (A n) (cylinders.measurableSet _) (ε / 2 ^ (n + 2))
      (ENNReal.div_pos_iff.mpr ⟨hε.ne', by norm_num⟩)
  have hK_meas : ∀ n, MeasurableSet (K n) := fun n => measurableSet_innerCompact _ _ _ _ _ _
  have hC_diff : (s n \ ⋃ i ≤ n, cylinder (Js (hs i)) (A i \ K i)) ⊆ c hP_inner hs ε hε n :=
    diff_subset_c hP_inner hs hs_anti ε hε n
  have hdiff_mem : ∀ n, cylinder (J n) (A n \ K n) ∈ cylinders α := fun n =>
    cylinder_mem_cylinders _ _ ((hA_meas n).diff (hK_meas n))
  have hUnion_mem : (⋃ i ≤ n, cylinder (J i) (A i \ K i)) ∈ cylinders α :=
    iUnion_le_mem_cylinders hdiff_mem n
  have hUnion_kol : kolContent hP (⋃ i ≤ n, cylinder (J i) (A i \ K i)) ≤ ε / 2 :=
    by
    refine' (kolContent_iUnion_le hP hdiff_mem n).trans _
    calc
      ∑ i in Finset.range (n + 1), kolContent hP (cylinder (J i) (A i \ K i)) =
          ∑ i in Finset.range (n + 1), P (J i) (A i \ K i) :=
        by
        congr with i : 1
        rw [kolContent_congr hP (hdiff_mem i) rfl ((hA_meas i).diff (hK_meas i))]
      _ ≤ ∑ i in Finset.range (n + 1), ε / 2 ^ (i + 2) :=
        (Finset.sum_le_sum fun i _ => measure_diff_innerCompact _ _ _ _ _ _)
      _ ≤ ε / 2 := todo ε n
  calc
    ε / 2 = ε - ε / 2 := (ENNReal.sub_half hε_ne_top).symm
    _ ≤ kolContent hP (s n) - kolContent hP (⋃ i ≤ n, cylinder (J i) (A i \ K i)) :=
      (tsub_le_tsub (hs_ge n) hUnion_kol)
    _ ≤ kolContent hP (s n \ ⋃ i ≤ n, cylinder (J i) (A i \ K i)) :=
      (kolContent_diff hP (hs n) hUnion_mem)
    _ ≤ kolContent hP (c hP_inner hs ε hε n) :=
      kolContent_mono hP (diff_mem_cylinders (hs n) hUnion_mem) (c_mem_cylinders _ _ _ _ n) hC_diff

theorem nonempty_c (hP : IsProjectiveMeasureFamily P)
    (hP_inner : ∀ J, (P J).InnerRegular (fun s => IsCompact s ∧ IsClosed s) MeasurableSet)
    (hs : ∀ n, s n ∈ cylinders α) (hs_anti : Antitone s) {ε : ℝ≥0∞} (hε : 0 < ε)
    (hs_ge : ∀ n, ε ≤ kolContent hP (s n)) (n : ℕ) : (c hP_inner hs ε hε n).Nonempty := by
  by_contra h_empty
  rw [not_nonempty_iff_eq_empty] at h_empty 
  have hC_kol := kolContent_c hP hP_inner hs hs_anti hε hs_ge n
  rw [h_empty, addContent_empty] at hC_kol 
  simp only [nonpos_iff_eq_zero, ENNReal.div_eq_zero_iff, or_false] at hC_kol
  exact absurd hC_kol (ne_of_lt hε).symm

theorem nonempty_c' (hP : IsProjectiveMeasureFamily P)
    (hP_inner : ∀ J, (P J).InnerRegular (fun s => IsCompact s ∧ IsClosed s) MeasurableSet)
    (hs : ∀ n, s n ∈ cylinders α) (hs_anti : Antitone s) {ε : ℝ≥0∞} (hε : 0 < ε)
    (hs_ge : ∀ n, ε ≤ kolContent hP (s n)) (n : ℕ) : (c' hP_inner hs ε hε n).Nonempty := by
  have h := nonempty_c hP hP_inner hs hs_anti hε hs_ge n
  rw [c_eq_preimage_c'] at h 
  exact nonempty_of_nonempty_preimage h

theorem nonempty_c'_inter_piInnerCompact (hP : IsProjectiveMeasureFamily P)
    (hP_inner : ∀ J, (P J).InnerRegular (fun s => IsCompact s ∧ IsClosed s) MeasurableSet)
    (hs : ∀ n, s n ∈ cylinders α) (hs_anti : Antitone s) {ε : ℝ≥0∞} (hε : 0 < ε)
    (hs_ge : ∀ n, ε ≤ kolContent hP (s n)) (n : ℕ)
    [∀ i : allProj hs, DecidablePred fun n => ↑i ∈ Js (hs n)] :
    (c' hP_inner hs ε hε n ∩ piInnerCompact hP_inner hs ε hε).Nonempty :=
  by
  have hεP : ∀ n, ε ≤ P (Js (hs n)) (As (hs n)) :=
    by
    intro n
    convert hs_ge n
    rw [kolContent_congr hP (hs n) (cylinders.eq_cylinder (hs n)) (cylinders.measurableSet (hs n))]
  let x := (nonempty_piInnerCompact hP_inner hs hε hεP).some
  have hx : x ∈ piInnerCompact hP_inner hs ε hε :=
    (nonempty_piInnerCompact hP_inner hs hε hεP).choose_spec
  let y := (nonempty_c' hP hP_inner hs hs_anti hε hs_ge n).some
  have hy : y ∈ c' hP_inner hs ε hε n := (nonempty_c' hP hP_inner hs hs_anti hε hs_ge n).choose_spec
  let z := fun i : allProj hs => if indexProj hs i ≤ n then y i else x i
  refine' ⟨z, mem_inter _ _⟩
  · simp_rw [c', mem_iInter]
    intro i hi
    simp only [cylCompact', mem_preimage]
    classical
    have :
      (fun j : Js (hs i) =>
          ite (indexProj hs ⟨j, subset_allProj hs i j.2⟩ ≤ n) (y ⟨j, subset_allProj hs i j.2⟩)
            (x ⟨j, subset_allProj hs i j.2⟩)) =
        fun j : Js (hs i) => y ⟨j, subset_allProj hs i j.2⟩ :=
      by
      ext1 j
      rw [if_pos]
      refine' le_trans (le_of_eq _) ((indexProj_le hs i j).trans hi)
      congr
    rw [this]
    change
      y ∈
        cylCompact' hP_inner hs (ε / 2 ^ (i + 2)) (ENNReal.div_pos_iff.mpr ⟨hε.ne', by norm_num⟩) i
    exact c'_subset_cylCompact' hP_inner hs ε hε n i hi hy
  · simp only [piInnerCompact, mem_image, SetCoe.forall, mem_setOf_eq]
    intro i hi
    by_cases hi_le : indexProj hs ⟨i, hi⟩ ≤ n
    · let m := indexProj hs ⟨i, hi⟩
      have hy' :
        y ∈
          cylCompact' hP_inner hs (ε / 2 ^ (m + 2)) (ENNReal.div_pos_iff.mpr ⟨hε.ne', by norm_num⟩)
            m :=
        c'_subset_cylCompact' hP_inner hs ε hε n m hi_le hy
      rw [cylCompact', mem_preimage] at hy' 
      refine' ⟨fun j => y ⟨j, subset_allProj hs _ j.2⟩, hy', _⟩
      simp_rw [if_pos hi_le]
    · simp only [piInnerCompact, mem_image, SetCoe.forall, mem_setOf_eq] at hx 
      specialize hx i hi
      obtain ⟨x', hx'_mem, hx'_eq⟩ := hx
      refine' ⟨x', hx'_mem, _⟩
      simp_rw [if_neg hi_le]
      exact hx'_eq

theorem nonempty_iInter_c' (hP : IsProjectiveMeasureFamily P)
    (hP_inner : ∀ J, (P J).InnerRegular (fun s => IsCompact s ∧ IsClosed s) MeasurableSet)
    (hs : ∀ n, s n ∈ cylinders α) (hs_anti : Antitone s) {ε : ℝ≥0∞} (hε : 0 < ε)
    (hs_ge : ∀ n, ε ≤ kolContent hP (s n))
    [∀ i : allProj hs, DecidablePred fun n => ↑i ∈ Js (hs n)] :
    (⋂ i, c' hP_inner hs ε hε i).Nonempty :=
  by
  suffices ((⋂ i, c' hP_inner hs ε hε i) ∩ piInnerCompact hP_inner hs ε hε).Nonempty by
    rwa [inter_eq_left_iff_subset.mpr (iInter_c'_subset_piInnerCompact hP_inner hs ε hε)] at this 
  rw [iInter_inter]
  refine'
    IsCompact.nonempty_iInter_of_sequence_nonempty_compact_closed
      (fun i => c' hP_inner hs ε hε i ∩ piInnerCompact hP_inner hs ε hε) _ _ _ _
  · intro i
    refine' inter_subset_inter _ subset_rfl
    simp_rw [c', Set.bInter_le_succ]
    exact inter_subset_left _ _
  · exact fun n => nonempty_c'_inter_piInnerCompact hP hP_inner hs hs_anti hε hs_ge n
  · exact (isCompact_piInnerCompact hP_inner _ _ _).inter_left (isClosed_c' _ _ _ _ _)
  · exact fun _ => IsClosed.inter (isClosed_c' _ _ _ _ _) (isClosed_piInnerCompact _ _ _ _)

theorem continuous_at_empty_aux (hP : IsProjectiveMeasureFamily P)
    (hP_inner : ∀ J, (P J).InnerRegular (fun s => IsCompact s ∧ IsClosed s) MeasurableSet)
    (hs : ∀ n, s n ∈ cylinders α) (hs_anti : Antitone s) {ε : ℝ≥0∞} (hε : 0 < ε)
    (hs_ge : ∀ n, ε ≤ kolContent hP (s n)) : (⋂ n, s n) ≠ ∅ :=
  by
  suffices (⋂ n, c hP_inner hs ε hε n).Nonempty
    by
    rw [nonempty_iff_ne_empty] at this 
    rw [Ne.def, ← subset_empty_iff] at this ⊢
    intro h
    refine' this ((iInter_mono fun i => _).trans h)
    exact c_subset hP_inner hs ε hε i
  classical
  simp_rw [c_eq_preimage_c']
  rw [← preimage_iInter, Function.Surjective.nonempty_preimage]
  · exact nonempty_iInter_c' hP hP_inner hs hs_anti hε hs_ge
  · intro x
    let y : ∀ i, α i := Nonempty.some inferInstance
    let z : ∀ i, α i := fun i : ι => if hi : i ∈ allProj hs then x ⟨i, hi⟩ else y i
    refine' ⟨z, _⟩
    ext1 i
    simp only [Subtype.coe_prop, dite_true]

theorem continuous_at_empty_kolContent (hP : IsProjectiveMeasureFamily P)
    (hP_inner : ∀ J, (P J).InnerRegular (fun s => IsCompact s ∧ IsClosed s) MeasurableSet)
    (hs : ∀ n : ℕ, s n ∈ cylinders α) (hs_anti : Antitone s) (hs_Inter : (⋂ n : ℕ, s n) = ∅) :
    Filter.Tendsto (fun n => kolContent hP (s n)) Filter.atTop (nhds 0) :=
  by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_contra h_freq_gt
  simp_rw [Filter.not_eventually, not_le] at h_freq_gt 
  refine' absurd hs_Inter _
  -- we suppose that the limit is not 0, and we will show that `⋂ (n : ℕ), s n` is not empty to
  -- obtain a contradition
  suffices h_forall : ∀ n, ε ≤ kolContent hP (s n)
  · exact continuous_at_empty_aux hP hP_inner hs hs_anti hε h_forall
  rw [Filter.frequently_atTop] at h_freq_gt 
  intro n
  obtain ⟨m, hnm, hm⟩ := h_freq_gt n
  exact hm.le.trans (kolContent_mono hP (hs m) (hs n) (hs_anti hnm))

end ContinuityAtEmpty

section InnerRegularAssumption

variable [Nonempty (∀ i, α i)] [∀ i, TopologicalSpace (α i)] [∀ i, OpensMeasurableSpace (α i)]
  [∀ i, TopologicalSpace.SecondCountableTopology (α i)] [∀ I, IsFiniteMeasure (P I)]

theorem kolContent_sigma_additive_of_innerRegular (hP : IsProjectiveMeasureFamily P)
    (hP_inner : ∀ J, (P J).InnerRegular (fun s => IsCompact s ∧ IsClosed s) MeasurableSet)
    ⦃f : ℕ → Set (∀ i, α i)⦄ (hf : ∀ i, f i ∈ cylinders α) (hf_Union : (⋃ i, f i) ∈ cylinders α)
    (h_disj : Pairwise (Disjoint on f)) : kolContent hP (⋃ i, f i) = ∑' i, kolContent hP (f i) :=
  by
  refine' countably_additive_addContent_of_todo setRing_cylinders _ _ _ hf hf_Union h_disj
  · exact fun hx => kolContent_ne_top _ hx
  · exact fun s hs => continuous_at_empty_kolContent hP hP_inner hs

theorem kolContent_countably_subadditive_of_innerRegular (hP : IsProjectiveMeasureFamily P)
    (hP_inner : ∀ J, (P J).InnerRegular (fun s => IsCompact s ∧ IsClosed s) MeasurableSet)
    ⦃f : ℕ → Set (∀ i, α i)⦄ (hf : ∀ i, f i ∈ cylinders α) (hf_Union : (⋃ i, f i) ∈ cylinders α) :
    kolContent hP (⋃ i, f i) ≤ ∑' i, kolContent hP (f i) :=
  (kolContent hP).countably_subadditive_of_countably_additive setRing_cylinders
    (kolContent_sigma_additive_of_innerRegular hP hP_inner) f hf hf_Union

end InnerRegularAssumption

/-- TODO name. Remove this? -/
noncomputable def projectiveLimitWithWeakestHypotheses [∀ i, PseudoEMetricSpace (α i)]
    [∀ i, BorelSpace (α i)] [∀ i, TopologicalSpace.SecondCountableTopology (α i)]
    [∀ i, CompleteSpace (α i)] [Nonempty (∀ i, α i)] (P : ∀ J : Finset ι, Measure (∀ j : J, α j))
    [∀ i, IsFiniteMeasure (P i)] (hP : IsProjectiveMeasureFamily P) : Measure (∀ i, α i) :=
  Measure.ofAddContent setSemiringCylinders generateFrom_cylinders (kolContent hP)
    (kolContent_countably_subadditive_of_innerRegular hP fun J =>
      innerRegular_isCompact_isClosed_measurableSet_of_complete_countable (P J))

section Polish

variable [Nonempty (∀ i, α i)] [∀ i, TopologicalSpace (α i)] [∀ i, BorelSpace (α i)]
  [∀ i, PolishSpace (α i)] [∀ I, IsFiniteMeasure (P I)]

theorem kolContent_sigma_additive (hP : IsProjectiveMeasureFamily P) ⦃f : ℕ → Set (∀ i, α i)⦄
    (hf : ∀ i, f i ∈ cylinders α) (hf_Union : (⋃ i, f i) ∈ cylinders α)
    (h_disj : Pairwise (Disjoint on f)) : kolContent hP (⋃ i, f i) = ∑' i, kolContent hP (f i) :=
  by
  haveI : ∀ i, TopologicalSpace.SecondCountableTopology (α i) := fun i =>
    PolishSpace.secondCountableTopology
  refine' kolContent_sigma_additive_of_innerRegular hP _ hf hf_Union h_disj
  exact fun J => PolishSpace.innerRegular_isCompact_measurableSet (P J)

theorem kolContent_countably_subadditive (hP : IsProjectiveMeasureFamily P) ⦃f : ℕ → Set (∀ i, α i)⦄
    (hf : ∀ i, f i ∈ cylinders α) (hf_Union : (⋃ i, f i) ∈ cylinders α) :
    kolContent hP (⋃ i, f i) ≤ ∑' i, kolContent hP (f i) :=
  by
  haveI : ∀ i, TopologicalSpace.SecondCountableTopology (α i) := fun i =>
    PolishSpace.secondCountableTopology
  refine' kolContent_countably_subadditive_of_innerRegular hP _ hf hf_Union
  exact fun J => PolishSpace.innerRegular_isCompact_measurableSet (P J)

/-- Projective limit of a projective measure family. -/
noncomputable def projectiveLimit (P : ∀ J : Finset ι, Measure (∀ j : J, α j))
    [∀ i, IsFiniteMeasure (P i)] (hP : IsProjectiveMeasureFamily P) : Measure (∀ i, α i) :=
  Measure.ofAddContent setSemiringCylinders generateFrom_cylinders (kolContent hP)
    (kolContent_countably_subadditive hP)

/-- **Kolmogorov extension theorem**: for any projective measure family `P`, there exists a measure
on `Π i, α i` which is the projective limit of `P`. That measure is given by
`projective_limit P hP`, where `hP : is_projective_measure_family P`.
The projective limit is unique: see `is_projective_limit_unique`. -/
theorem isProjectiveLimit_projectiveLimit (hP : IsProjectiveMeasureFamily P) :
    IsProjectiveLimit (projectiveLimit P hP) P := by
  intro J
  ext1 s hs
  rw [Measure.map_apply _ hs]
  swap; · apply measurable_proj
  have h_mem : (fun (x : ∀ i : ι, (fun i : ι => α i) i) (i : ↥J) => x ↑i) ⁻¹' s ∈ cylinders α := by
    rw [mem_cylinders]; exact ⟨J, s, hs, rfl⟩
  rw [projectiveLimit, Measure.ofAddContent_eq _ _ _ _ h_mem, kolContent_congr hP h_mem rfl hs]

instance isFiniteMeasure_projectiveLimit [Nonempty ι] (hP : IsProjectiveMeasureFamily P) :
    IsFiniteMeasure (projectiveLimit P hP) :=
  isFiniteMeasure_of_isProjectiveLimit (isProjectiveLimit_projectiveLimit hP)

instance isProbabilityMeasure_projectiveLimit [hι : Nonempty ι]
    {P : ∀ J : Finset ι, Measure (∀ j : J, α j)} [∀ i, IsProbabilityMeasure (P i)]
    (hP : IsProjectiveMeasureFamily P) : IsProbabilityMeasure (projectiveLimit P hP) := by
  constructor
  let I := ({hι.some} : Finset ι)
  rw [← cylinder_univ I,
    (isProjectiveLimit_projectiveLimit hP).measure_cylinder _ MeasurableSet.univ]
  exact measure_univ

end Polish

end MeasureTheory

