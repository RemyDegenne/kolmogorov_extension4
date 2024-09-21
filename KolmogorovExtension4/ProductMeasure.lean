/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import KolmogorovExtension4.IonescuTulceaKernel

open MeasureTheory MeasurableSpace ProbabilityTheory Finset ENNReal Filter Topology Function Kernel Preorder

namespace MeasureTheory

section Preliminaries

variable {ι : Type*}

theorem preimage_proj {α : ι → Type*} (I J : Finset ι) [∀ i : ι, Decidable (i ∈ I)]
    (hIJ : I ⊆ J) (s : (i : I) → Set (α i)) :
    (restrict₂ hIJ) ⁻¹' (Set.univ.pi s) =
    (@Set.univ J).pi (fun j ↦ if h : j.1 ∈ I then s ⟨j.1, h⟩ else Set.univ) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Subtype.forall]
  refine ⟨fun h i hi ↦ ?_, fun h i i_mem ↦ by simpa [i_mem] using h i (hIJ i_mem)⟩
  split_ifs with i_mem
  · exact h i i_mem
  · trivial

variable {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
variable (μ : (i : ι) → Measure (X i)) [hμ : ∀ i, IsProbabilityMeasure (μ i)]

/-- Consider a family of probability measures. You can take their products for any fimite
subfamily. This gives a projective family of measures, see `IsProjectiveMeasureFamily`. -/
theorem isProjectiveMeasureFamily_pi :
    IsProjectiveMeasureFamily (fun I : Finset ι ↦ (Measure.pi (fun i : I ↦ μ i))) := by
  refine fun I J hJI ↦ Measure.pi_eq (fun s ms ↦ ?_)
  classical
  rw [Measure.map_apply (measurable_restrict₂ hJI) (MeasurableSet.univ_pi ms),
    preimage_proj J I hJI, Measure.pi_pi]
  let g := fun i ↦ (μ i) (if hi : i ∈ J then s ⟨i, hi⟩ else Set.univ)
  conv_lhs => change ∏ i : I, g i
  have h2 : univ.prod (fun i : J ↦ (μ i) (s i)) = univ.prod (fun i : J ↦ g i) :=
    Finset.prod_congr rfl (by simp [g])
  rw [h2, Finset.prod_coe_sort, Finset.prod_coe_sort,
    Finset.prod_subset hJI (fun _ h h' ↦ by simp [g, h, h'])]

theorem kolContent_eq_measure_pi [Fintype ι] {s : Set ((i : ι) → X i)} (hs : MeasurableSet s) :
    kolContent (isProjectiveMeasureFamily_pi μ) s = Measure.pi μ s := by
  let aux : ((i : univ) → X i) → ((i : ι) → X i) := fun x i ↦ x ⟨i, mem_univ i⟩
  have maux : Measurable aux := measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
  let t := aux ⁻¹' s
  have : s = cylinder Finset.univ t := by ext x; simp [t, aux]
  nth_rw 1 [this]
  rw [kolContent_cylinder _ (maux hs)]
  have : Measure.pi μ = (Measure.pi (fun i : @univ ι _ ↦ μ i)).map aux := by
    refine Measure.pi_eq fun a ma ↦ ?_
    rw [Measure.map_apply maux (MeasurableSet.univ_pi ma)]
    have : aux ⁻¹' Set.univ.pi a = Set.univ.pi (fun i : @univ ι _ ↦ a i) := by ext x; simp [aux]
    rw [this, Measure.pi_pi]
    simp
  rw [this, Measure.map_apply maux hs]

end Preliminaries

section Nat

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
variable (μ : (n : ℕ) → Measure (X n)) [hμ : ∀ n, IsProbabilityMeasure (μ n)]

lemma mem_Iic_zero {i : ℕ} (hi : i ∈ Iic 0) : 0 = i := (by simpa using hi : i = 0).symm

/-- `{0} = Ici 0`, version as a measurable equivalence for dependent functions. -/
def zer : (X 0) ≃ᵐ ((i : Iic 0) → X i) where
  toFun := fun x₀ i ↦ mem_Iic_zero i.2 ▸ x₀
  invFun := fun x ↦ x ⟨0, mem_Iic.2 <| _root_.le_refl 0⟩
  left_inv := fun x₀ ↦ by simp
  right_inv := fun x ↦ by
    ext i
    have : ⟨0, mem_Iic.2 <| _root_.le_refl 0⟩ = i := by simp [mem_Iic_zero i.2]
    cases this; rfl
  measurable_toFun := by
    refine measurable_pi_lambda _ (fun i ↦ ?_)
    simp_rw [eqRec_eq_cast]
    apply measurable_cast
    have : ⟨0, mem_Iic.2 <| _root_.le_refl 0⟩ = i := by simp [mem_Iic_zero i.2]
    cases this; rfl
  measurable_invFun := measurable_pi_apply _

/-- Infinite product measure indexed by `ℕ`. Use instead `Measure.productMeasure` for the case of a
general index space. -/
noncomputable def Measure.infinitePiNat : Measure ((n : ℕ) → X n) :=
  (Measure.pi (fun i : Iic 0 ↦ μ i)).bind
    (@ionescuTulceaKernel _ _
      (fun n ↦ const _ (μ (n + 1))) _ (ProbabilityMeasure.nonempty ⟨μ 0, hμ 0⟩) 0)

open Measure

instance {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {κ : Kernel X Y}
    [IsProbabilityMeasure μ] [IsMarkovKernel κ] : IsProbabilityMeasure (μ.bind κ) where
  measure_univ := by
    rw [bind_apply MeasurableSet.univ (Kernel.measurable κ)]
    simp

instance : IsProbabilityMeasure (infinitePiNat μ) := by
  rw [infinitePiNat]
  infer_instance

theorem er_succ_preimage_pi {n : ℕ} (hn : 0 < n) (s : (i : Ioc 0 (n + 1)) → Set (X i)) :
    er 0 n (n + 1) hn n.le_succ ⁻¹' Set.univ.pi s =
      (Set.univ.pi (fun i : Ioc 0 n ↦ s ⟨i.1, Ioc_subset_Ioc_right n.le_succ i.2⟩)) ×ˢ
        ((e n).symm ⁻¹' (s ⟨n + 1, right_mem_Ioc.2 n.succ_pos⟩)) := by
  ext p
  simp only [er, Nat.succ_eq_add_one, Nat.reduceAdd, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk,
    Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Subtype.forall, mem_Ioc, e,
    MeasurableEquiv.symm_mk, Equiv.coe_fn_symm_mk, Set.mem_prod]
  refine ⟨fun h ↦ ⟨fun i ⟨hi1, hi2⟩ ↦ ?_, ?_⟩, fun ⟨h1, h2⟩ i ⟨hi1, hi2⟩ ↦ ?_⟩
  · convert h i ⟨hi1, hi2.trans n.le_succ⟩
    rw [dif_pos hi2]
  · convert h (n + 1) ⟨n.succ_pos, _root_.le_refl _⟩
    simp
  · split_ifs with h
    · exact h1 i ⟨hi1, h⟩
    · cases (by omega : i = n + 1)
      exact h2

theorem kerNat_prod {N : ℕ} (hN : 0 < N) :
    (kerNat (fun n ↦ const _ (μ (n + 1))) 0 N) =
      Kernel.const _ (Measure.pi (fun i : Ioc 0 N ↦ μ i)) := by
  ext1 x₀
  refine Nat.le_induction ?_ (fun n hn hind ↦ ?_) N (Nat.succ_le.2 hN)
  · rw [kerNat_succ_self, Kernel.const_apply]
    refine (Measure.pi_eq (fun s ms ↦ ?_)).symm
    have : Subsingleton (Ioc 0 1) := by
      constructor
      rintro ⟨i, hi⟩ ⟨j, hj⟩
      rw [mem_Ioc_succ] at hi hj
      simp [hi, hj]
    rw [Fintype.prod_subsingleton _ ⟨1, right_mem_Ioc.2 zero_lt_one⟩,
      map_apply' _ (e 0).measurable, Kernel.const_apply]
    · congr with x
      simp only [Nat.reduceAdd, e, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, Nat.succ_eq_add_one,
        Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Subtype.forall,
        Nat.Ioc_succ_singleton, zero_add, mem_singleton, Nat.zero_eq]
      refine ⟨fun h ↦ h 1 rfl, fun h i hi ↦ ?_⟩
      cases hi; exact h
    · exact MeasurableSet.univ_pi ms
  · rw [Kernel.const_apply]
    refine (Measure.pi_eq fun s ms ↦ ?_).symm
    rw [kerNat_succ_right _ _ _ (Nat.succ_le.1 hn), kerNat_succ_self, compProdNat,
      dif_pos ⟨Nat.succ_le.1 hn, n.lt_succ_self⟩,
      map_apply' _ _ _ (MeasurableSet.univ_pi ms), er_succ_preimage_pi (Nat.succ_le.1 hn),
      split, Kernel.map_const, Kernel.comap_const, Kernel.compProd_apply_prod, ← prod_Ioc,
      ← Measure.pi_pi, ← setLIntegral_const, hind, Kernel.const_apply]
    · congr with x
      rw [Kernel.const_apply, Measure.map_apply (e n).measurable]
      · congr
      · exact (e n).measurable_invFun (ms _)
    · exact MeasurableSet.univ_pi (fun _ ↦ ms _)
    · exact (e n).measurable_invFun (ms _)
    · exact (e n).measurable
    · exact (er ..).measurable

theorem prod_noyau_proj (N : ℕ) :
    partialKernel (fun n ↦ const ((i : Iic n) → X i) (μ (n + 1))) 0 N =
      Kernel.map ((deterministic id measurable_id) ×ₖ
          (const _ (Measure.pi (fun i : Ioc 0 N ↦ μ i))))
        (el 0 N (zero_le N)) := by
  rcases eq_zero_or_pos N with rfl | hN
  · have : IsEmpty (Ioc 0 0) := by simp
    rw [partialKernel, dif_neg (lt_irrefl 0), Measure.pi_of_empty]
    ext x s ms
    rw [Kernel.map_apply _ (el ..).measurable, deterministic_apply, Kernel.prod_apply,
      deterministic_apply, Kernel.const_apply, Measure.dirac_prod_dirac,
      Measure.map_apply (el 0 0 (_root_.le_refl 0)).measurable ms,
      Measure.dirac_apply' _ ((el 0 0 (_root_.le_refl 0)).measurable ms),
      Measure.dirac_apply' _ ms]
    apply indicator_const_eq
    simp only [id_eq, el, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, mem_preimage]
    congrm (fun i ↦ ?_) ∈ s
    simp [(mem_Iic_zero i.2).symm]
  · rw [partialKernel, dif_pos hN, kerNat_prod _ hN]

theorem el_preimage {n : ℕ} (s : (i : Iic n) → Set (X i)) :
    (el 0 n (zero_le n)) ⁻¹' (Set.univ.pi s) =
      (Set.univ.pi fun i : Iic 0 ↦ s ⟨i.1, Iic_subset_Iic.2 (zero_le n) i.2⟩) ×ˢ
      (Set.univ.pi fun i : Ioc 0 n ↦ s ⟨i.1, Ioc_subset_Iic_self i.2⟩) := by
  ext p
  simp only [el, nonpos_iff_eq_zero, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, Set.mem_preimage,
    Set.mem_pi, Set.mem_univ, true_implies, Subtype.forall, mem_Iic, Set.mem_prod, mem_Ioc]
  constructor
  · intro h
    constructor
    · rintro - rfl
      exact h 0 (zero_le n)
    · rintro a ⟨h1, h2⟩
      convert h a h2
      rw [dif_neg h1.ne']
  · intro h a ha
    obtain rfl | ha' := eq_zero_or_pos a
    · exact h.1 0 rfl
    · rw [dif_neg ha'.ne']
      exact h.2 a ⟨ha', ha⟩

theorem Measure.map_bind {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z]
    (μ : Measure X) (κ : Kernel X Y) (f : Y → Z) (mf : Measurable f) :
    (μ.bind κ).map f = μ.bind (κ.map f) := by
  ext s ms
  rw [Measure.map_apply mf ms, Measure.bind_apply ms (Kernel.measurable _),
    Measure.bind_apply (mf ms) (Kernel.measurable _)]
  simp_rw [Kernel.map_apply' _ mf _ ms]

theorem map_bind_eq_bind_comap {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z]
    (μ : Measure X) (κ : Kernel Y Z) (f : X → Y) (mf : Measurable f) :
    (μ.map f).bind κ = μ.bind (Kernel.comap κ f mf) := by
  ext s ms
  rw [Measure.bind_apply ms (Kernel.measurable _), lintegral_map, Measure.bind_apply ms]
  · rfl
  · exact Kernel.measurable _
  · exact Kernel.measurable_coe _ ms
  · exact mf

theorem isProjectiveLimit_infinitePiNat :
    IsProjectiveLimit (infinitePiNat μ) (fun I : Finset ℕ ↦ (Measure.pi (fun i : I ↦ μ i))) := by
  have _M := ProbabilityMeasure.nonempty ⟨μ 0, hμ 0⟩
  intro I
  simp_rw [isProjectiveMeasureFamily_pi μ _ _ I.sub_Iic]
  rw [← restrict₂_comp_restrict I.sub_Iic,
    ← Measure.map_map (measurable_restrict₂ _) (measurable_restrict _), ← frestrictLe]
  congr
  rw [infinitePiNat, Measure.map_bind, ionescuTulceaKernel_proj]; swap
  · exact measurable_frestrictLe _
  refine (Measure.pi_eq fun s ms ↦ ?_).symm
  have mpis := MeasurableSet.univ_pi ms
  rw [Measure.bind_apply mpis (Kernel.measurable _),
    ← prod_congr' (Iic_union_Ioc_eq_Iic (zero_le _)), ← prod_union' (disjoint_Iic_Ioc (zero_le _)),
    mul_comm, ← Measure.pi_pi (ι := Iic 0), ← setLIntegral_const,
    ← lintegral_indicator _ (MeasurableSet.univ_pi (fun _ ↦ ms _))]
  congr with x₀
  rw [prod_noyau_proj, Kernel.map_apply', Kernel.prod_apply, el_preimage,
    Measure.prod_prod, deterministic_apply', Kernel.const_apply, indicator_one_mul_const']
  · simp
  · exact MeasurableSet.univ_pi fun _ ↦ ms _
  · exact (el ..).measurable
  · exact mpis

theorem kolContent_eq_infinitePiNat {A : Set ((n : ℕ) → X n)} (hA : A ∈ measurableCylinders X) :
    kolContent (isProjectiveMeasureFamily_pi μ) A = infinitePiNat μ A := by
  obtain ⟨s, S, mS, A_eq⟩ : ∃ s S, MeasurableSet S ∧ A = cylinder s S := by
    simpa [mem_measurableCylinders] using hA
  rw [kolContent_congr _ A A_eq mS, A_eq, cylinder, ← Measure.map_apply (measurable_restrict _) mS,
    isProjectiveLimit_infinitePiNat μ]

end Nat

section ProductMeasure

variable {ι : Type*}
variable {X : ι → Type*} [hX : ∀ i, MeasurableSpace (X i)]
variable (μ : (i : ι) → Measure (X i)) [hμ : ∀ i, IsProbabilityMeasure (μ i)]

lemma cast_pi_eval {X : ι → Type*} (s : Set ι) (x : (i : s) → X i) (i j : s) (h : i = j)
    (h' : X i = X j) :
    cast h' (x i) = x j := by
  subst h
  rfl

lemma cast_mem_cast (α β : Type u) (h : α = β) (a : α) (s : Set α) (h' : Set α = Set β) :
    (cast h a ∈ cast h' s) = (a ∈ s) := by
  subst h
  rfl

lemma HEq_meas {i j : ι} (hij : i = j) :
    HEq (inferInstance : MeasurableSpace (X i)) (inferInstance : MeasurableSpace (X j)) := by
  cases hij; rfl

/-- This theorem is used to prove the existence of the product measure: the `kolContent` of
a decresaing sequence of cylinders with empty intersection converges to `0`, in the case where
the measurable spaces are indexed by a countable type. This implies the σ-additivity of
`kolContent` (see `sigma_additive_addContent_of_tendsto_zero`),
which allows to extend it to the σ-algebra by Carathéodory's theorem. -/
theorem secondLemma
    (φ : ℕ ≃ ι) {A : ℕ → Set ((i : ι) → X i)} (A_mem : ∀ n, A n ∈ measurableCylinders X)
    (A_anti : Antitone A) (A_inter : ⋂ n, A n = ∅) :
    Tendsto (fun n ↦ kolContent (isProjectiveMeasureFamily_pi μ) (A n)) atTop (𝓝 0) := by
  set μ_proj := isProjectiveMeasureFamily_pi μ
  let μ_fproj := isProjectiveMeasureFamily_pi (fun k : ℕ ↦ μ (φ k))
  have A_cyl n : ∃ s S, MeasurableSet S ∧ A n = cylinder s S := by
    simpa [mem_measurableCylinders] using A_mem n
  choose s S mS A_eq using A_cyl
  -- The goal of the proof is to apply the same result when the index set is `ℕ`. To do so we
  -- have to pull back the sets `sₙ` and `Sₙ` using equivalences.
  let t n := (s n).preimage φ φ.injective.injOn
  have h i : X (φ (φ.symm i)) = X i := congrArg X (φ.apply_symm_apply i)
  have e n i (h : i ∈ s n) : φ.symm i ∈ t n := by simpa [t] using h
  have e' n k (h : k ∈ t n) : φ k ∈ s n := by simpa [t] using h
  -- The function `f` does the link between families indexed by `ℕ` and those indexed by `ι`.
  -- Here we have to use `cast` because otherwhise we land in `X (φ (φ.symm i))`, which is not
  -- definitionally equal to X i.
  have meas_cast i : Measurable (cast (h i)) := by
    apply measurable_cast
    exact HEq_meas (by simp)
  let f : ((k : ℕ) → X (φ k)) → (i : ι) → X i := fun x i ↦ cast (h i) (x (φ.symm i))
  -- `aux n` is an equivalence between `sₙ` ans `tₙ`, it will be used to link the two.
  let aux n : s n ≃ t n :=
    { toFun := fun i ↦ ⟨φ.symm i, e n i.1 i.2⟩
      invFun := fun k ↦ ⟨φ k, e' n k.1 k.2⟩
      left_inv := fun _ ↦ by simp
      right_inv := fun _ ↦ by simp }
  -- `gₙ` is the equivalent of `f` for families indexed by `tₙ` and `sₙ`.
  let g n : ((k : t n) → X (φ k)) → (i : s n) → X i :=
    fun x i ↦ cast (h i) (x (aux n i))
  -- Now fe define `Bₙ` and `Tₙ` as follows. `Bₙ` is a cylinder.
  let B n := f ⁻¹' (A n)
  let T n := (g n) ⁻¹' (S n)
  have B_eq n : B n = cylinder (t n) (T n) := by
    simp_rw [B, A_eq]
    rfl
  -- `gₙ` is measurable. We have to play with `Heq` to prove measurability of `cast`.
  have mg n : Measurable (g n) :=
    measurable_pi_lambda _ (fun i ↦ (meas_cast _).comp <| measurable_pi_apply _)
  -- We deduce that `Tₙ` is measurable.
  have mT n : MeasurableSet (T n) := (mS n).preimage (mg n)
  -- The sequence `(Bₙ)` satisfies the hypotheses of `firstLemma`, we now have to prove that we can
  -- rewrite the goal in terms of `B`.
  have B_anti : Antitone B := fun m n hmn ↦ Set.preimage_mono <| A_anti hmn
  have B_inter : ⋂ n, B n = ∅ := by
    simp_rw [B, ← Set.preimage_iInter, A_inter, Set.preimage_empty]
  have B_mem n : B n ∈ measurableCylinders (fun k ↦ X (φ k)) :=
    (mem_measurableCylinders (B n)).2 ⟨t n, T n, mT n, B_eq n⟩
  -- Taking the preimage of a product indexed by `sₙ` by `gₙ` yields a product indexed by `uₙ`,
  -- again we have to play with `cast`.
  have imp n (u : (i : s n) → Set (X i)) : (g n) ⁻¹' (Set.univ.pi u) =
      Set.univ.pi (fun k : t n ↦ u ((aux n).symm k)) := by
    ext x
    simp only [Equiv.coe_fn_mk, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
      Subtype.forall, Equiv.coe_fn_symm_mk, g, aux]
    refine ⟨fun h' k hk ↦ ?_, fun h' i hi ↦ ?_⟩
    · convert h' (φ k) (e' n k hk)
      rw [@cast_pi_eval ℕ (fun k ↦ X (φ k)) (t n) x ⟨φ.symm (φ k), by simp [hk]⟩ ⟨k, hk⟩]
      simp
    · convert h' (φ.symm i) (e n i hi)
      rw [← @cast_pi_eval ι (fun i ↦ Set (X i)) (s n) u ⟨φ (φ.symm i), by simp [hi]⟩
          ⟨i, hi⟩ (by simp) _,
        cast_mem_cast (X (φ (φ.symm i))) (X i) (by simp) (x ⟨φ.symm i, e n i hi⟩)
          (u ⟨φ (φ.symm i), by simp [hi]⟩) (by simp)]
  -- The pushforward measure of the product measure of `(μ_{φ k})_{k ∈ tₙ}` by `gₙ` is the
  -- product measre of `(∨ᵢ)_{i ∈ sₙ}`.
  have test' n : Measure.pi (fun i : s n ↦ μ i) =
      (Measure.pi (fun k : t n ↦ μ (φ k))).map (g n) := by
    refine Measure.pi_eq (fun x mx ↦ ?_)
    rw [Measure.map_apply (mg n), imp n, Measure.pi_pi,
      Fintype.prod_equiv (aux n).symm _ (fun i ↦ (μ i) (x i))]
    · simp [aux]
    · exact MeasurableSet.pi Set.countable_univ (by simp [mx])
  -- This yields the desired result: the `kolContent` of `Aₙ` is the same as the one of `Bₙ`.
  have crucial n : kolContent μ_proj (A n) = kolContent μ_fproj (B n) := by
    simp_rw [fun n ↦ kolContent_congr μ_proj _ (A_eq n) (mS n),
      fun n ↦ kolContent_congr μ_fproj _ (B_eq n) (mT n), T, test' n]
    rw [Measure.map_apply (mg n) (mS n)]
  simp_rw [crucial, fun n ↦ kolContent_eq_infinitePiNat (fun k ↦ μ (φ k)) (B_mem n),
    ← measure_empty (μ := Measure.infinitePiNat (fun k ↦ μ (φ k))), ← B_inter]
  exact tendsto_measure_iInter
    (fun n ↦ (MeasurableSet.of_mem_measurableCylinders (B_mem n)).nullMeasurableSet)
    B_anti ⟨0, measure_ne_top _ _⟩

/-- The `kolContent` of `cylinder I S` can be computed by integrating the indicator of
`cylinder I S` over the variables indexed by `I`. -/
theorem kolContent_eq_lmarginal [DecidableEq ι]
    (I : Finset ι) {S : Set ((i : I) → X i)} (mS : MeasurableSet S) (x : (i : ι) → X i) :
    kolContent (isProjectiveMeasureFamily_pi μ) (cylinder I S) =
    (∫⋯∫⁻_I, (cylinder I S).indicator 1 ∂μ) x := by
  rw [kolContent_cylinder _ mS, ← lintegral_indicator_one mS]
  refine lintegral_congr <| fun x ↦ ?_
  by_cases hx : x ∈ S <;> simp [hx, Function.updateFinset, restrict_def]

theorem thirdLemma (A : ℕ → Set ((i : ι) → X i)) (A_mem : ∀ n, A n ∈ measurableCylinders X)
    (A_anti : Antitone A) (A_inter : ⋂ n, A n = ∅) :
    Tendsto (fun n ↦ kolContent (isProjectiveMeasureFamily_pi μ) (A n)) atTop (𝓝 0) := by
  have : ∀ i, Nonempty (X i) := by
    have := fun i ↦ ProbabilityMeasure.nonempty ⟨μ i, hμ i⟩
    infer_instance
  set μ_proj := isProjectiveMeasureFamily_pi μ
  have A_cyl n : ∃ s S, MeasurableSet S ∧ A n = cylinder s S :=
    (mem_measurableCylinders _).1 (A_mem n)
  choose s S mS A_eq using A_cyl
  -- The family `(Aₙ)` only depends on a countable set of coordinates, called `u`. Therefore our
  -- goal is to see it as a family indexed by this countable set,
  -- so that we can apply `secondLemma`. The proof is very similar to the previous one, except
  -- that the use of coercions avoids manipulating `cast`, as equalities will hold by `rfl`.
  let u := ⋃ n, (s n).toSet
  let μ_fproj := isProjectiveMeasureFamily_pi (fun i : u ↦ μ i)
  -- `tₙ` will be `sₙ` seen as a subset of `u`.
  let t n : Finset u := (s n).preimage Subtype.val Subtype.val_injective.injOn
  -- These are a few lemmas to move between `sₙ` and `tₙ`.
  have su n : (s n).toSet ⊆ u := Set.subset_iUnion (fun n ↦ (s n).toSet) n
  have st n i (hi : i ∈ s n) : ⟨i, su n hi⟩ ∈ t n := by simpa [t] using hi
  have ts n i (hi : i ∈ t n) : i.1 ∈ s n := by simpa [t] using hi
  classical
  let f : ((i : u) → X i) → (i : ι) → X i :=
    fun x i ↦ if hi : i ∈ u then x ⟨i, hi⟩ else Classical.ofNonempty
  -- This brings again `aux`.
  let aux : (n : ℕ) → (s n ≃ t n) := fun n ↦
    { toFun := fun i ↦ ⟨⟨i.1, su n i.2⟩, st n i i.2⟩
      invFun := fun i ↦ ⟨i.1.1, ts n i i.2⟩
      left_inv := fun i ↦ by simp
      right_inv := fun i ↦ by simp }
  let g n : ((i : t n) → X i) → (i : s n) → X i := fun x i ↦ x (aux n i)
  have test n : (s n).restrict ∘ f = (g n) ∘ (fun (x : (i : u) → X i) i ↦ x i) := by
    ext x i
    simp [f, g, aux, su n i.2, restrict_def]
  let B n := f ⁻¹' (A n)
  let T n := (g n) ⁻¹' (S n)
  have B_eq n : B n = cylinder (t n) (T n) := by
    simp_rw [B, A_eq, cylinder, ← Set.preimage_comp, test]
    rfl
  have mg n : Measurable (g n) := measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
  have mT n : MeasurableSet (T n) := mg n (mS n)
  have B_anti : Antitone B := fun m n hmn ↦ Set.preimage_mono <| A_anti hmn
  have B_inter : ⋂ n, B n = ∅ := by
    simp_rw [B, ← Set.preimage_iInter, A_inter, Set.preimage_empty]
  have B_mem n : B n ∈ measurableCylinders (fun i : u ↦ X i) :=
    (mem_measurableCylinders (B n)).2 ⟨t n, T n, mT n, B_eq n⟩
  have imp n (a : (i : s n) → Set (X i)) : (g n) ⁻¹' (Set.univ.pi a) =
      Set.univ.pi (fun i : t n ↦ a ((aux n).symm i)) := by
    ext x
    simp only [Equiv.coe_fn_mk, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
      Equiv.coe_fn_symm_mk, g]
    exact ⟨fun h i ↦ h ((aux n).symm i), fun h i ↦ h (aux n i)⟩
  -- The pushforward measure of the product measure of `(μ_{φ k})_{k ∈ tₙ}` by `gₙ` is the
  -- product measre of `(∨ᵢ)_{i ∈ sₙ}`.
  have test' n : Measure.pi (fun i : s n ↦ μ i) =
      (Measure.pi (fun i : t n ↦ μ i)).map (g n) := by
    refine Measure.pi_eq (fun x mx ↦ ?_)
    rw [Measure.map_apply (mg n), imp n, Measure.pi_pi,
      Fintype.prod_equiv (aux n).symm _ (fun i ↦ (μ i) (x i))]
    · simp [aux]
    · exact MeasurableSet.pi Set.countable_univ (by simp [mx])
  -- This yields the desired result: the `kolContent` of `Aₙ` is the same as the one of `Bₙ`.
  have crucial n : kolContent μ_proj (A n) = kolContent μ_fproj (B n) := by
    simp_rw [fun n ↦ kolContent_congr μ_proj _ (A_eq n) (mS n),
      fun n ↦ kolContent_congr μ_fproj _ (B_eq n) (mT n), T, test' n]
    rw [Measure.map_apply (mg n) (mS n)]
  -- We now have two cases: if `u` is finite, then the result is simple because
  -- we have an actual measure.
  rcases finite_or_infinite u with (u_fin | u_inf)
  · have := Fintype.ofFinite u
    simp_rw [crucial,
      fun n ↦ kolContent_eq_measure_pi (fun i : u ↦ μ i)
        (MeasurableSet.of_mem_measurableCylinders (B_mem n)),
      ← measure_empty (μ := Measure.pi (fun i : u ↦ μ i)), ← B_inter]
    exact tendsto_measure_iInter
      (fun n ↦ (MeasurableSet.of_mem_measurableCylinders (B_mem n)).nullMeasurableSet)
      B_anti ⟨0, measure_ne_top _ _⟩
  · -- If `u` is infinite, then we have an equivalence with `ℕ` so we can apply `secondLemma`.
    have count_u : Countable u := Set.countable_iUnion (fun n ↦ (s n).countable_toSet)
    obtain ⟨φ, -⟩ := Classical.exists_true_of_nonempty (α := ℕ ≃ u) nonempty_equiv_of_countable
    simp_rw [crucial]
    exact secondLemma (fun i : u ↦ μ i) φ B_mem B_anti B_inter

/-- The `kolContent` associated to a family of probability measures is σ-subadditive. -/
theorem kolContent_pi_sigma_subadditive ⦃f : ℕ → Set ((i : ι) → X i)⦄
    (hf : ∀ n, f n ∈ measurableCylinders X)
    (hf_Union : (⋃ n, f n) ∈ measurableCylinders X) :
    kolContent (isProjectiveMeasureFamily_pi μ) (⋃ n, f n) ≤
    ∑' n, kolContent (isProjectiveMeasureFamily_pi μ) (f n) := by
  classical
  have : ∀ i, Nonempty (X i) := by
    have := fun i ↦ ProbabilityMeasure.nonempty ⟨μ i, hμ i⟩;
    infer_instance
  refine addContent_iUnion_le_of_addContent_iUnion_eq_tsum
    isSetRing_measurableCylinders (fun f hf hf_Union hf' ↦ ?_) f hf hf_Union
  refine sigma_additive_addContent_of_tendsto_zero isSetRing_measurableCylinders
    (kolContent (isProjectiveMeasureFamily_pi μ)) (fun s hs ↦ ?_) ?_ hf hf_Union hf'
  · rcases (mem_measurableCylinders _).1 hs with ⟨I, S, mS, s_eq⟩
    rw [s_eq, kolContent_eq_lmarginal μ (mS := mS) (x := Classical.ofNonempty)]
    refine ne_of_lt (lt_of_le_of_lt ?_ (by norm_num : (1 : ℝ≥0∞) < ⊤))
    rw [← lmarginal_const (μ := μ) (s := I) 1 Classical.ofNonempty]
    apply lmarginal_mono
    intro x
    apply Set.indicator_le
    simp
  · intro s hs anti_s inter_s
    exact thirdLemma μ s hs anti_s inter_s

/-- The product measure of an arbitrary family of probability measures. It is defined as the unique
extension of the function which gives to cylinders the measure given by the associated product
measure. -/
noncomputable def productMeasure : Measure ((i : ι) → X i) := by
  exact Measure.ofAddContent isSetSemiring_measurableCylinders generateFrom_measurableCylinders
    (kolContent (isProjectiveMeasureFamily_pi μ))
    (kolContent_pi_sigma_subadditive μ)

/-- The product measure is the projective limit of the partial product measures. This ensures
uniqueness and expresses the value of the product measures applied to cylinders. -/
theorem isProjectiveLimit_productMeasure :
    IsProjectiveLimit (productMeasure μ) (fun I : Finset ι ↦ (Measure.pi (fun i : I ↦ μ i))) := by
  intro I
  ext1 s hs
  rw [Measure.map_apply _ hs]
  swap; · apply measurable_restrict
  have h_mem : I.restrict ⁻¹' s ∈ measurableCylinders X := by
    rw [mem_measurableCylinders]; exact ⟨I, s, hs, rfl⟩
  conv_lhs => change (productMeasure μ) (I.restrict ⁻¹' s)
  rw [productMeasure, Measure.ofAddContent_eq _ _ _ _ h_mem,
    kolContent_congr _ (I.restrict ⁻¹' s) rfl hs]

instance : IsProbabilityMeasure (productMeasure μ) := by
  constructor
  rw [← cylinder_univ ∅, cylinder, ← Measure.map_apply, isProjectiveLimit_productMeasure μ]
  · simp
  · exact measurable_restrict _
  · exact MeasurableSet.univ

theorem productMeasure_boxes {s : Finset ι} {t : (i : ι) → Set (X i)}
    (mt : ∀ i ∈ s, MeasurableSet (t i)) :
    productMeasure μ (Set.pi s t) = ∏ i ∈ s, (μ i) (t i) := by
  have : Set.pi s t = cylinder s ((@Set.univ s).pi (fun i : s ↦ t i)) := by
    ext x
    simp
  rw [this, cylinder, ← Measure.map_apply, isProjectiveLimit_productMeasure μ,
    Measure.pi_pi]
  · rw [Finset.univ_eq_attach, Finset.prod_attach _ (fun i ↦ (μ i) (t i))]
  · exact measurable_restrict _
  · exact MeasurableSet.pi Set.countable_univ fun i _ ↦ mt i.1 i.2

theorem productMeasure_cylinder {s : Finset ι} {S : Set ((i : s) → X i)} (mS : MeasurableSet S) :
    productMeasure μ (cylinder s S) = Measure.pi (fun i : s ↦ μ i) S := by
  rw [cylinder, ← Measure.map_apply (measurable_restrict _) mS, isProjectiveLimit_productMeasure μ]

theorem integral_dep_productMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Finset ι} {f : ((i : s) → X i) → E} (hf : StronglyMeasurable f) :
    ∫ y, f (s.restrict y) ∂productMeasure μ =
    ∫ y, f y ∂Measure.pi (fun i : s ↦ μ i) := by

  rw [← integral_map (measurable_restrict _).aemeasurable hf.aestronglyMeasurable,
    isProjectiveLimit_productMeasure μ]

/-- The canonical filtration on dependent functions indexed by ι, where `𝓕 s` consists of
measurable sets depending only on coordinates is `s`. -/
def ℱ : @Filtration ((i : ι) → X i) (Finset ι) _ inferInstance where
  seq s := (inferInstance : MeasurableSpace ((i : s) → X i)).comap s.restrict
  mono' s t hst := by
    simp only
    rw [← restrict₂_comp_restrict hst, ← comap_comp]
    exact MeasurableSpace.comap_mono (measurable_restrict₂ _).comap_le
  le' s := (measurable_restrict s).comap_le

/-- If a function is strongly measurable with respect to the σ-algebra generated by
the finite set of coordinates `s`, then it only depends on those coordinates. -/
theorem stronglyMeasurable_dependsOn' {E : Type*} [NormedAddCommGroup E]
    {s : Finset ι} {f : ((i : ι) → X i) → E}
    (mf : @StronglyMeasurable _ _ _ (ℱ s) f) : DependsOn f s := by
  intro x y hxy
  apply eq_of_stronglyMeasurable_comap s.restrict mf
  exact dependsOn_restrict s hxy

theorem integral_stronglyMeasurable [DecidableEq ι] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {s : Finset ι} {f : ((i : ι) → X i) → E}
    (mf : @StronglyMeasurable _ _ _ (ℱ s) f) (x : (i : ι) → X i) :
    ∫ y, f y ∂productMeasure μ =
    ∫ y, f (Function.updateFinset x s y) ∂Measure.pi (fun i : s ↦ μ i) := by
  let g : ((i : s) → X i) → E := fun y ↦ f (Function.updateFinset x _ y)
  have this y : g (s.restrict y) = f y := by
    apply stronglyMeasurable_dependsOn' mf
    intro i hi
    simp only [updateFinset, restrict, dite_eq_ite, ite_eq_then]
    exact fun h ↦ (h hi).elim
  rw [← integral_congr_ae <| Eventually.of_forall this, integral_dep_productMeasure]
  exact mf.comp_measurable (measurable_updateFinset.mono (_root_.le_refl _) (ℱ.le s))

theorem lintegral_dep {s : Finset ι} {f : ((i : s) → X i) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f (s.restrict y) ∂productMeasure μ =
    ∫⁻ y, f y∂Measure.pi (fun i : s ↦ μ i) := by
  rw [← lintegral_map hf (measurable_restrict _), isProjectiveLimit_productMeasure μ]

/-- If a function is measurable with respect to the σ-algebra generated by
the finite set of coordinates `s`, then it only depends on those coordinates. -/
theorem measurable_dependsOn' {s : Finset ι} {f : ((i : ι) → X i) → ℝ≥0∞}
    (mf : @Measurable _ _ (ℱ s) _ f) : DependsOn f s := by
  intro x y hxy
  apply eq_of_measurable_comap s.restrict mf
  exact dependsOn_restrict s hxy

theorem lintegral_measurable [DecidableEq ι] {s : Finset ι}
    {f : ((i : ι) → X i) → ℝ≥0∞} (mf : @Measurable _ _ (ℱ s) _ f)
    (x : (i : ι) → X i) : ∫⁻ y, f y ∂productMeasure μ = (∫⋯∫⁻_s, f ∂μ) x := by
  let g : ((i : s) → X i) → ℝ≥0∞ := fun y ↦ f (Function.updateFinset x _ y)
  have this y : g (s.restrict y) = f y := by
    refine measurable_dependsOn' mf fun i hi ↦ ?_
    simp only [updateFinset, restrict, dite_eq_ite, ite_eq_then]
    exact fun h ↦ (h hi).elim
  simp_rw [← this]
  rw [lintegral_dep]
  · rfl
  · exact mf.comp (measurable_updateFinset.mono (_root_.le_refl _) (ℱ.le s))

end ProductMeasure
