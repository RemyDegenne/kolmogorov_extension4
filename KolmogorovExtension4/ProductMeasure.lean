/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import KolmogorovExtension4.IonescuTulceaKernel
import Mathlib.Probability.Kernel.Composition.MeasureComp

open MeasureTheory ProbabilityTheory Finset Filter Topology Kernel Preorder MeasurableEquiv

open scoped ENNReal

namespace MeasureTheory

section Preliminaries

variable {ι : Type*}

theorem _root_.preimage_restrict₂ {α : ι → Type*} {I J : Finset ι} [∀ i : ι, Decidable (i ∈ I)]
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
lemma isProjectiveMeasureFamily_pi :
    IsProjectiveMeasureFamily (fun I : Finset ι ↦ (Measure.pi (fun i : I ↦ μ i))) := by
  refine fun I J hJI ↦ Measure.pi_eq (fun s ms ↦ ?_)
  classical
  rw [Measure.map_apply (measurable_restrict₂ hJI) (MeasurableSet.univ_pi ms),
    preimage_restrict₂ hJI, Measure.pi_pi]
  let g := fun i ↦ (μ i) (if hi : i ∈ J then s ⟨i, hi⟩ else Set.univ)
  conv_lhs => change ∏ i : I, g i
  have h2 : univ.prod (fun i : J ↦ (μ i) (s i)) = univ.prod (fun i : J ↦ g i) :=
    Finset.prod_congr rfl (by simp [g])
  rw [h2, prod_coe_sort, prod_coe_sort, prod_subset hJI (fun _ h h' ↦ by simp [g, h, h'])]

theorem kolContent_eq_measure_pi [Fintype ι] {s : Set (Π i, X i)} (hs : MeasurableSet s) :
    kolContent (isProjectiveMeasureFamily_pi μ) s = Measure.pi μ s := by
  let aux : (Π i : univ, X i) → (Π i, X i) := fun x i ↦ x ⟨i, mem_univ i⟩
  have maux : Measurable aux := measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
  have pi_eq : Measure.pi μ = (Measure.pi (fun i : univ ↦ μ i)).map aux := by
    refine Measure.pi_eq fun a ma ↦ ?_
    rw [Measure.map_apply maux (MeasurableSet.univ_pi ma)]
    have : aux ⁻¹' Set.univ.pi a = Set.univ.pi (fun i : @univ ι _ ↦ a i) := by ext x; simp [aux]
    rw [this, Measure.pi_pi]
    simp
  have : s = cylinder univ (aux ⁻¹' s) := by ext x; simp [aux]
  nth_rw 1 [this]
  rw [kolContent_cylinder _ (maux hs), pi_eq, Measure.map_apply maux hs]

end Preliminaries

section Nat

/-! ### Product of measures indexed by `ℕ` -/

variable {X : ℕ → Type*}

lemma _root_.IocProdIoc_preim {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    (s : (i : Ioc a c) → Set (X i)) :
    IocProdIoc a b c ⁻¹' (Set.univ.pi s) =
      (Set.univ.pi <| restrict₂ (π := (fun n ↦ Set (X n))) (Ioc_subset_Ioc_right hbc) s) ×ˢ
        (Set.univ.pi <| restrict₂ (π := (fun n ↦ Set (X n))) (Ioc_subset_Ioc_left hab) s) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, IocProdIoc, forall_const, Subtype.forall,
    mem_Ioc, Set.mem_prod, restrict₂]
  refine ⟨fun h ↦ ⟨fun i ⟨hi1, hi2⟩ ↦ ?_, fun i ⟨hi1, hi2⟩ ↦ ?_⟩, fun ⟨h1, h2⟩ i ⟨hi1, hi2⟩ ↦ ?_⟩
  · convert h i ⟨hi1, hi2.trans hbc⟩
    rw [dif_pos hi2]
  · convert h i ⟨lt_of_le_of_lt hab hi1, hi2⟩
    rw [dif_neg (not_le.2 hi1)]
  · split_ifs with hi3
    · exact h1 i ⟨hi1, hi3⟩
    · exact h2 i ⟨not_le.1 hi3, hi2⟩

lemma _root_.IicProdIoc_preim {a b : ℕ} (hab : a ≤ b) (s : (i : Iic b) → Set (X i)) :
    IicProdIoc a b ⁻¹' (Set.univ.pi s) =
      (Set.univ.pi <| frestrictLe₂ (π := (fun n ↦ Set (X n))) hab s) ×ˢ
        (Set.univ.pi <| restrict₂ (π := (fun n ↦ Set (X n))) Ioc_subset_Iic_self s) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, IicProdIoc, forall_const, Subtype.forall,
    mem_Iic, Set.mem_prod, frestrictLe₂_apply, restrict₂, mem_Ioc]
  refine ⟨fun h ↦ ⟨fun i hi ↦ ?_, fun i ⟨hi1, hi2⟩ ↦ ?_⟩, fun ⟨h1, h2⟩ i hi ↦ ?_⟩
  · convert h i (hi.trans hab)
    rw [dif_pos hi]
  · convert h i hi2
    rw [dif_neg (not_le.2 hi1)]
  · split_ifs with hi3
    · exact h1 i hi3
    · exact h2 i ⟨not_le.1 hi3, hi⟩

variable [∀ n, MeasurableSpace (X n)]
  (μ : (n : ℕ) → Measure (X n)) [hμ : ∀ n, IsProbabilityMeasure (μ n)]

/-- Infinite product measure indexed by `ℕ`. This is an auxiliary construction, you should use
the generic product measure `Measure.productMeasure`. -/
noncomputable def Measure.infinitePiNat : Measure ((n : ℕ) → X n) :=
  (traj (fun n ↦ const _ (μ (n + 1))) 0) ∘ₘ (Measure.pi (fun i : Iic 0 ↦ μ i))

instance : IsProbabilityMeasure (Measure.infinitePiNat μ) := by
  rw [Measure.infinitePiNat]; infer_instance

lemma Measure.pi_prod_map_IocProdIoc {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    ((Measure.pi (fun i : Ioc a b ↦ μ i)).prod (Measure.pi (fun i : Ioc b c ↦ μ i))).map
      (IocProdIoc a b c) = Measure.pi (fun i : Ioc a c ↦ μ i) := by
  refine (Measure.pi_eq fun s ms ↦ ?_).symm
  rw [Measure.map_apply, IocProdIoc_preim hab hbc, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi,
    ← prod_Ioc hab hbc]
  · rfl
  · fun_prop
  · exact MeasurableSet.univ_pi ms

lemma Measure.pi_prod_map_IicProdIoc {a b : ℕ} :
    ((Measure.pi (fun i : Iic a ↦ μ i)).prod (Measure.pi (fun i : Ioc a b ↦ μ i))).map
      (IicProdIoc a b) = Measure.pi (fun i : Iic b ↦ μ i) := by
  obtain hab | hba := le_total a b
  · refine (Measure.pi_eq fun s ms ↦ ?_).symm
    rw [Measure.map_apply, IicProdIoc_preim hab, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi,
      ← prod_Iic hab (f := fun i ↦ μ i (s i))]
    · rfl
    · fun_prop
    · exact MeasurableSet.univ_pi ms
  · rw [IicProdIoc_le hba, ← Measure.map_map, ← Measure.fst, Measure.fst_prod]
    exact isProjectiveMeasureFamily_pi μ (Iic a) (Iic b) (Iic_subset_Iic.2 hba) |>.symm
    all_goals fun_prop

lemma Measure.map_piSingleton (μ : (n : ℕ) → Measure (X n)) [∀ n, SigmaFinite (μ n)] (n : ℕ) :
    (μ (n + 1)).map (piSingleton n) = Measure.pi (fun i : Ioc n (n + 1) ↦ μ i) := by
  refine (Measure.pi_eq fun s hs ↦ ?_).symm
  have : Subsingleton (Ioc n (n + 1)) := by
    rw [Nat.Ioc_succ_singleton]
    infer_instance
  rw [Fintype.prod_subsingleton _ ⟨n + 1, mem_Ioc_succ.2 rfl⟩, Measure.map_apply]
  · congr with x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const, Subtype.forall,
      Nat.Ioc_succ_singleton, mem_singleton]
    exact ⟨fun h ↦ h (n + 1) rfl, fun h a b ↦ b.symm ▸ h⟩
  · exact (piSingleton n).measurable
  · exact MeasurableSet.univ_pi hs

theorem ptraj_const' {a b : ℕ} :
    (ptraj (fun n ↦ const _ (μ (n + 1))) a b).map (restrict₂ (Ioc_subset_Iic_self (a := a))) =
    const _ (Measure.pi (fun i : Ioc a b ↦ μ i)) := by
  obtain hab | hba := lt_or_le a b
  · refine Nat.le_induction ?_ (fun n hn hind ↦ ?_) b (Nat.succ_le.2 hab) <;> ext1 x₀
    · rw [ptraj_succ_self, Kernel.map_map, map_apply, prod_apply, map_apply, const_apply,
        const_apply, Measure.map_piSingleton, restrict₂_comp_IicProdIoc, Measure.map_snd_prod,
        measure_univ, one_smul]
      all_goals fun_prop
    · have : (restrict₂ (Ioc_subset_Iic_self (a := a))) ∘ (IicProdIoc (X := X) n (n + 1)) =
          (IocProdIoc a n (n + 1)) ∘ (Prod.map (restrict₂ Ioc_subset_Iic_self) id) := rfl
      rw [const_apply, ptraj_succ_of_le (by omega), map_const, prod_const_comp, id_comp,
        Kernel.map_map, this, ← Kernel.map_map, Kernel.map_prod, hind,  Kernel.map_id, map_apply,
        prod_apply, const_apply, const_apply, Measure.map_piSingleton,
        Measure.pi_prod_map_IocProdIoc]
      any_goals fun_prop
      all_goals omega
  · have : IsEmpty (Ioc a b) := by simpa [hba] using Subtype.isEmpty_false
    ext x s ms
    by_cases hs : s.Nonempty
    · rw [Subsingleton.eq_univ_of_nonempty hs, @measure_univ .., measure_univ]
      exact (IsMarkovKernel.map _ (measurable_restrict₂ _)) |>.isProbabilityMeasure x
    · rw [Set.not_nonempty_iff_eq_empty.1 hs]
      simp

theorem ptraj_const {a b : ℕ} :
    ptraj (fun n ↦ const _ (μ (n + 1))) a b =
      (Kernel.id ×ₖ (const _ (Measure.pi (fun i : Ioc a b ↦ μ i)))).map (IicProdIoc a b) := by
  rw [ptraj_eq_prod, ptraj_const']

theorem isProjectiveLimit_infinitePiNat :
    IsProjectiveLimit (Measure.infinitePiNat μ)
      (fun I : Finset ℕ ↦ (Measure.pi (fun i : I ↦ μ i))) := by
  have _ := ProbabilityMeasure.nonempty ⟨μ 0, hμ 0⟩
  intro I
  simp_rw [isProjectiveMeasureFamily_pi μ _ _ I.sub_Iic]
  rw [← restrict₂_comp_restrict I.sub_Iic, ← Measure.map_map, ← frestrictLe, Measure.infinitePiNat,
    Measure.map_comp, traj_map_frestrictLe, ptraj_const, ← Measure.map_comp,
    ← Measure.compProd_eq_comp_prod, Measure.compProd_const, Measure.pi_prod_map_IicProdIoc]
  any_goals fun_prop

theorem kolContent_eq_infinitePiNat {A : Set ((n : ℕ) → X n)} (hA : A ∈ measurableCylinders X) :
    kolContent (isProjectiveMeasureFamily_pi μ) A = Measure.infinitePiNat μ A := by
  obtain ⟨s, S, mS, A_eq⟩ : ∃ s S, MeasurableSet S ∧ A = cylinder s S := by
    simpa [mem_measurableCylinders] using hA
  rw [kolContent_congr _ A A_eq mS, A_eq, cylinder, ← Measure.map_apply (measurable_restrict _) mS,
    isProjectiveLimit_infinitePiNat μ]

end Nat

section ProductMeasure

/-! ### Product of infinitely many probability measures -/

variable {ι : Type*} {X : ι → Type*}

section castLemmas

lemma cast_pi_eval (s : Set ι) (x : Π i : s, X i) (i j : s) (h : i = j) :
    cast (congrArg X (Subtype.coe_inj.2 h)) (x i) = x j := by cases h; rfl

lemma cast_mem_cast (α β : Type u) (h : α = β) (a : α) (s : Set α) :
    (cast h a ∈ cast (congrArg Set h) s) = (a ∈ s) := by cases h; rfl

variable [mX : ∀ i, MeasurableSpace (X i)]

lemma HEq_measurableSpace {i j : ι} (hij : i = j) : HEq (mX i) (mX j) := by cases hij; rfl

end castLemmas

variable [∀ i, MeasurableSpace (X i)]
  (μ : (i : ι) → Measure (X i)) [hμ : ∀ i, IsProbabilityMeasure (μ i)]

/-- This theorem is used to prove the existence of the product measure: the `kolContent` of
a decreasing sequence of cylinders with empty intersection converges to `0`, in the case where
the measurable spaces are indexed by a countable type. This implies the σ-additivity of
`kolContent` (see `sigma_additive_addContent_of_tendsto_zero`),
which allows to extend it to the σ-algebra by Carathéodory's theorem. -/
theorem secondLemma
    (φ : ℕ ≃ ι) {A : ℕ → Set (Π i, X i)} (A_mem : ∀ n, A n ∈ measurableCylinders X)
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
  have meas_cast i : Measurable (cast (h i)) := measurable_cast _ (HEq_measurableSpace (by simp))
  let f : (Π k, X (φ k)) → Π i, X i := fun x i ↦ cast (h i) (x (φ.symm i))
  -- `aux n` is an equivalence between `sₙ` ans `tₙ`, it will be used to link the two.
  let aux n : s n ≃ t n :=
    { toFun := fun i ↦ ⟨φ.symm i, e n i.1 i.2⟩
      invFun := fun k ↦ ⟨φ k, e' n k.1 k.2⟩
      left_inv := fun _ ↦ by simp
      right_inv := fun _ ↦ by simp }
  -- `gₙ` is the equivalent of `f` for families indexed by `tₙ` and `sₙ`.
  let g n : (Π k : t n, X (φ k)) → Π i : s n, X i := fun x i ↦ cast (h i) (x (aux n i))
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
  -- Taking the preimage of a product indexed by `sₙ` by `gₙ` yields a product indexed by `tₙ`,
  -- again we have to play with `cast`.
  have g_preim n (u : (i : s n) → Set (X i)) : (g n) ⁻¹' (Set.univ.pi u) =
      Set.univ.pi (fun k : t n ↦ u ((aux n).symm k)) := by
    ext x
    simp [Equiv.coe_fn_mk, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
      Subtype.forall, Equiv.coe_fn_symm_mk, g, aux]
    refine ⟨fun h' k hk ↦ ?_, fun h' i hi ↦ ?_⟩
    · convert h' (φ k) (e' n k hk)
      rw [@cast_pi_eval ℕ (fun k ↦ X (φ k)) (t n) x ⟨φ.symm (φ k), by simp [hk]⟩ ⟨k, hk⟩ (by simp)]
    · convert h' (φ.symm i) (e n i hi)
      rw [← @cast_pi_eval ι (fun i ↦ Set (X i)) (s n) u ⟨φ (φ.symm i), by simp [hi]⟩
          ⟨i, hi⟩ (by simp),
        cast_mem_cast (X (φ (φ.symm i))) (X i) (by simp) (x ⟨φ.symm i, e n i hi⟩)
          (u ⟨φ (φ.symm i), by simp [hi]⟩)]
  -- The pushforward measure of the product measure of `(μ_{φ k})_{k ∈ tₙ}` by `gₙ` is the
  -- product measre of `(μᵢ)_{i ∈ sₙ}`.
  have pi_s n : Measure.pi (fun i : s n ↦ μ i) =
      (Measure.pi (fun k : t n ↦ μ (φ k))).map (g n) := by
    refine Measure.pi_eq (fun x mx ↦ ?_)
    rw [Measure.map_apply (mg n), g_preim n, Measure.pi_pi,
      Fintype.prod_equiv (aux n).symm _ (fun i ↦ (μ i) (x i))]
    · simp [aux]
    · exact MeasurableSet.pi Set.countable_univ (by simp [mx])
  -- This yields the desired result: the `kolContent` of `Aₙ` is the same as the one of `Bₙ`.
  have kol n : kolContent μ_proj (A n) = kolContent μ_fproj (B n) := by
    rw [kolContent_congr μ_proj _ (A_eq n) (mS n), kolContent_congr μ_fproj _ (B_eq n) (mT n),
      pi_s n, Measure.map_apply (mg n) (mS n)]
  simp_rw [kol, fun n ↦ kolContent_eq_infinitePiNat (fun k ↦ μ (φ k)) (B_mem n),
    ← measure_empty (μ := Measure.infinitePiNat (fun k ↦ μ (φ k))), ← B_inter]
  exact tendsto_measure_iInter_atTop
    (fun n ↦ (MeasurableSet.of_mem_measurableCylinders (B_mem n)).nullMeasurableSet)
    B_anti ⟨0, measure_ne_top _ _⟩

theorem thirdLemma {A : ℕ → Set (Π i, X i)} (A_mem : ∀ n, A n ∈ measurableCylinders X)
    (A_anti : Antitone A) (A_inter : ⋂ n, A n = ∅) :
    Tendsto (fun n ↦ kolContent (isProjectiveMeasureFamily_pi μ) (A n)) atTop (𝓝 0) := by
  have : ∀ i, Nonempty (X i) := fun i ↦ ProbabilityMeasure.nonempty ⟨μ i, hμ i⟩
  set μ_proj := isProjectiveMeasureFamily_pi μ
  have A_cyl n : ∃ s S, MeasurableSet S ∧ A n = cylinder s S :=
    (mem_measurableCylinders _).1 (A_mem n)
  choose s S mS A_eq using A_cyl
  -- The family `(Aₙ)` only depends on a countable set of coordinates, called `u`. Therefore our
  -- goal is to see it as a family indexed by this countable set,
  -- so that we can apply `secondLemma`. The proof is very similar to the previous one, except
  -- that the use of coercions avoids manipulating `cast`, as types will be definitionally equal.
  let u := ⋃ n, (s n).toSet
  let μ_fproj := isProjectiveMeasureFamily_pi (fun i : u ↦ μ i)
  -- `tₙ` will be `sₙ` seen as a subset of `u`.
  let t n : Finset u := (s n).preimage Subtype.val Subtype.val_injective.injOn
  -- These are a few lemmas to move between `sₙ` and `tₙ`.
  have su n : (s n).toSet ⊆ u := Set.subset_iUnion (fun n ↦ (s n).toSet) n
  have st n i (hi : i ∈ s n) : ⟨i, su n hi⟩ ∈ t n := by simpa [t] using hi
  have ts n i (hi : i ∈ t n) : i.1 ∈ s n := by simpa [t] using hi
  classical
  let f : (Π i : u, X i) → Π i, X i :=
    fun x i ↦ if hi : i ∈ u then x ⟨i, hi⟩ else Classical.ofNonempty
  -- This brings again `aux`.
  let aux n : s n ≃ t n :=
    { toFun := fun i ↦ ⟨⟨i.1, su n i.2⟩, st n i i.2⟩
      invFun := fun i ↦ ⟨i.1.1, ts n i i.2⟩
      left_inv := fun i ↦ by simp
      right_inv := fun i ↦ by simp }
  let g n : (Π i : t n, X i) → Π i : s n, X i := fun x i ↦ x (aux n i)
  have test n : (s n).restrict ∘ f = (g n) ∘ (fun (x : (i : u) → X i) i ↦ x i) := by
    ext x i
    simp [f, g, aux, su n i.2]
  let B n := f ⁻¹' (A n)
  let T n := (g n) ⁻¹' (S n)
  have B_eq n : B n = cylinder (t n) (T n) := by
    simp_rw [B, A_eq, cylinder, ← Set.preimage_comp, test]
    rfl
  have mg n : Measurable (g n) := by fun_prop
  have mT n : MeasurableSet (T n) := mg n (mS n)
  have B_anti : Antitone B := fun m n hmn ↦ Set.preimage_mono <| A_anti hmn
  have B_inter : ⋂ n, B n = ∅ := by
    simp_rw [B, ← Set.preimage_iInter, A_inter, Set.preimage_empty]
  have B_mem n : B n ∈ measurableCylinders (fun i : u ↦ X i) :=
    (mem_measurableCylinders (B n)).2 ⟨t n, T n, mT n, B_eq n⟩
  have g_preim n (a : Π i : s n, Set (X i)) : (g n) ⁻¹' (Set.univ.pi a) =
      Set.univ.pi (fun i : t n ↦ a ((aux n).symm i)) := by
    ext x
    simp only [Equiv.coe_fn_mk, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
      Equiv.coe_fn_symm_mk, g]
    exact ⟨fun h i ↦ h ((aux n).symm i), fun h i ↦ h (aux n i)⟩
  -- The pushforward measure of the product measure of `(μᵢ)_{i ∈ tₙ}` by `gₙ` is the
  -- product measre of `(μᵢ)_{i ∈ sₙ}`.
  have pi_s n : Measure.pi (fun i : s n ↦ μ i) =
      (Measure.pi (fun i : t n ↦ μ i)).map (g n) := by
    refine Measure.pi_eq (fun x mx ↦ ?_)
    rw [Measure.map_apply (mg n), g_preim n, Measure.pi_pi,
      Fintype.prod_equiv (aux n).symm _ (fun i ↦ (μ i) (x i))]
    · simp [aux]
    · exact MeasurableSet.pi Set.countable_univ (by simp [mx])
  -- This yields the desired result: the `kolContent` of `Aₙ` is the same as the one of `Bₙ`.
  have kol n : kolContent μ_proj (A n) = kolContent μ_fproj (B n) := by
    rw [kolContent_congr μ_proj _ (A_eq n) (mS n), kolContent_congr μ_fproj _ (B_eq n) (mT n),
      pi_s n, Measure.map_apply (mg n) (mS n)]
  -- We now have two cases: if `u` is finite, then the result is simple because
  -- we have an actual measure.
  obtain u_fin | u_inf := finite_or_infinite u
  · have := Fintype.ofFinite u
    simp_rw [kol, fun n ↦ kolContent_eq_measure_pi (fun i : u ↦ μ i)
      (MeasurableSet.of_mem_measurableCylinders (B_mem n)),
      ← measure_empty (μ := Measure.pi (fun i : u ↦ μ i)), ← B_inter]
    exact tendsto_measure_iInter_atTop
      (fun n ↦ (MeasurableSet.of_mem_measurableCylinders (B_mem n)).nullMeasurableSet)
      B_anti ⟨0, measure_ne_top _ _⟩
  · -- If `u` is infinite, then we have an equivalence with `ℕ` so we can apply `secondLemma`.
    have count_u : Countable u := Set.countable_iUnion (fun n ↦ (s n).countable_toSet)
    obtain ⟨φ, -⟩ := Classical.exists_true_of_nonempty (α := ℕ ≃ u) nonempty_equiv_of_countable
    simp_rw [kol]
    exact secondLemma (fun i : u ↦ μ i) φ B_mem B_anti B_inter

/-- The `kolContent` associated to a family of probability measures is σ-subadditive. -/
theorem kolContent_pi_sigma_subadditive ⦃f : ℕ → Set (Π i, X i)⦄
    (hf : ∀ n, f n ∈ measurableCylinders X) (hf_Union : (⋃ n, f n) ∈ measurableCylinders X) :
    kolContent (isProjectiveMeasureFamily_pi μ) (⋃ n, f n) ≤
    ∑' n, kolContent (isProjectiveMeasureFamily_pi μ) (f n) := by
  classical
  have : ∀ i, Nonempty (X i) := fun i ↦ ProbabilityMeasure.nonempty ⟨μ i, hμ i⟩
  refine addContent_iUnion_le_of_addContent_iUnion_eq_tsum
    isSetRing_measurableCylinders (fun f hf hf_Union hf' ↦ ?_) f hf hf_Union
  exact addContent_iUnion_eq_sum_of_tendsto_zero isSetRing_measurableCylinders
    (kolContent (isProjectiveMeasureFamily_pi μ)) (fun s hs ↦ kolContent_ne_top _)
    (fun _ ↦ thirdLemma μ) hf hf_Union hf'

/-- The product measure of an arbitrary family of probability measures. It is defined as the unique
extension of the function which gives to cylinders the measure given by the associated product
measure. -/
noncomputable def Measure.productMeasure : Measure (Π i, X i) := by
  exact (kolContent (isProjectiveMeasureFamily_pi μ)).measure isSetSemiring_measurableCylinders
    generateFrom_measurableCylinders.ge (kolContent_pi_sigma_subadditive μ)

open Measure

/-- The product measure is the projective limit of the partial product measures. This ensures
uniqueness and expresses the value of the product measures applied to cylinders. -/
theorem isProjectiveLimit_productMeasure :
    IsProjectiveLimit (productMeasure μ) (fun I : Finset ι ↦ (Measure.pi (fun i : I ↦ μ i))) := by
  intro I
  ext1 s hs
  rw [Measure.map_apply (measurable_restrict I) hs, productMeasure, AddContent.measure_eq,
    kolContent_congr _ (_ ⁻¹' s) rfl hs]
  · exact generateFrom_measurableCylinders.symm
  · exact cylinder_mem_measurableCylinders _ _ hs

instance : IsProbabilityMeasure (productMeasure μ) := by
  constructor
  rw [← cylinder_univ ∅, cylinder, ← Measure.map_apply, isProjectiveLimit_productMeasure μ,
    measure_univ]
  · exact measurable_restrict _
  · exact MeasurableSet.univ

lemma productMeasure_boxes {s : Finset ι} {t : (i : ι) → Set (X i)}
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

theorem productMeasure_eq_pi [Fintype ι] : productMeasure μ = Measure.pi μ := by
  refine (pi_eq fun s hs ↦ ?_).symm
  rw [← coe_univ, productMeasure_boxes]
  simpa

lemma productMeasure_cylinder {s : Finset ι} {S : Set (Π i : s, X i)} (mS : MeasurableSet S) :
    productMeasure μ (cylinder s S) = Measure.pi (fun i : s ↦ μ i) S := by
  rw [cylinder, ← Measure.map_apply (measurable_restrict _) mS, isProjectiveLimit_productMeasure μ]

theorem integral_dep_productMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Finset ι} {f : (Π i : s, X i) → E}
    (hf : AEStronglyMeasurable f (Measure.pi (fun i : s ↦ μ i))) :
    ∫ y, f (s.restrict y) ∂productMeasure μ = ∫ y, f y ∂Measure.pi (fun i : s ↦ μ i) := by
  rw [← integral_map, isProjectiveLimit_productMeasure μ]
  · fun_prop
  · rwa [isProjectiveLimit_productMeasure μ]

/-- The canonical filtration on dependent functions indexed by `ι`, where `piFinset s` consists of
measurable sets depending only on coordinates is `s`. -/
def Filtration.piFinset : @Filtration (Π i, X i) (Finset ι) _ inferInstance where
  seq s := (inferInstance : MeasurableSpace (Π i : s, X i)).comap s.restrict
  mono' s t hst := by
    simp only
    rw [← restrict₂_comp_restrict hst, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_restrict₂ _).comap_le
  le' s := (measurable_restrict s).comap_le

open Filtration

/-- If a function is strongly measurable with respect to the σ-algebra generated by
the finite set of coordinates `s`, then it only depends on those coordinates. -/
theorem dependsOn_of_stronglyMeasurable' {E : Type*} [NormedAddCommGroup E]
    {s : Finset ι} {f : (Π i, X i) → E}
    (mf : StronglyMeasurable[piFinset s] f) : DependsOn f s := by
  intro x y hxy
  apply eq_of_stronglyMeasurable_comap s.restrict mf
  exact dependsOn_restrict s hxy

theorem integral_stronglyMeasurable [DecidableEq ι] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {s : Finset ι} {f : (Π i, X i) → E}
    (mf : StronglyMeasurable[piFinset s] f) (x : Π i, X i) :
    ∫ y, f y ∂productMeasure μ =
    ∫ y, f (Function.updateFinset x s y) ∂Measure.pi (fun i : s ↦ μ i) := by
  let g : (Π i : s, X i) → E := fun y ↦ f (Function.updateFinset x _ y)
  have this y : g (s.restrict y) = f y := by
    apply dependsOn_of_stronglyMeasurable' mf
    intro i hi
    simp only [Function.updateFinset, Finset.restrict, dite_eq_ite, ite_eq_left_iff]
    exact fun h ↦ (h hi).elim
  rw [← integral_congr_ae <| Eventually.of_forall this, integral_dep_productMeasure]
  exact mf.comp_measurable (measurable_updateFinset.mono le_rfl (piFinset.le s))
    |>.aestronglyMeasurable

theorem lintegral_dep {s : Finset ι} {f : (Π i : s, X i) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f (s.restrict y) ∂productMeasure μ = ∫⁻ y, f y ∂Measure.pi (fun i : s ↦ μ i) := by
  rw [← lintegral_map hf (measurable_restrict _), isProjectiveLimit_productMeasure μ]

/-- If a function is measurable with respect to the σ-algebra generated by
the finite set of coordinates `s`, then it only depends on those coordinates. -/
theorem measurable_dependsOn' {s : Finset ι} {f : (Π i, X i) → ℝ≥0∞}
    (mf : Measurable[piFinset s] f) : DependsOn f s := by
  intro x y hxy
  apply eq_of_measurable_comap s.restrict mf
  exact dependsOn_restrict s hxy

theorem lintegral_measurable_piFinset [DecidableEq ι] {s : Finset ι}
    {f : (Π i, X i) → ℝ≥0∞} (mf : Measurable[piFinset s] f)
    (x : Π i, X i) : ∫⁻ y, f y ∂productMeasure μ = (∫⋯∫⁻_s, f ∂μ) x := by
  let g : (Π i : s, X i) → ℝ≥0∞ := fun y ↦ f (Function.updateFinset x _ y)
  have this y : g (s.restrict y) = f y := by
    refine measurable_dependsOn' mf fun i hi ↦ ?_
    simp only [Function.updateFinset, Finset.restrict, dite_eq_ite, ite_eq_left_iff]
    exact fun h ↦ (h hi).elim
  simp_rw [← this]
  rw [lintegral_dep]
  · rfl
  · exact mf.comp (measurable_updateFinset.mono (_root_.le_refl _) (piFinset.le s))

end ProductMeasure
