/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Etienne Marion
-/
import KolmogorovExtension4.Annexe
import KolmogorovExtension4.DependsOn
import Mathlib.Probability.Kernel.Composition.MeasureComp

open Finset ENNReal ProbabilityTheory MeasureTheory Function Preorder MeasurableEquiv

variable {X : ℕ → Type*}

section Lemmas

@[measurability, fun_prop]
lemma measurable_cast {X Y : Type u} [mX : MeasurableSpace X] [mY : MeasurableSpace Y] (h : X = Y)
    (hm : HEq mX mY) : Measurable (cast h) := by
  subst h
  subst hm
  exact measurable_id

theorem update_updateFinset_eq (x z : Π n, X n) {m : ℕ} :
    update (updateFinset x (Iic m) (frestrictLe m z)) (m + 1) (z (m + 1)) =
    updateFinset x (Iic (m + 1)) (frestrictLe (m + 1) z) := by
  ext i
  simp only [update, updateFinset, mem_Iic, dite_eq_ite]
  split_ifs with h <;> try omega
  cases h
  all_goals rfl

instance subsingleton_subtype {α : Type*} (a : α) : Subsingleton ({a} : Finset α) where
  allEq x y := by
    rw [← Subtype.coe_inj, eq_of_mem_singleton x.2, eq_of_mem_singleton y.2]

lemma updateFinset_updateFinset_subset {ι : Type*} [DecidableEq ι] {α : ι → Type*}
    {s t : Finset ι} (hst : s ⊆ t) (x : (i : ι) → α i) (y : (i : s) → α i) (z : (i : t) → α i) :
    updateFinset (updateFinset x s y) t z = updateFinset x t z := by
  ext i
  simp only [updateFinset]
  split_ifs with h1 h2 <;> try rfl
  exact (h1 (hst h2)).elim

end Lemmas

section Mappings

/-- Gluing `Iic a` and `Ioc a b` into `Iic b`. If `b < a`, this is just a projection on the first
coordinate followed by a restriction, see `IicProdIoc_le`. -/
def IicProdIoc (a b : ℕ) (x : (Π i : Iic a, X i) × (Π i : Ioc a b, X i)) : Π i : Iic b, X i :=
    fun i ↦ if h : i ≤ a then x.1 ⟨i, mem_Iic.2 h⟩
      else x.2 ⟨i, mem_Ioc.2 ⟨not_le.1 h, mem_Iic.1 i.2⟩⟩

/-- When `IicProdIoc` is only partially apply (i.e. `IicProdIoc a b x` but not `IicProdIoc a b x i`)
`simp [IicProdIoc]` won't unfold the definition. This lemma allows to unfold it
by writing `simp [IicProdIoc_def]`. -/
lemma IicProdIoc_def (a b : ℕ) :
    IicProdIoc (X := X) a b = fun x i ↦ if h : i.1 ≤ a then x.1 ⟨i, mem_Iic.2 h⟩
      else x.2 ⟨i, mem_Ioc.2 ⟨not_le.1 h, mem_Iic.1 i.2⟩⟩ := rfl

lemma frestrictLe₂_comp_IicProdIoc {a b : ℕ} (hab : a ≤ b) :
    (frestrictLe₂ hab) ∘ (IicProdIoc (X := X) a b) = Prod.fst := by
  ext x i
  simp [IicProdIoc, mem_Iic.1 i.2]

lemma IicProdIoc_self (a : ℕ) : IicProdIoc (X := X) a a = Prod.fst := by
  ext x i
  simp [IicProdIoc, mem_Iic.1 i.2]

lemma IicProdIoc_le {a b : ℕ} (hba : b ≤ a) :
    IicProdIoc (X := X) a b = (frestrictLe₂ hba) ∘ Prod.fst := by
  ext x i
  simp [IicProdIoc, (mem_Iic.1 i.2).trans hba]

/-- Gluing `Ioc a b` and `Ioc b c` into `Ioc a c`. -/
def IocProdIoc (a b c : ℕ) (x : (Π i : Ioc a b, X i) × (Π i : Ioc b c, X i)) : Π i : Ioc a c, X i :=
    fun i ↦ if h : i ≤ b then x.1 ⟨i, mem_Ioc.2 ⟨(mem_Ioc.1 i.2).1, h⟩⟩
      else x.2 ⟨i, mem_Ioc.2 ⟨not_le.1 h, (mem_Ioc.1 i.2).2⟩⟩

variable [∀ n, MeasurableSpace (X n)]

@[measurability, fun_prop]
lemma measurable_IicProdIoc {m n : ℕ} : Measurable (IicProdIoc (X := X) m n) := by
  apply measurable_pi_lambda _ (fun (i : Iic n) ↦ ?_)
  by_cases h : i ≤ m
  · simpa [IicProdIoc, h] using measurable_fst.eval
  · simpa [IicProdIoc, h] using measurable_snd.eval

@[measurability, fun_prop]
lemma measurable_IocProdIoc {a b c : ℕ} : Measurable (IocProdIoc (X := X) a b c) := by
  apply measurable_pi_lambda _ (fun i ↦ ?_)
  by_cases h : i ≤ b
  · simpa [IocProdIoc, h] using measurable_fst.eval
  · simpa [IocProdIoc, h] using measurable_snd.eval

/-- Identifying `{n + 1}` with `Ioc n (n + 1)`, as a measurable equiv on dependent functions. -/
def MeasurableEquiv.piSingleton (a : ℕ) : (X (a + 1)) ≃ᵐ ((i : Ioc a (a + 1)) → X i) where
  toFun := fun x i ↦ (mem_Ioc_succ.1 i.2).symm ▸ x
  invFun := fun x ↦ x ⟨a + 1, right_mem_Ioc.2 a.lt_succ_self⟩
  left_inv := fun x ↦ by simp
  right_inv := fun x ↦ funext fun i ↦ by cases mem_Ioc_succ' i; rfl
  measurable_toFun := by
    simp_rw [eqRec_eq_cast]
    refine measurable_pi_lambda _ (fun i ↦ measurable_cast _ ?_)
    cases mem_Ioc_succ' i; rfl
  measurable_invFun := measurable_pi_apply _

/-- Gluing `Iic a` and `Ioi a` into `ℕ`, version as a measurable equivalence
on dependent functions. -/
def IicProdIoi (a : ℕ) : ((Π i : Iic a, X i) × ((i : Set.Ioi a) → X i)) ≃ᵐ (Π n, X n) :=
  { toFun := fun x i ↦ if hi : i ≤ a
      then x.1 ⟨i, mem_Iic.2 hi⟩
      else x.2 ⟨i, Set.mem_Ioi.2 (not_le.1 hi)⟩
    invFun := fun x ↦ (fun i ↦ x i, fun i ↦ x i)
    left_inv := fun x ↦ by
      ext i
      · simp [mem_Iic.1 i.2]
      · simp [not_le.2 <| Set.mem_Ioi.1 i.2]
    right_inv := fun x ↦ by simp
    measurable_toFun := by
      refine measurable_pi_lambda _ (fun i ↦ ?_)
      by_cases hi : i ≤ a <;> simp only [Equiv.coe_fn_mk, hi, ↓reduceDIte]
      · exact measurable_fst.eval
      · exact measurable_snd.eval
    measurable_invFun := Measurable.prod_mk (measurable_restrict _) (Set.measurable_restrict _) }

end Mappings

variable [∀ n, MeasurableSpace (X n)] {a b c : ℕ}
  {κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1))}

section ptraj

namespace ProbabilityTheory
namespace Kernel

variable (κ) in
/-- Given a family of kernels `κ n` from `X 0 × ... × X n` to `X (n + 1)` for all `n`,
construct a kernel from `X 0 × ... × X a` to `X 0 × ... × X b` by iterating `κ`.

The idea is that the input is some trajectory up to time `a`, and the ouptut is the distribution
of the trajectory up to time `b`. In particular if `b ≤ a`, this is just a deterministic kernel
(see `ptraj_le`). The name `ptraj` stands for "partial trajectory".

This kernel is extended in the file `IonescuTulcea` into a kernel with codomain `Π n, X n`. -/
noncomputable def ptraj (κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1))) (a b : ℕ) :
    Kernel (Π i : Iic a, X i) (Π i : Iic b, X i) := by
  induction b with
  | zero => exact deterministic (frestrictLe₂ (zero_le a)) (measurable_frestrictLe₂ _)
  | succ k κ_k =>
    exact if h : k + 1 ≤ a
      then deterministic (frestrictLe₂ h) (measurable_frestrictLe₂ h)
      else ((Kernel.id ×ₖ ((κ k).map (piSingleton k))) ∘ₖ κ_k).map (IicProdIoc k (k + 1))

section Basic

lemma ptraj_succ_eq (a b : ℕ) :
    ptraj κ a (b + 1) = if hab : b + 1 ≤ a
      then deterministic (frestrictLe₂ hab) (measurable_frestrictLe₂ hab)
      else ((Kernel.id ×ₖ ((κ b).map (piSingleton b))) ∘ₖ ptraj κ a b).map (IicProdIoc b (b + 1)) :=
  rfl

/-- If `b ≤ a`, given the trajectory up to time `a`, the trajectory up to time `b` is
deterministic and is equal to the restriction of the trajectory up to time `a`. -/
lemma ptraj_le (hba : b ≤ a) :
    ptraj κ a b = deterministic (frestrictLe₂ hba) (measurable_frestrictLe₂ _) := by
  induction b with
  | zero => rfl
  | succ k hk => rw [ptraj_succ_eq, dif_pos hba]

lemma ptraj_zero :
    ptraj κ a 0 = deterministic (frestrictLe₂ (zero_le a)) (measurable_frestrictLe₂ _) := by
  rw [ptraj_le (zero_le a)]

instance (a b : ℕ) : IsSFiniteKernel (ptraj κ a b) := by
  induction b with
  | zero => rw [ptraj_zero]; infer_instance
  | succ k hk =>
    rw [ptraj_succ_eq]
    split_ifs with hab <;> infer_instance

instance [∀ n, IsFiniteKernel (κ n)] (a b : ℕ) : IsFiniteKernel (ptraj κ a b) := by
  induction b with
  | zero => rw [ptraj_zero]; infer_instance
  | succ k hk =>
    rw [ptraj_succ_eq]
    split_ifs with hab <;> infer_instance

instance [∀ n, IsZeroOrMarkovKernel (κ n)] (a b : ℕ) : IsZeroOrMarkovKernel (ptraj κ a b) := by
  induction b with
  | zero => rw [ptraj_zero]; infer_instance
  | succ k hk =>
    rw [ptraj_succ_eq]
    split_ifs <;> infer_instance

instance [∀ n, IsMarkovKernel (κ n)] (a b : ℕ) : IsMarkovKernel (ptraj κ a b) := by
  induction b with
  | zero => rw [ptraj_zero]; infer_instance
  | succ k hk =>
    rw [ptraj_succ_eq]
    split_ifs
    · infer_instance
    · have := IsMarkovKernel.map (κ k) (piSingleton k).measurable
      exact IsMarkovKernel.map _ measurable_IicProdIoc

@[simp]
lemma ptraj_self (a : ℕ) : ptraj κ a a = Kernel.id := by
  rw [ptraj_le le_rfl]
  rfl

lemma ptraj_succ (hab : a ≤ b) : ptraj κ a (b + 1) =
    ((Kernel.id ×ₖ ((κ b).map (piSingleton b))) ∘ₖ (ptraj κ a b)).map (IicProdIoc b (b + 1)) := by
  rw [ptraj_succ_eq, dif_neg (by omega)]

lemma ptraj_succ_self (a : ℕ) : ptraj κ a (a + 1) =
    (Kernel.id ×ₖ ((κ a).map (piSingleton a))).map (IicProdIoc a (a + 1)) := by
  rw [ptraj_succ le_rfl, ptraj_self, comp_id]

lemma ptraj_succ_eq_comp (hab : a ≤ b) : ptraj κ a (b + 1) = ptraj κ b (b + 1) ∘ₖ ptraj κ a b := by
  induction b with
  | zero => rw [le_zero_iff.1 hab, ptraj_self, comp_id]
  | succ k hk =>
    rw [ptraj_succ_self, ← map_comp, ptraj_succ hab]

/-- Given the trajectory up to time `a`, `ptraj κ a b` gives the distribution of the trajectory
up to time `b`. Then plugging this into `ptraj κ b c` gives the distribution of the trajectory
up to time `c`. -/
theorem ptraj_comp_ptraj [∀ n, IsSFiniteKernel (κ n)] (hab : a ≤ b) (hbc : b ≤ c) :
    ptraj κ b c ∘ₖ ptraj κ a b = ptraj κ a c := by
  induction c, hbc using Nat.le_induction with
  | base => simp
  | succ k h hk => rw [ptraj_succ_eq_comp h, comp_assoc, hk, ← ptraj_succ_eq_comp (hab.trans h)]

/-- This is a technical lemma saying that `ptraj κ a b` consists of two independent parts, the
first one being the identity. It allows to compute integrals. -/
lemma ptraj_eq_prod [∀ n, IsSFiniteKernel (κ n)] {a b : ℕ} :
    ptraj κ a b =
      (Kernel.id ×ₖ (ptraj κ a b).map (restrict₂ Ioc_subset_Iic_self)).map (IicProdIoc a b) := by
  obtain hab | hba := le_total a b
  · induction b, hab using Nat.le_induction with
    | base =>
      ext1 x
      rw [ptraj_self, id_map, map_apply, prod_apply, IicProdIoc_self, ← Measure.fst,
        Measure.fst_prod]
      any_goals fun_prop
    | succ k h hk =>
      rw [← ptraj_comp_ptraj h k.le_succ, hk, ptraj_succ_self]
      ext x s ms
      rw [comp_apply', map_apply, MeasureTheory.lintegral_map, lintegral_id_prod, lintegral_map,
        map_apply', id_prod_apply', map_apply', comp_apply', lintegral_map, lintegral_id_prod,
        lintegral_map]
      · congr with y
        rw [map_apply', id_prod_apply', map_apply' (_ ×ₖ _), id_prod_apply']
        · congr with z
          simp only [IicProdIoc_def, restrict₂, Set.mem_preimage, subset_refl, Set.coe_inclusion]
          congrm (fun i ↦ ?_) ∈ s
          split_ifs with h1 h2 h3 <;> try rfl
          omega
        any_goals fun_prop
        all_goals exact ms.preimage (by fun_prop)
      any_goals fun_prop
      any_goals exact ms.preimage (by fun_prop)
      all_goals exact (Kernel.measurable_coe _ (ms.preimage (by fun_prop))).comp (by fun_prop)
  · rw [ptraj_le hba, IicProdIoc_le hba, ← map_map _ measurable_fst (measurable_frestrictLe₂ _),
      ← fst_eq, @fst_prod _ _ _ _ _ _ _ _ _ ?_, id_map]
    exact IsMarkovKernel.map _ (measurable_restrict₂ _)

variable [∀ n, IsMarkovKernel (κ n)]

lemma ptraj_succ_map_frestrictLe₂ (a b : ℕ) :
    (ptraj κ a (b + 1)).map (frestrictLe₂ b.le_succ) = ptraj κ a b := by
  obtain hab | hba := le_or_lt a b
  · have := IsMarkovKernel.map (κ b) (piSingleton b).measurable
    rw [ptraj_succ_eq_comp hab, map_comp, ptraj_succ_self, map_map, frestrictLe₂_comp_IicProdIoc,
      ← fst_eq, fst_prod, id_comp]
    all_goals fun_prop
  · rw [ptraj_le (Nat.succ_le.2 hba), ptraj_le hba.le, map_deterministic]
    · rfl
    · fun_prop

lemma ptraj_map_frestrictLe₂ (a : ℕ) (hbc : b ≤ c) :
    (ptraj κ a c).map (frestrictLe₂ hbc) = ptraj κ a b := by
  induction c, hbc using Nat.le_induction with
  | base => convert map_id ..
  | succ k h hk =>
    rw [← hk, ← frestrictLe₂_comp_frestrictLe₂ h k.le_succ, ← map_map, ptraj_succ_map_frestrictLe₂]
    any_goals fun_prop

lemma ptraj_map_frestrictLe₂_apply' (x₀ : Π i : Iic a, X i) (hbc : b ≤ c) :
    (ptraj κ a c x₀).map (frestrictLe₂ hbc) = ptraj κ a b x₀ := by
  rw [← map_apply _ (by fun_prop), ptraj_map_frestrictLe₂]

lemma ptraj_comp_ptraj' (c : ℕ) (hab : a ≤ b) :
    ptraj κ b c ∘ₖ ptraj κ a b = ptraj κ a c := by
  obtain hbc | hcb := le_total b c
  · rw [ptraj_comp_ptraj hab hbc]
  · rw [ptraj_le hcb, deterministic_comp_eq_map, ptraj_map_frestrictLe₂]

lemma ptraj_comp_ptraj'' {b c : ℕ} (hcb : c ≤ b) :
    ptraj κ b c ∘ₖ ptraj κ a b = ptraj κ a c := by
  rw [ptraj_le hcb, deterministic_comp_eq_map, ptraj_map_frestrictLe₂]

end Basic

section lmarginalPTraj

variable (κ)

/-- This function computes the integral of a function `f` against `ptraj`,
and allows to view it as a function depending on all the variables. -/
noncomputable def lmarginalPTraj (a b : ℕ) (f : (Π n, X n) → ℝ≥0∞) (x : Π n, X n) : ℝ≥0∞ :=
  ∫⁻ z : (i : Iic b) → X i, f (updateFinset x _ z) ∂(ptraj κ a b (frestrictLe a x))

/-- If `b ≤ a`, then integrating `f` against the `ptraj κ a b` does nothing. -/
lemma lmarginalPTraj_le (hba : b ≤ a) {f : (Π n, X n) → ℝ≥0∞} (mf : Measurable f) :
    lmarginalPTraj κ a b f = f := by
  ext x
  rw [lmarginalPTraj, ptraj_le hba, Kernel.lintegral_deterministic']
  · congr with i
    simp [updateFinset]
  · exact mf.comp measurable_updateFinset

variable {κ}

lemma lmarginalPTraj_mono (a b : ℕ) {f g : (Π n, X n) → ℝ≥0∞} (hfg : f ≤ g) (x : Π n, X n) :
    lmarginalPTraj κ a b f x ≤ lmarginalPTraj κ a b g x :=
  lintegral_mono fun _ ↦ hfg _

/-- Integrating `f` against `ptraj κ a b x` is the same as integrating only over the variables
  from `x_{a+1}` to `x_b`. -/
lemma lmarginalPTraj_eq_lintegral_map [∀ n, IsSFiniteKernel (κ n)] {f : (Π n, X n) → ℝ≥0∞}
    (mf : Measurable f) (x : Π n, X n) :
    lmarginalPTraj κ a b f x =
      ∫⁻ (y : Π i : Ioc a b, X i), f (updateFinset x _ y)
        ∂(ptraj κ a b).map (restrict₂ Ioc_subset_Iic_self) (frestrictLe a x) := by
  nth_rw 1 [lmarginalPTraj, ptraj_eq_prod, lintegral_map, lintegral_id_prod]
  · congrm ∫⁻ y, f (fun i ↦ ?_) ∂_
    simp only [updateFinset, mem_Iic, IicProdIoc, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk,
      frestrictLe_apply, restrict₂, mem_Ioc]
    split_ifs <;> try rfl
    all_goals omega
  all_goals fun_prop

/-- Integrating `f` against `ptraj κ a (a + 1)` is the same as integrating against `κ a`. -/
lemma lmarginalPTraj_succ [∀ n, IsFiniteKernel (κ n)] (a : ℕ)
    {f : (Π n, X n) → ℝ≥0∞} (mf : Measurable f) (x₀ : Π n, X n) :
    lmarginalPTraj κ a (a + 1) f x₀ =
      ∫⁻ x : X (a + 1), f (update x₀ _ x) ∂κ a (frestrictLe a x₀) := by
  rw [lmarginalPTraj, ptraj_succ_self, lintegral_map, lintegral_id_prod, lintegral_map]
  · congrm ∫⁻ x, f (fun i ↦ ?_) ∂_
    simp [updateFinset, piSingleton, IicProdIoc, update]
    split_ifs with h1 h2 h3 <;> try rfl
    all_goals omega
  all_goals fun_prop

@[measurability, fun_prop]
lemma measurable_lmarginalPTraj [∀ n, IsSFiniteKernel (κ n)] (a b : ℕ)
    {f : (Π n, X n) → ℝ≥0∞} (hf : Measurable f) : Measurable (lmarginalPTraj κ a b f) := by
  unfold lmarginalPTraj
  let g : ((i : Iic b) → X i) × (Π n, X n) → ℝ≥0∞ := fun c ↦ f (updateFinset c.2 _ c.1)
  let η : Kernel (Π n, X n) (Π i : Iic b, X i) :=
    (ptraj κ a b).comap (frestrictLe a) (measurable_frestrictLe _)
  change Measurable fun x ↦ ∫⁻ z : (i : Iic b) → X i, g (z, x) ∂η x
  refine Measurable.lintegral_kernel_prod_left' <| hf.comp ?_
  simp only [updateFinset, measurable_pi_iff]
  intro i
  by_cases h : i ∈ Iic b <;> simp [h] <;> fun_prop

/-- Integrating `f` against `ptraj κ a b` and then against `ptraj κ b c` is the same
as integrating `f` against `ptraj κ a c`. -/
theorem lmarginalPTraj_self [∀ n, IsSFiniteKernel (κ n)] {a b c : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c)
    {f : (Π n, X n) → ℝ≥0∞} (hf : Measurable f) :
    lmarginalPTraj κ a b (lmarginalPTraj κ b c f) = lmarginalPTraj κ a c f := by
  ext x
  obtain rfl | hab := eq_or_lt_of_le hab <;> obtain rfl | hbc := eq_or_lt_of_le hbc
  · rw [lmarginalPTraj_le κ le_rfl (measurable_lmarginalPTraj _ _ hf)]
  · rw [lmarginalPTraj_le κ le_rfl (measurable_lmarginalPTraj _ _ hf)]
  · rw [lmarginalPTraj_le κ le_rfl hf]
  simp_rw [lmarginalPTraj, frestrictLe, restrict_updateFinset,
    updateFinset_updateFinset_subset (Iic_subset_Iic.2 hbc.le)]
  rw [← lintegral_comp, ptraj_comp_ptraj hab.le hbc.le]
  fun_prop

end lmarginalPTraj

end Kernel
end ProbabilityTheory

end ptraj

open ProbabilityTheory Kernel

variable [∀ n, IsMarkovKernel (κ n)]

namespace DependsOn

/-- If `f` only depends on the variables up to rank `a` and `a ≤ b`, integrating `f` against
`ptraj κ b c` does nothing. -/
theorem lmarginalPTraj_le (c : ℕ) {f : (Π n, X n) → ℝ≥0∞} (mf : Measurable f)
    (hf : DependsOn f (Iic a)) (hab : a ≤ b) :
    lmarginalPTraj κ b c f = f := by
  ext x
  rw [lmarginalPTraj_eq_lintegral_map mf]
  refine @lintegral_eq_const _ _ _ ?_ _ _ fun y ↦ hf fun i hi ↦ ?_
  · refine @IsMarkovKernel.isProbabilityMeasure _ _ _ _ _ ?_ _
    exact IsMarkovKernel.map _ (by fun_prop)
  · simp_all only [coe_Iic, Set.mem_Iic, updateFinset, mem_Ioc, dite_eq_right_iff]
    exact fun h ↦ by omega

/-- If `f` only depends on the variables uo to rank `a`, integrating beyond rank `a` is the same
as integrating up to rank `a`. -/
theorem lmarginalPTraj_right {a : ℕ} (b : ℕ) {d : ℕ}
    (mf : Measurable f) (hf : DependsOn f (Iic a)) (hac : a ≤ c) (had : a ≤ d) :
    lmarginalPTraj κ b c f = lmarginalPTraj κ b d f := by
  wlog hcd : c ≤ d generalizing c d
  · rw [this had hac (le_of_not_le hcd)]
  · obtain hbc | hcb := le_total b c
    · rw [← lmarginalPTraj_self hbc hcd mf, hf.lmarginalPTraj_le d mf hac]
    · rw [hf.lmarginalPTraj_le c mf (hac.trans hcb), hf.lmarginalPTraj_le d mf (hac.trans hcb)]

/-- If `f` only depends on variables up to rank `b`, its integral from `a` to `b` only depends on
variables up to rank `a`. -/
theorem dependsOn_lmarginalPTraj (a : ℕ) {f : (Π n, X n) → ℝ≥0∞}
    (hf : DependsOn f (Iic b)) (mf : Measurable f) :
    DependsOn (lmarginalPTraj κ a b f) (Iic a) := by
  intro x y hxy
  obtain hba | hab := le_total b a
  · rw [Kernel.lmarginalPTraj_le κ hba mf]
    exact hf fun i hi ↦ hxy i (Iic_subset_Iic.2 hba hi)
  · rw [lmarginalPTraj_eq_lintegral_map mf, lmarginalPTraj_eq_lintegral_map mf]
    congrm ∫⁻ z : _, ?_ ∂(ptraj κ a b).map _ (fun i ↦ ?_)
    · exact hxy i.1 i.2
    · refine dependsOn_updateFinset hf _ _ ?_
      rwa [← coe_sdiff, Iic_sdiff_Ioc_same hab]

end DependsOn
