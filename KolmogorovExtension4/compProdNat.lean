/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Etienne Marion
-/
import KolmogorovExtension4.Projections

open Finset ENNReal ProbabilityTheory MeasureTheory

noncomputable section

section compProdNat

lemma measurable_cast {X Y : Type u} [mX : MeasurableSpace X] [mY : MeasurableSpace Y] (h : X = Y)
    (hm : HEq mX mY) : Measurable (cast h) := by
  subst h
  subst hm
  exact measurable_id

variable {X : ℕ → Type*} [∀ i, MeasurableSpace (X i)]

section equivs

/-- Identifying `{n + 1}` with `Ioc n (n+1)`, as a measurable equiv on dependent functions. -/
def e (n : ℕ) : (X (n + 1)) ≃ᵐ ((i : Ioc n (n + 1)) → X i) where
  toFun := fun x i ↦ (mem_Ioc_succ.1 i.2).symm ▸ x
  invFun := fun x ↦ x ⟨n + 1, right_mem_Ioc.2 n.lt_succ_self⟩
  left_inv := fun x ↦ by simp
  right_inv := fun x ↦ by
    ext i
    have : ⟨n + 1, right_mem_Ioc.2 n.lt_succ_self⟩ = i := by
      simp [(mem_Ioc_succ.1 i.2).symm]
    cases this; rfl
  measurable_toFun := by
    refine measurable_pi_lambda _ (fun i ↦ ?_)
    simp_rw [eqRec_eq_cast]
    apply measurable_cast
    have : ⟨n + 1, right_mem_Ioc.2 n.lt_succ_self⟩ = i := by
      simp [(mem_Ioc_succ.1 i.2).symm]
    cases this; rfl
  measurable_invFun := measurable_pi_apply _

/-- Gluing `Iic m` and `Ioc m n` into `Iic n`, as a measurable equiv of dependent functions. -/
def el (m n : ℕ) (hmn : m ≤ n) :
    ((i : Iic m) → X i) × ((i : Ioc m n) → X i) ≃ᵐ ((i : Iic n) → X i) where
  toFun := fun p x ↦ if h : x ≤ m then p.1 ⟨x, mem_Iic.2 h⟩
    else p.2 ⟨x, mem_Ioc.2 ⟨not_le.mp h, mem_Iic.1 x.2⟩⟩
  invFun := fun p ↦ ⟨fun x ↦ p ⟨x, mem_Iic.2 <| (mem_Iic.mp x.2).trans hmn⟩,
    fun x ↦ p ⟨x, mem_Iic.2 (mem_Ioc.mp x.2).2⟩⟩
  left_inv := fun p ↦ by
    ext i
    · simp [mem_Iic.1 i.2]
    · simp [not_le.2 (mem_Ioc.mp i.2).1]
  right_inv := fun p ↦ by
    ext i
    by_cases hi : i.1 ≤ m <;> simp [hi]
  measurable_toFun := by
    apply measurable_pi_lambda _ (fun (x : Iic n) ↦ ?_)
    by_cases h : x ≤ m
    · simp only [Equiv.coe_fn_mk, h, dite_true]
      exact measurable_fst.eval
    · simp only [Equiv.coe_fn_mk, h, dite_false]
      exact measurable_snd.eval
  measurable_invFun := by
    refine Measurable.prod_mk ?_ ?_ <;> exact measurable_pi_lambda _ (fun a ↦ measurable_id.eval)

/-- Gluing `Ioc i j` and `Ioc j k` into `Ioc i k`, as a measurable equiv of dependent functions. -/
def er (i j k : ℕ) (hij : i < j) (hjk : j ≤ k) :
    ((l : Ioc i j) → X l) × ((l : Ioc j k) → X l) ≃ᵐ ((l : Ioc i k) → X l) where
  toFun := fun p x ↦ if h : x ≤ j then p.1 ⟨x, mem_Ioc.2 ⟨(mem_Ioc.1 x.2).1, h⟩⟩
    else p.2 ⟨x, mem_Ioc.2 ⟨not_le.mp h, (mem_Ioc.1 x.2).2⟩⟩
  invFun := fun p ↦ ⟨fun x ↦ p ⟨x, mem_Ioc.2 ⟨(mem_Ioc.1 x.2).1, (mem_Ioc.1 x.2).2.trans hjk⟩⟩,
    fun x ↦ p ⟨x, mem_Ioc.2 ⟨hij.trans (mem_Ioc.1 x.2).1, (mem_Ioc.1 x.2).2⟩⟩⟩
  left_inv := fun p ↦ by
    ext x
    · simp only
      rw [dif_pos (mem_Ioc.1 x.2).2]
    · simp only
      rw [dif_neg (not_le.mpr (mem_Ioc.1 x.2).1)]
  right_inv := fun p ↦ by
    ext x
    simp only
    split_ifs <;> rfl
  measurable_toFun := by
    apply measurable_pi_lambda _ (fun x ↦ ?_)
    by_cases h : x ≤ j
    · simp only [Equiv.coe_fn_mk, h, dite_true]
      exact measurable_fst.eval
    · simp only [Equiv.coe_fn_mk, h, dite_false]
      exact measurable_snd.eval
  measurable_invFun := by
    refine Measurable.prod_mk ?_ ?_ <;> exact measurable_pi_lambda _ (fun a ↦ measurable_id.eval)

theorem fproj₂_er (i j k : ℕ) (hij : i < j) (hjk : j ≤ k)
    (y : (n : Ioc i j) → X n) (z : (n : Ioc j k) → X n) :
    fproj₂ (Ioc_subset_Ioc_right hjk) (er i j k hij hjk (y, z)) = y := by
  ext n
  simp [fproj₂, er, (mem_Ioc.1 n.2).2]

lemma el_assoc {i j k : ℕ} (hij : i < j) (hjk : j ≤ k) (a : (x : Iic i) → X ↑x)
    (b : (l : Ioc i j) → X l) (c : (l : Ioc j k) → X l) :
    el j k hjk (el i j hij.le (a, b), c)
      = el i k (hij.le.trans hjk) (a, er i j k hij hjk (b, c)) := by
  ext x
  simp only [el, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, er]
  split_ifs with h _ h3
  · rfl
  · rfl
  · exfalso; exact h (h3.trans hij.le)
  · rfl

lemma er_assoc {i j k l : ℕ} (hij : i < j) (hjk : j < k) (hkl : k ≤ l)
    (b : (l : Ioc i j) → X l) (c : (l : Ioc j k) → X l) (d : (m : Ioc k l) → X m) :
    er i j l hij (hjk.le.trans hkl) (b, er j k l hjk hkl (c, d))
      = er i k l (hij.trans hjk) hkl (er i j k hij hjk.le (b, c), d) := by
  ext x
  simp only [MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, er]
  split_ifs with h h2
  · rfl
  · exfalso; exact h2 (h.trans hjk.le)
  · rfl
  · rfl

end equivs

/-- When `j = k`, then `Ioc i j = Ioc i k`, as a measurable equiv of dependent functions. -/
def e_path_eq {i j k : ℕ} (h : j = k) : ((l : Ioc i j) → X l) ≃ᵐ ((l : Ioc i k) → X l) :=
  MeasurableEquiv.cast (by rw [h]) (by rw [h])

/-- Given a kernel from variables in `Iic j`, split `Iic j` into the
union of `Iic i` and `Ioc i j` and construct the resulting kernel.
TODO: the target space could be anything, generalize. -/
def split (i j k : ℕ) (hij : i < j)
    (κ : Kernel ((l : Iic j) → X l) ((l : Ioc j k) → X l)) :
    Kernel (((l : Iic i) → X l) × ((l : Ioc i j) → X l)) ((l : Ioc j k) → X l) :=
  Kernel.comap κ (el i j hij.le) (el i j hij.le).measurable

lemma split_eq_comap (i j k : ℕ) (hij : i < j)
    (κ : Kernel ((l : Iic j) → X l) ((l : Ioc j k) → X l)) :
    split i j k hij κ = Kernel.comap κ (el i j hij.le) (el i j hij.le).measurable := rfl

instance {i j k : ℕ} (hij : i < j) (κ : Kernel ((l : Iic j) → X l) ((l : Ioc j k) → X l))
    [IsSFiniteKernel κ] :
    IsSFiniteKernel (split i j k hij κ) := by
  rw [split]
  infer_instance

instance {i j k : ℕ} (hij : i < j) (κ : Kernel ((l : Iic j) → X l) ((l : Ioc j k) → X l))
    [IsFiniteKernel κ] :
    IsFiniteKernel (split i j k hij κ) := by
  rw [split]
  infer_instance

@[simp]
lemma split_zero (i j k : ℕ) (hij : i < j) :
    split i j k hij (0 : Kernel ((l : Iic j) → X l) ((l : Ioc j k) → X l)) = 0 := by
  rw [split] -- todo: Kernel.comap_zero missing as simp lemma
  ext1 a
  rw [Kernel.comap_apply, Kernel.zero_apply, Kernel.zero_apply]

open Classical

namespace ProbabilityTheory
namespace Kernel

/-- Given a kernel from variables in `Ici i` to `Ioc i j`, and another one from variables in
`Iic j` to `Ioc j k`, compose them to get a kernel from `Ici i` to `Ioc i k`. This makes sense
only when `i < j` and `j < k`. Otherwise, use `0` as junk value. -/
def compProdNat {i j k : ℕ} (κ : Kernel ((l : Iic i) → X l) ((l : Ioc i j) → X l))
    (η : Kernel ((l : Iic j) → X l) ((l : Ioc j k) → X l)) :
    Kernel ((l : Iic i) → X l) ((l : Ioc i k) → X l) :=
  if h : i < j ∧ j < k
    then Kernel.map (κ ⊗ₖ split i j k h.1 η) (er i j k h.1 h.2.le) (er i j k h.1 h.2.le).measurable
    else 0

lemma compProdNat_eq {i j k : ℕ} (κ : Kernel ((l : Iic i) → X l) ((l : Ioc i j) → X l))
    (η : Kernel ((l : Iic j) → X l) ((l : Ioc j k) → X l)) (hij : i < j) (hjk : j < k) :
    compProdNat κ η = Kernel.map (κ ⊗ₖ split i j k hij η) (er i j k hij hjk.le)
      (er i j k hij hjk.le).measurable := by
  rw [compProdNat, dif_pos]
  exact ⟨hij, hjk⟩

instance {i j k : ℕ} (κ : Kernel ((l : Iic i) → X l) ((l : Ioc i j) → X l))
    (η : Kernel ((l : Iic j) → X l) ((l : Ioc j k) → X l)) :
    IsSFiniteKernel (compProdNat κ η) := by
  rw [compProdNat]
  split_ifs <;> infer_instance

instance {i j k : ℕ} (κ : Kernel ((l : Iic i) → X l) ((l : Ioc i j) → X l))
    [IsFiniteKernel κ]
    (η : Kernel ((l : Iic j) → X l) ((l : Ioc j k) → X l))
    [IsFiniteKernel η] :
    IsFiniteKernel (compProdNat κ η) := by
  rw [compProdNat]
  split_ifs <;> infer_instance

@[inherit_doc]
notation κ " ⊗ₖ' " η => compProdNat κ η

lemma compProdNat_apply' {i j k : ℕ} (κ : Kernel ((l : Iic i) → X l) ((l : Ioc i j) → X l))
    (η : Kernel ((l : Iic j) → X l) ((l : Ioc j k) → X l)) [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (hij : i < j) (hjk : j < k) (a : (l : Iic i) → X l) {s : Set ((l : Ioc i k) → X l)}
    (hs : MeasurableSet s) :
    (κ ⊗ₖ' η) a s
      = ∫⁻ b, η (el i j hij.le (a, b)) {c | (b, c) ∈ er i j k hij hjk.le ⁻¹' s} ∂(κ a) := by
  rw [compProdNat_eq _ _ hij hjk, Kernel.map_apply' _ _ _ hs,
    Kernel.compProd_apply _ _ _ ((er _ _ _ _ _).measurable hs)]
  simp_rw [split, Kernel.comap_apply]

@[simp]
lemma compProdNat_zero_right {i j : ℕ}
    (κ : Kernel ((l : Iic i) → X l) ((l : Ioc i j) → X l)) (k : ℕ) :
    (κ ⊗ₖ' (0 : Kernel ((l : Iic j) → X l) ((l : Ioc j k) → X l))) = 0 := by
  rw [compProdNat]
  split_ifs
  · simp only [split_zero, Kernel.compProd_zero_right, Kernel.map_zero]
  · rfl

@[simp]
lemma compProdNat_zero_left {j k : ℕ} (i : ℕ)
    (κ : Kernel ((l : Iic j) → X l) ((l : Ioc j k) → X l)) :
    ((0 : Kernel ((l : Iic i) → X l) ((l : Ioc i j) → X l)) ⊗ₖ' κ) = 0 := by
  rw [compProdNat]
  split_ifs
  · simp only [Kernel.compProd_zero_left, Kernel.map_zero]
  · rfl

lemma compProdNat_undef_left {i j k : ℕ} (κ : Kernel ((l : Iic i) → X l) ((l : Ioc i j) → X l))
    (η : Kernel ((l : Iic j) → X l) ((l : Ioc j k) → X l)) (hij : i < j) (hjk : j < k)
    (h : ¬ IsSFiniteKernel κ) :
    (κ ⊗ₖ' η) = 0 := by
  rw [compProdNat_eq _ _ hij hjk, Kernel.compProd_of_not_isSFiniteKernel_left _ _ h]
  simp

lemma compProdNat_assoc {i j k l : ℕ} (κ : Kernel ((l : Iic i) → X l) ((l : Ioc i j) → X l))
    (η : Kernel ((l : Iic j) → X l) ((l : Ioc j k) → X l))
    (ξ : Kernel ((l : Iic k) → X l) ((m : Ioc k l) → X m))
    [IsSFiniteKernel η] [IsSFiniteKernel ξ]
    (hij : i < j) (hjk : j < k) (hkl : k < l) :
    (κ ⊗ₖ' (η ⊗ₖ' ξ)) = (κ ⊗ₖ' η) ⊗ₖ' ξ := by
  by_cases hκ : IsSFiniteKernel κ
  swap
  · rw [compProdNat_undef_left _ _ hij (hjk.trans hkl) hκ, compProdNat_undef_left _ _ hij hjk hκ]
    simp
  ext a s hs
  have h_comp_det : ∀ b, ξ (el i k (hij.trans hjk).le (a, b))
      = (ξ ∘ₖ Kernel.deterministic (el i k (hij.trans hjk).le)
          (el i k (hij.trans hjk).le).measurable) (a, b) := by
    intro b
    rw [Kernel.comp_deterministic_eq_comap, Kernel.comap_apply]
  have h_meas_comp : Measurable fun b ↦
      ξ (el i k (hij.trans hjk).le (a, b))
        {c | (b, c) ∈ er i k l (hij.trans hjk) hkl.le ⁻¹' s} := by
    simp_rw [h_comp_det]
    exact Kernel.measurable_kernel_prod_mk_left' ((er _ _ _ _ _).measurable hs) a
  rw [compProdNat_apply' _ _ hij (hjk.trans hkl) _ hs,
    compProdNat_apply' _ _ (hij.trans hjk) hkl _ hs, compProdNat_eq _ _ hjk hkl,
    compProdNat_eq _ _ hij hjk, map_apply,
    MeasureTheory.lintegral_map h_meas_comp (er _ _ _ _ _).measurable]
  have : ∀ b, MeasurableSet {c | (b, c) ∈ er i j l hij (hjk.trans hkl).le ⁻¹' s} :=
    fun b ↦ (@measurable_prod_mk_left _ _ inferInstance _ b) ((er _ _ _ _ _).measurable hs)
  simp_rw [Kernel.map_apply' _ _ _ (this _)]
  have : ∀ b, MeasurableSet
      (er j k l hjk hkl.le ⁻¹' {c | (b, c) ∈ er i j l hij (hjk.trans hkl).le ⁻¹' s}) :=
    fun b ↦ (er _ _ _ _ _).measurable (this b)
  simp_rw [compProd_apply _ _ _ (this _), split, Kernel.comap_apply]
  rw [lintegral_compProd]
  swap; exact h_meas_comp.comp (er i j k hij hjk.le).measurable
  simp only [comap_apply, el_assoc, Set.mem_preimage, Set.preimage_setOf_eq, Set.mem_setOf_eq,
    er_assoc]
  simp_rw [el_assoc hij hjk.le]

/-- Given a kernel taking values in `Ioc i j`, convert it to a kernel taking values
in `Ioc i k` when `j = k`. -/
def castPath {i j k : ℕ} (κ : Kernel ((l : Iic i) → X l) ((l : Ioc i j) → X l)) (h : j = k) :
    Kernel ((l : Iic i) → X l) ((l : Ioc i k) → X l) :=
  Kernel.map κ (e_path_eq h) (MeasurableEquiv.measurable _)

lemma castPath_apply {i j k : ℕ} (κ : Kernel ((l : Iic i) → X l) ((l : Ioc i j) → X l)) (h : j = k)
    (a : (l : Iic i) → X l) (s : Set ((l : Ioc i k) → X l)) (hs : MeasurableSet s) :
    castPath κ h a s = κ a (e_path_eq h ⁻¹' s) := by
  rw [castPath, Kernel.map_apply' _ _ _ hs]

instance {i j k : ℕ} (κ : Kernel ((l : Iic i) → X l) ((l : Ioc i j) → X l)) (h : j = k)
    [IsSFiniteKernel κ] :
    IsSFiniteKernel (castPath κ h) := by
  rw [castPath]; infer_instance

instance {i j k : ℕ} (κ : Kernel ((l : Iic i) → X l) ((l : Ioc i j) → X l)) (h : j = k)
    [IsFiniteKernel κ] :
    IsFiniteKernel (castPath κ h) := by
  rw [castPath]; infer_instance

section kerNat

variable {i j k : ℕ}

/-- Given a kernel `κ₀` from variables in `Iic i` to `Ioc i j`, and a family of kernels `κ_k`
from `Iic k` to `X (k + 1)`, one can compose the kernels to get a kernel from `Ici i` to `Ioc i k`
as the composition of `κ₀` with `κ_j` then `κ_{j+1}` ... then `κ_{k-1}`. -/
def kerInterval (κ₀ : Kernel ((l : Iic i) → X l) ((l : Ioc i j) → X l))
    (κ : ∀ k, Kernel ((l : Iic k) → X l) (X (k + 1))) (k : ℕ) :
    Kernel ((l : Iic i) → X l) ((l : Ioc i k) → X l) := by
  induction k with
  | zero => exact 0
  | succ k κ_k => exact if h : j = k + 1 then castPath κ₀ h else
    (κ_k ⊗ₖ' (Kernel.map (κ k) (e k) (e k).measurable))

@[simp]
lemma kerInterval_zero (κ₀ : Kernel ((l : Iic i) → X l) ((l : Ioc i j) → X l))
    (κ : ∀ k, Kernel ((l : Iic k) → X l) (X (k + 1))) :
    kerInterval κ₀ κ 0 = 0 := rfl

lemma kerInterval_succ {κ₀ : Kernel ((l : Iic i) → X l) ((l : Ioc i j) → X l)}
    {κ : ∀ k, Kernel ((l : Iic k) → X l) (X (k + 1))} (k : ℕ) :
    kerInterval κ₀ κ (k + 1)
      = if h : j = k + 1 then castPath κ₀ h else
        ((kerInterval κ₀ κ k) ⊗ₖ' (Kernel.map (κ k) (e k) (e k).measurable)) := rfl

lemma kerInterval_succ_of_ne {κ₀ : Kernel ((l : Iic i) → X l) ((l : Ioc i j) → X l)}
    {κ : ∀ k, Kernel ((l : Iic k) → X l) (X (k + 1))} (h : j ≠ k + 1) :
    kerInterval κ₀ κ (k + 1) =
      (kerInterval κ₀ κ k) ⊗ₖ' (Kernel.map (κ k) (e k) (e k).measurable) := by
  rw [kerInterval_succ, dif_neg h]

lemma kerInterval_succ_right {κ₀ : Kernel ((l : Iic i) → X l) ((l : Ioc i j) → X l)}
    {κ : ∀ k, Kernel ((l : Iic k) → X l) (X (k + 1))} (h : j ≤ k) :
    kerInterval κ₀ κ (k + 1) =
      (kerInterval κ₀ κ k) ⊗ₖ' (Kernel.map (κ k) (e k) (e k).measurable) := by
  rw [kerInterval_succ, dif_neg (by linarith)]

lemma kerInterval_of_lt {κ₀ : Kernel ((l : Iic i) → X l) ((l : Ioc i j) → X l)}
    {κ : ∀ k, Kernel ((l : Iic k) → X l) (X (k + 1))} (h : k < j) :
    kerInterval κ₀ κ k = 0 := by
  induction k with
  | zero => rfl
  | succ n ih =>
      rw [kerInterval_succ, dif_neg h.ne', ih (by linarith)]
      simp

lemma kerInterval_of_eq (κ₀ : Kernel ((l : Iic i) → X l) ((l : Ioc i j) → X l))
    (κ : ∀ k, Kernel ((l : Iic k) → X l) (X (k + 1))) (hj : 0 < j) :
    kerInterval κ₀ κ j = κ₀ := by
  cases j with
  | zero => exfalso; linarith
  | succ n =>
    rw [kerInterval_succ, dif_pos rfl]
    ext a s hs
    rw [castPath_apply _ _ _ _ hs]
    rfl

instance (κ₀ : Kernel ((l : Iic i) → X l) ((l : Ioc i j) → X l)) [h₀ : IsSFiniteKernel κ₀]
    (κ : ∀ k, Kernel ((l : Iic k) → X l) (X (k + 1))) (k : ℕ) :
    IsSFiniteKernel (kerInterval κ₀ κ k) := by
  induction k with
  | zero => rw [kerInterval_zero]; infer_instance
  | succ n _ => rw [kerInterval_succ]; split_ifs <;> infer_instance

instance (κ₀ : Kernel ((l : Iic i) → X l) ((l : Ioc i j) → X l)) [h₀ : IsFiniteKernel κ₀]
    (κ : ∀ k, Kernel ((l : Iic k) → X l) (X (k + 1)))
    [∀ k, IsFiniteKernel (κ k)] (k : ℕ) :
    IsFiniteKernel (kerInterval κ₀ κ k) := by
  induction k with
  | zero => rw [kerInterval_zero]; infer_instance
  | succ n _ => rw [kerInterval_succ]; split_ifs <;> infer_instance

/-- Consider for each `k` a kernel with variables in `Iic k`, distributed in `X (k+1)`. Given any
`i < j`, one can compose them to get a kernel from `Ici i` to `Ioc i j`. This kernel is called
`kerNat κ i j`. -/
def kerNat (κ : (k : ℕ) → Kernel ((l : Iic k) → X l) (X (k + 1))) (i j : ℕ) :
    Kernel ((l : Iic i) → X l) ((l : Ioc i j) → X l) :=
  if i < j then kerInterval (Kernel.map (κ i) (e i) (e i).measurable) κ j else 0

lemma kerNat_eq (κ : (k : ℕ) → Kernel ((l : Iic k) → X l) (X (k + 1)))
    (hij : i < j) :
    kerNat κ i j = kerInterval (Kernel.map (κ i) (e i) (e i).measurable) κ j :=
  dif_pos hij

lemma kerNat_of_ge (κ : (k : ℕ) → Kernel ((l : Iic k) → X l) (X (k + 1))) (hij : j ≤ i) :
    kerNat κ i j = 0 :=
  dif_neg (not_lt.mpr hij)

instance (κ : (k : ℕ) → Kernel ((l : Iic k) → X l) (X (k + 1))) [∀ i, IsSFiniteKernel (κ i)] :
    IsSFiniteKernel (kerNat κ i j) := by
  rw [kerNat]; split_ifs <;> infer_instance

instance (κ : (k : ℕ) → Kernel ((l : Iic k) → X l) (X (k + 1))) [∀ i, IsFiniteKernel (κ i)] :
    IsFiniteKernel (kerNat κ i j) := by
  rw [kerNat]; split_ifs <;> infer_instance

lemma kerNat_succ (κ : (k : ℕ) → Kernel ((l : Iic k) → X l) (X (k + 1))) (i : ℕ) :
    kerNat κ i (i + 1) = Kernel.map (κ i) (e i) (e i).measurable := by
  rw [kerNat_eq _ (Nat.lt_succ_self _), kerInterval_of_eq _ _ (by linarith)]

lemma kerNat_succ_right (κ : (k : ℕ) → Kernel ((l : Iic k) → X l) (X (k + 1)))
    (i j : ℕ) (hij : i < j) :
    kerNat κ i (j + 1) = (kerNat κ i j) ⊗ₖ' (kerNat κ j (j + 1)) := by
  rw [kerNat_eq _ (hij.trans (Nat.lt_succ_self _)),
    kerInterval_succ_right (Nat.succ_le_iff.mpr hij)]
  congr
  · rw [kerNat_eq _ hij]
  · rw [kerNat_succ κ j]

lemma kerNat_succ_left (κ : (k : ℕ) → Kernel ((l : Iic k) → X l) (X (k + 1)))
    [∀ i, IsSFiniteKernel (κ i)] (i j : ℕ) (hij : i + 1 < j) :
    kerNat κ i j = (kerNat κ i (i + 1)) ⊗ₖ' (kerNat κ (i + 1) j) := by
  induction j with
  | zero =>
    rw [kerNat_of_ge κ (Nat.zero_le _), kerNat_of_ge κ (Nat.zero_le _)]
    simp
  | succ j hj => cases le_or_lt j (i + 1) with
    | inl h =>
      have hj_eq : j = i + 1 := le_antisymm h (Nat.succ_lt_succ_iff.mp (by convert hij))
      rw [kerNat_succ_right]
      · congr
      · rw [hj_eq]; exact Nat.lt_succ_self i
    | inr h =>
      rw [kerNat_succ_right _ _ _ (Nat.succ_lt_succ_iff.mp hij), hj h,
        kerNat_succ_right _ _ j h,
        compProdNat_assoc (kerNat κ i (i + 1)) (kerNat κ (i + 1) j)
          (kerNat κ j (j + 1)) (Nat.lt_succ_self i) h (Nat.lt_succ_self j)]

theorem compProdNat_kerNat (κ : (k : ℕ) → Kernel ((l : Iic k) → X l) (X (k + 1)))
    [∀ i, IsSFiniteKernel (κ i)] (hij : i < j) (hjk : j < k) :
    ((kerNat κ i j) ⊗ₖ' (kerNat κ j k)) = kerNat κ i k := by
  cases k with
  | zero => exfalso; linarith
  | succ k =>
    refine Nat.decreasingInduction' ?_ (Nat.lt_succ_iff.mp hjk) ?_
    · intro l hlk hjl h
      rw [← h, kerNat_succ_left _ l]
      swap; linarith
      rw [kerNat_succ_right _ i _ (hij.trans_le hjl),
        compProdNat_assoc _ _ _ (hij.trans_le hjl) (Nat.lt_succ_self l)]
      linarith
    · rw [kerNat_succ_right _ _ _ (hij.trans_le (Nat.lt_succ_iff.mp hjk))]

theorem isMarkovKernel_compProdNat {i j k : ℕ}
    (κ : Kernel ((l : Iic i) → X l) ((l : Ioc i j) → X l))
    (η : Kernel ((l : Iic j) → X l) ((l : Ioc j k) → X l))
    [IsMarkovKernel κ] [IsMarkovKernel η] (hij : i < j) (hjk : j < k) :
    IsMarkovKernel (κ ⊗ₖ' η) := by
  simp only [compProdNat, hij, hjk, and_self, ↓reduceDIte, split]
  infer_instance

theorem isMarkovKernel_castPath {i j k : ℕ}
    (κ : Kernel ((l : Iic i) → X l) ((l : Ioc i j) → X l)) [IsMarkovKernel κ] (hjk : j = k) :
    IsMarkovKernel (castPath κ hjk) := by
  rw [castPath]; infer_instance

theorem isMarkovKernel_kerInterval {i j k : ℕ}
    (κ₀ : Kernel ((l : Iic i) → X l) ((l : Ioc i j) → X l)) [h₀ : IsMarkovKernel κ₀]
    (κ : ∀ k, Kernel ((l : Iic k) → X l) (X (k + 1))) [∀ k, IsMarkovKernel (κ k)]
    (hij : i < j) (hjk : j ≤ k) :
    IsMarkovKernel (kerInterval κ₀ κ k) := by
  induction k with
  | zero => omega
  | succ n hn =>
    rw [kerInterval_succ]
    split_ifs with h
    · exact isMarkovKernel_castPath _ _
    · have _ := hn (by omega)
      exact isMarkovKernel_compProdNat _ _ (by omega) n.lt_succ_self

theorem isMarkovKernel_kerNat {i j : ℕ}
    (κ : ∀ k, Kernel ((l : Iic k) → X l) (X (k + 1)))
    [∀ k, IsMarkovKernel (κ k)] (hij : i < j) :
    IsMarkovKernel (kerNat κ i j) := by
  simp only [kerNat, hij, ↓reduceIte]
  exact isMarkovKernel_kerInterval _ _ i.lt_succ_self (Nat.succ_le.2 hij)

theorem kerNat_proj (κ : (k : ℕ) → Kernel ((l : Iic k) → X l) (X (k + 1)))
    [∀ i, IsMarkovKernel (κ i)] {a b c : ℕ} (hab : a < b) (hbc : b ≤ c) :
    Kernel.map (kerNat κ a c) (fproj₂ (Ioc_subset_Ioc_right hbc)) (measurable_fproj₂ _) =
      kerNat κ a b := by
  rcases eq_or_lt_of_le hbc with rfl | hbc
  · exact Kernel.map_id _
  · ext x s ms
    rw [Kernel.map_apply' _ _ _ ms, ← compProdNat_kerNat κ hab hbc,
      compProdNat_apply' _ _ hab hbc _ (measurable_fproj₂ _ ms), ← one_mul (kerNat κ a b x s),
      ← lintegral_indicator_const ms]
    congr with y
    by_cases hy : y ∈ s <;> simp only [Set.mem_preimage, Set.indicator, hy, ↓reduceIte]
    · have := isMarkovKernel_kerNat κ hbc
      convert measure_univ
      · ext z
        simpa only [Set.mem_setOf_eq, Set.mem_univ, iff_true, fproj₂_er] using hy
      · infer_instance
    · convert measure_empty
      · ext z
        simpa [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, fproj₂_er] using hy
      · infer_instance

end kerNat

end Kernel
end ProbabilityTheory

end compProdNat

section partialKernel

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
variable (κ : (n : ℕ) → Kernel ((i : Iic n) → X i) (X (n + 1)))

namespace ProbabilityTheory
namespace Kernel

/-- Given a family of kernels `κ : (n : ℕ) → Kernel ((i : Iic n) → X i) (X (n + 1))`, we can
compose them : if `a < b`, then `(κ a) ⊗ₖ ... ⊗ₖ (κ (b - 1))` is a kernel from
`(i : Iic a) → X i` to `(i : Ioc a b) → X i`. This composition is called `kerNat κ a b`.

In order to make manipulations easier, we define
`partialKernel κ a b : Kernel ((i : Iic a) → X i) ((i : Iic b) → X i)`. Given the trajectory up to
time `a`, `partialKernel κ a b` gives the distribution of the trajectory up to time `b`. It is
the product of a Dirac mass along the trajectory, up to `a`, with `kerNat κ a b`. -/
noncomputable def partialKernel (a b : ℕ) : Kernel ((i : Iic a) → X i) ((i : Iic b) → X i) :=
  if hab : a < b
    then ((Kernel.deterministic id measurable_id) ×ₖ kerNat κ a b).map
      (el a b hab.le) (el a b hab.le).measurable
    else Kernel.deterministic (fprojNat_le (not_lt.1 hab)) (measurable_fprojNat_le _)

theorem partialKernel_lt {a b : ℕ} (hab : a < b) :
    partialKernel κ a b =
      ((Kernel.deterministic id measurable_id) ×ₖ kerNat κ a b).map
        (el a b hab.le) (el a b hab.le).measurable := by
  rw [partialKernel, dif_pos hab]

theorem partialKernel_le {a b : ℕ} (hab : b ≤ a) :
    partialKernel κ a b =
      Kernel.deterministic (fprojNat_le hab) (measurable_fprojNat_le _) := by
  rw [partialKernel, dif_neg (not_lt.2 hab)]

variable [∀ n, IsMarkovKernel (κ n)]

instance (a b : ℕ) : IsMarkovKernel (partialKernel κ a b) := by
  rw [partialKernel]
  split_ifs with hab
  · have := isMarkovKernel_kerNat κ hab
    infer_instance
  · infer_instance

/-- If `b ≤ c`, then projecting the trajectory up to time `c` on first coordinates gives the
trajectory up to time `b`. -/
theorem partialKernel_proj (a : ℕ) {b c : ℕ} (hbc : b ≤ c) :
    (partialKernel κ a c).map (fprojNat_le hbc) (measurable_fprojNat_le _) =
      partialKernel κ a b := by
  unfold partialKernel
  split_ifs with h1 h2 h3
  · have : (fprojNat_le (X := X) hbc) ∘ (el a c h1.le) =
        (el a b h2.le) ∘ (Prod.map id (fproj₂ (Ioc_subset_Ioc_right hbc))) := by
      ext x i
      simp [el]
    rw [Kernel.map_map, Kernel.map_eq _ _ this, ← Kernel.map_map, Kernel.map_prod, Kernel.map_id,
      kerNat_proj _ h2 hbc]
  · have : (fprojNat_le (X := X) hbc) ∘ (el a c h1.le) =
        (fprojNat_le (not_lt.1 h2)) ∘ Prod.fst := by
      ext x i
      simp [el, fprojNat_le, fproj₂, (mem_Iic.1 i.2).trans (not_lt.1 h2)]
    have _ := isMarkovKernel_kerNat κ h1
    rw [Kernel.map_map, Kernel.map_eq _ _ this, ← Kernel.map_map _ _ (measurable_fprojNat_le _),
      Kernel.map_prod_fst, Kernel.map_deterministic]
    rfl
  · omega
  · rw [Kernel.map_deterministic]
    rfl

/-- Given the trajectory up to time `a`, first computing the distribution up to time `b`
and then the distribution up to time `c` is the same as directly computing the distribution up
to time `c`. -/
theorem partialKernel_comp (c : ℕ) {a b : ℕ} (h : a ≤ b) :
    (partialKernel κ b c) ∘ₖ (partialKernel κ a b) = partialKernel κ a c := by
  by_cases hab : a < b <;> by_cases hbc : b < c <;> by_cases hac : a < c <;> try omega
  · ext x s ms
    rw [partialKernel_lt κ hab, partialKernel_lt κ hbc, partialKernel_lt κ hac,
      Kernel.comp_apply' _ _ _ ms, Kernel.lintegral_map, Kernel.lintegral_prod,
      Kernel.map_apply' _ _ _ ms, Kernel.prod_apply', Kernel.lintegral_deterministic',
      Kernel.lintegral_deterministic', ← compProdNat_kerNat κ hab hbc,
      compProdNat_apply' _ _ hab hbc]
    · congr with y
      rw [Kernel.map_apply' _ _ _ ms, Kernel.prod_apply', Kernel.lintegral_deterministic']
      · congr with z
        simp only [el, id_eq, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, Set.mem_preimage,
          Set.mem_setOf_eq, er, Set.preimage_setOf_eq]
        congrm (fun i ↦ ?_) ∈ s
        split_ifs <;> try rfl
        omega
      · exact measurable_measure_prod_mk_left ((el b c hbc.le).measurable ms)
      · exact (el b c hbc.le).measurable ms
    · exact measurable_prod_mk_left ((el a c hac.le).measurable ms)
    · exact measurable_measure_prod_mk_left ((el a c hac.le).measurable ms)
    · apply Measurable.lintegral_prod_right' (f := fun x ↦ (Kernel.map _ _ _) _ _)
      exact (Kernel.measurable_coe _ ms).comp (el a b hab.le).measurable
    · exact (el a c hac.le).measurable ms
    · exact (Kernel.measurable_coe _ ms).comp (el a b hab.le).measurable
    · exact Kernel.measurable_coe _ ms
  · rw [partialKernel_le κ (not_lt.1 hbc), Kernel.deterministic_comp_eq_map,
      partialKernel_proj κ a (not_lt.1 hbc)]
  · rw [partialKernel_le κ (not_lt.1 hbc), Kernel.deterministic_comp_eq_map,
      partialKernel_proj κ a (not_lt.1 hbc)]
  · have : a = b := by omega
    cases this
    rw [partialKernel_le κ (le_refl a), Kernel.comp_deterministic_eq_comap]
    convert Kernel.comap_id (partialKernel κ a c)
  · rw [partialKernel_le κ (not_lt.1 hbc), Kernel.deterministic_comp_eq_map,
      partialKernel_proj κ a (not_lt.1 hbc)]

/-- Given the trajectory up to time `a`, first computing the distribution up to time `b`
and then the distribution up to time `c` is the same as directly computing the distribution up
to time `c`. -/
theorem partialKernel_comp' (a : ℕ) {b c : ℕ} (h : c ≤ b) :
    (partialKernel κ b c) ∘ₖ (partialKernel κ a b) = partialKernel κ a c := by
  by_cases a < b <;> by_cases hbc : b < c <;> by_cases a < c <;>
    try rw [partialKernel_le κ (not_lt.1 hbc), Kernel.deterministic_comp_eq_map,
      partialKernel_proj κ a (not_lt.1 hbc)]
  all_goals omega

end Kernel
end ProbabilityTheory
