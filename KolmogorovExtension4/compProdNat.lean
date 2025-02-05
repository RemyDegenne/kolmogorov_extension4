/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Etienne Marion
-/
import KolmogorovExtension4.Annexe
import KolmogorovExtension4.DependsOn

open Finset ENNReal ProbabilityTheory MeasureTheory Function Preorder

noncomputable section

section compProdNat

lemma measurable_cast {X Y : Type u} [mX : MeasurableSpace X] [mY : MeasurableSpace Y] (h : X = Y)
    (hm : HEq mX mY) : Measurable (cast h) := by
  subst h
  subst hm
  exact measurable_id

lemma measurable_eqRec {X Y : Type u} [mX : MeasurableSpace X] [mY : MeasurableSpace Y] (h : X = Y)
    (hm : HEq mX mY) : Measurable (fun x : X ↦ h ▸ x) := by
  subst h
  subst hm
  exact measurable_id

variable {X : ℕ → Type*}

theorem update_updateFinset_eq (x z : (n : ℕ) → X n) {m : ℕ} :
    update (updateFinset x (Iic m) (frestrictLe m z)) (m + 1) (z (m + 1)) =
    updateFinset x (Iic (m + 1)) (frestrictLe (m + 1) z) := by
  ext i
  simp only [update, updateFinset, mem_Iic, dite_eq_ite]
  split_ifs with h <;> try omega
  cases h
  all_goals rfl

variable [∀ i, MeasurableSpace (X i)]

section equivs

/-- Identifying `{n + 1}` with `Ioc n (n+1)`, as a measurable equiv on dependent functions. -/
def e (n : ℕ) : (X (n + 1)) ≃ᵐ ((i : Ioc n (n + 1)) → X i) where
  toFun := fun x i ↦ (mem_Ioc_succ.1 i.2).symm ▸ x
  invFun := fun x ↦ x ⟨n + 1, right_mem_Ioc.2 n.lt_succ_self⟩
  left_inv := fun x ↦ by simp
  right_inv := fun x ↦ funext fun i ↦ by cases mem_Ioc_succ' i; rfl
  measurable_toFun := by
    simp_rw [eqRec_eq_cast]
    refine measurable_pi_lambda _ (fun i ↦ measurable_cast _ ?_)
    cases mem_Ioc_succ' i; rfl
  measurable_invFun := measurable_pi_apply _

instance subsingleton_subtype {α : Type*} (a : α) : Subsingleton ({a} : Finset α) where
  allEq x y := by
    rw [← Subtype.coe_inj, Finset.eq_of_mem_singleton x.2, Finset.eq_of_mem_singleton y.2]

lemma MeasureTheory.Measure.map_e (μ : (n : ℕ) → Measure (X n)) [∀ n, SigmaFinite (μ n)] (n : ℕ) :
    Measure.pi (fun i : Ioc n (n + 1) ↦ μ i) = (μ (n + 1)).map (e n) := by
  refine Measure.pi_eq fun s hs ↦ ?_
  have : Subsingleton (Ioc n (n + 1)) := by
    rw [Nat.Ioc_succ_singleton]
    infer_instance
  rw [Fintype.prod_subsingleton _ ⟨n + 1, mem_Ioc_succ.2 rfl⟩, Measure.map_apply]
  · congr with x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const, Subtype.forall,
      Nat.Ioc_succ_singleton, mem_singleton]
    exact ⟨fun h ↦ h (n + 1) rfl, fun h a b ↦ b.symm ▸ h⟩
  · exact (e n).measurable
  · exact MeasurableSet.univ_pi hs

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
  right_inv := fun p ↦ funext fun i ↦ by
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

lemma frestrictLe₂_comp_el (a b : ℕ) (hab : a ≤ b) :
    (frestrictLe₂ hab) ∘ (el (X := X) a b hab) = Prod.fst := by
  ext x i
  simp [el, mem_Iic.1 i.2]

lemma el_self (a : ℕ) : ⇑(el (X := X) a a le_rfl) = Prod.fst := by
  ext x i
  simp [el, mem_Iic.1 i.2]

/-- The union of `Iic n` and `Ioi n` is the whole `ℕ`, version as a measurable equivalence
on dependent functions. -/
def el' (n : ℕ) : (((i : Iic n) → X i) × ((i : Set.Ioi n) → X i)) ≃ᵐ ((n : ℕ) → X n) :=
  { toFun := fun p i ↦ if hi : i ≤ n
      then p.1 ⟨i, mem_Iic.2 hi⟩
      else p.2 ⟨i, Set.mem_Ioi.2 (not_le.1 hi)⟩
    invFun := fun x ↦ (fun i ↦ x i, fun i ↦ x i)
    left_inv := fun p ↦ by
      ext i
      · simp [mem_Iic.1 i.2]
      · simp [not_le.2 <| Set.mem_Ioi.1 i.2]
    right_inv := fun x ↦ by simp
    measurable_toFun := by
      refine measurable_pi_lambda _ (fun i ↦ ?_)
      by_cases hi : i ≤ n <;> simp only [Equiv.coe_fn_mk, hi, ↓reduceDIte]
      · exact measurable_fst.eval
      · exact measurable_snd.eval
    measurable_invFun := Measurable.prod_mk (measurable_restrict _) (Set.measurable_restrict _) }

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

theorem restrict₂_er (i j k : ℕ) (hij : i < j) (hjk : j ≤ k)
    (y : (n : Ioc i j) → X n) (z : (n : Ioc j k) → X n) :
    restrict₂ (Ioc_subset_Ioc_right hjk) (er i j k hij hjk (y, z)) = y := by
  ext n
  simp [er, (mem_Ioc.1 n.2).2]

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
    then (κ ⊗ₖ split i j k h.1 η).map (er i j k h.1 h.2.le)
    else 0

lemma compProdNat_eq {i j k : ℕ} (κ : Kernel ((l : Iic i) → X l) ((l : Ioc i j) → X l))
    (η : Kernel ((l : Iic j) → X l) ((l : Ioc j k) → X l)) (hij : i < j) (hjk : j < k) :
    compProdNat κ η = (κ ⊗ₖ split i j k hij η).map (er i j k hij hjk.le) := by
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
    Kernel.compProd_apply ((er _ _ _ _ _).measurable hs)]
  · simp_rw [split, Kernel.comap_apply]
  · exact (er ..).measurable

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
  simp_rw [Kernel.map_apply' _ (er ..).measurable _ (this _)]
  have : ∀ b, MeasurableSet
      (er j k l hjk hkl.le ⁻¹' {c | (b, c) ∈ er i j l hij (hjk.trans hkl).le ⁻¹' s}) :=
    fun b ↦ (er _ _ _ _ _).measurable (this b)
  simp_rw [compProd_apply (this _), split, Kernel.comap_apply]
  rw [lintegral_compProd]
  swap; exact h_meas_comp.comp (er i j k hij hjk.le).measurable
  simp only [comap_apply, el_assoc, Set.mem_preimage, Set.preimage_setOf_eq, Set.mem_setOf_eq,
    er_assoc]
  simp_rw [el_assoc hij hjk.le]
  exact (er ..).measurable

/-- Given a kernel taking values in `Ioc i j`, convert it to a kernel taking values
in `Ioc i k` when `j = k`. -/
def castPath {i j k : ℕ} (κ : Kernel ((l : Iic i) → X l) ((l : Ioc i j) → X l)) (h : j = k) :
    Kernel ((l : Iic i) → X l) ((l : Ioc i k) → X l) :=
  κ.map (e_path_eq h)

theorem castPath_self {i j : ℕ} (κ : Kernel ((l : Iic i) → X l) ((l : Ioc i j) → X l)) :
    castPath κ (rfl : j = j) = κ := by
  simp only [castPath, e_path_eq]
  conv_lhs => enter [2]; change id
  simp

lemma castPath_apply {i j k : ℕ} (κ : Kernel ((l : Iic i) → X l) ((l : Ioc i j) → X l)) (h : j = k)
    (a : (l : Iic i) → X l) (s : Set ((l : Ioc i k) → X l)) (hs : MeasurableSet s) :
    castPath κ h a s = κ a (e_path_eq h ⁻¹' s) := by
  rw [castPath, Kernel.map_apply' _ (e_path_eq h).measurable _ hs]

instance {i j k : ℕ} (κ : Kernel ((l : Iic i) → X l) ((l : Ioc i j) → X l)) (h : j = k)
    [IsSFiniteKernel κ] :
    IsSFiniteKernel (castPath κ h) := by
  rw [castPath]; infer_instance

instance {i j k : ℕ} (κ : Kernel ((l : Iic i) → X l) ((l : Ioc i j) → X l)) (h : j = k)
    [IsFiniteKernel κ] :
    IsFiniteKernel (castPath κ h) := by
  rw [castPath]; infer_instance

instance {i j k : ℕ}
    (κ : Kernel ((l : Iic i) → X l) ((l : Ioc i j) → X l)) [IsMarkovKernel κ] (hjk : j = k) :
    IsMarkovKernel (castPath κ hjk) := IsMarkovKernel.map _ (e_path_eq hjk).measurable

section kerNat

variable {i j k : ℕ}

/-- Given a family of kernels `κ k` from `X 0 × ... × X k` to `X (k + 1)` for all `k`,
construct a kernel from `X 0 × ... × X i` to `X (i + 1) × ... × X j` by iterating `κ`. -/
def ptraj (κ : (k : ℕ) → Kernel ((l : Iic k) → X l) (X (k + 1))) (i j : ℕ) :
    Kernel ((l : Iic i) → X l) ((l : Iic j) → X l) := by
  induction j with
  | zero => exact deterministic (frestrictLe₂ (zero_le i)) (measurable_frestrictLe₂ _)
  | succ k κ_k =>
    exact if h : k + 1 ≤ i
      then deterministic (frestrictLe₂ h) (measurable_frestrictLe₂ h)
      else ((Kernel.id ×ₖ ((κ k).map (e k))) ∘ₖ κ_k).map (el k (k + 1) k.le_succ)
    -- exact if h : i = k then h ▸ (κ i).map (e i)
    -- else (κ_k ⊗ₖ split i j k h.1 η).map (er i j k h.1 h.2.le)
    -- (κ_k ⊗ₖ' ((κ k).map (e k)))

-- lemma kerNat_zero (κ : (k : ℕ) → Kernel ((l : Iic k) → X l) (X (k + 1))) (i : ℕ) :
--     kerNat κ i 0 = 0 := rfl

-- lemma kerNat_succ (κ : (k : ℕ) → Kernel ((l : Iic k) → X l) (X (k + 1))) (i j : ℕ) :
--     kerNat κ i (j + 1) =
--       if h : i = j then castPath ((κ i).map (e i)) (h ▸ rfl)
--         else (kerNat κ i j) ⊗ₖ' ((κ j).map (e j)) := rfl

-- lemma kerNat_succ_self (κ : (k : ℕ) → Kernel ((l : Iic k) → X l) (X (k + 1))) (i : ℕ) :
--     kerNat κ i (i + 1) = (κ i).map (e i) := by
--   rw [kerNat_succ, dif_pos rfl, castPath_self]

-- lemma kerNat_succ_of_ne (κ : (k : ℕ) → Kernel ((l : Iic k) → X l) (X (k + 1))) (h : i ≠ j) :
--     kerNat κ i (j + 1) = (kerNat κ i j) ⊗ₖ' ((κ j).map (e j)) := by
--   rw [kerNat_succ, dif_neg h]

-- lemma kerNat_succ_right (κ : (k : ℕ) → Kernel ((l : Iic k) → X l) (X (k + 1)))
--     (i j : ℕ) (hij : i < j) :
--     kerNat κ i (j + 1) = (kerNat κ i j) ⊗ₖ' (kerNat κ j (j + 1)) := by
--   rw [kerNat_succ_of_ne κ hij.ne, kerNat_succ_self]

-- lemma kerNat_of_ge (κ : (k : ℕ) → Kernel ((l : Iic k) → X l) (X (k + 1))) (h : j ≤ i) :
--     kerNat κ i j = 0 := by
--   induction j with
--   | zero => rfl
--   | succ n ih =>
--       rw [kerNat_succ, dif_neg (by omega), ih (by omega)]
--       simp

-- instance (κ : (k : ℕ) → Kernel ((l : Iic k) → X l) (X (k + 1))) [∀ i, IsSFiniteKernel (κ i)] :
--     IsSFiniteKernel (kerNat κ i j) := by
--   induction j with
--   | zero => rw [kerNat_zero]; infer_instance
--   | succ k _ => rw [kerNat_succ]; split_ifs <;> infer_instance

-- instance (κ : (k : ℕ) → Kernel ((l : Iic k) → X l) (X (k + 1))) [∀ i, IsFiniteKernel (κ i)] :
--     IsFiniteKernel (kerNat κ i j) := by
--   induction j with
--   | zero => rw [kerNat_zero]; infer_instance
--   | succ k _ => rw [kerNat_succ]; split_ifs <;> infer_instance

-- lemma kerNat_succ_left (κ : (k : ℕ) → Kernel ((l : Iic k) → X l) (X (k + 1)))
--     [∀ i, IsSFiniteKernel (κ i)] (i j : ℕ) (hij : i + 1 < j) :
--     kerNat κ i j = (kerNat κ i (i + 1)) ⊗ₖ' (kerNat κ (i + 1) j) := by
--   induction j with
--   | zero =>
--     rw [kerNat_of_ge κ (Nat.zero_le _), kerNat_of_ge κ (Nat.zero_le _)]
--     simp
--   | succ j hj => cases le_or_lt j (i + 1) with
--     | inl h =>
--       have hj_eq : j = i + 1 := le_antisymm h (Nat.succ_lt_succ_iff.mp (by convert hij))
--       rw [kerNat_succ_right]
--       · congr
--       · rw [hj_eq]; exact Nat.lt_succ_self i
--     | inr h =>
--       rw [kerNat_succ_right _ _ _ (Nat.succ_lt_succ_iff.mp hij), hj h,
--         kerNat_succ_right _ _ j h,
--         compProdNat_assoc (kerNat κ i (i + 1)) (kerNat κ (i + 1) j)
--           (kerNat κ j (j + 1)) (Nat.lt_succ_self i) h (Nat.lt_succ_self j)]

-- theorem compProdNat_kerNat (κ : (k : ℕ) → Kernel ((l : Iic k) → X l) (X (k + 1)))
--     [∀ i, IsSFiniteKernel (κ i)] (hij : i < j) (hjk : j < k) :
--     ((kerNat κ i j) ⊗ₖ' (kerNat κ j k)) = kerNat κ i k := by
--   cases k with
--   | zero => exfalso; linarith
--   | succ k =>
--     refine Nat.decreasingInduction' ?_ (Nat.lt_succ_iff.mp hjk) ?_
--     · intro l hlk hjl h
--       rw [← h, kerNat_succ_left _ l]
--       swap; linarith
--       rw [kerNat_succ_right _ i _ (hij.trans_le hjl),
--         compProdNat_assoc _ _ _ (hij.trans_le hjl) (Nat.lt_succ_self l)]
--       linarith
--     · rw [kerNat_succ_right _ _ _ (hij.trans_le (Nat.lt_succ_iff.mp hjk))]

-- theorem isMarkovKernel_compProdNat {i j k : ℕ}
--     (κ : Kernel ((l : Iic i) → X l) ((l : Ioc i j) → X l))
--     (η : Kernel ((l : Iic j) → X l) ((l : Ioc j k) → X l))
--     [IsMarkovKernel κ] [IsMarkovKernel η] (hij : i < j) (hjk : j < k) :
--     IsMarkovKernel (κ ⊗ₖ' η) := by
--   simp only [compProdNat, hij, hjk, and_self, ↓reduceDIte, split]
--   exact IsMarkovKernel.map _ (er ..).measurable

-- theorem isMarkovKernel_kerNat {i j : ℕ}
--     (κ : ∀ k, Kernel ((l : Iic k) → X l) (X (k + 1)))
--     [∀ k, IsMarkovKernel (κ k)] (hij : i < j) :
--     IsMarkovKernel (kerNat κ i j) := by
--   induction j with
--   | zero => omega
--   |succ k hk =>
--     rw [kerNat_succ]
--     split_ifs with h
--     · have := IsMarkovKernel.map (κ i) (e i).measurable
--       infer_instance
--     · have _ := hk (by omega)
--       have := IsMarkovKernel.map (κ k) (e k).measurable
--       exact isMarkovKernel_compProdNat _ _ (by omega) k.lt_succ_self

-- theorem kerNat_proj (κ : (k : ℕ) → Kernel ((l : Iic k) → X l) (X (k + 1)))
--     [∀ i, IsMarkovKernel (κ i)] {a b c : ℕ} (hab : a < b) (hbc : b ≤ c) :
--     Kernel.map (kerNat κ a c) (restrict₂ (Ioc_subset_Ioc_right hbc)) =
--       kerNat κ a b := by
--   rcases eq_or_lt_of_le hbc with rfl | hbc
--   · exact Kernel.map_id _
--   · ext x s ms
--     rw [Kernel.map_apply' _ (measurable_restrict₂ _) _ ms, ← compProdNat_kerNat κ hab hbc,
--       compProdNat_apply' _ _ hab hbc _ (measurable_restrict₂ _ ms), ← one_mul (kerNat κ a b x s),
--       ← lintegral_indicator_const ms]
--     congr with y
--     by_cases hy : y ∈ s <;> simp only [Set.mem_preimage, Set.indicator, hy, ↓reduceIte]
--     · have := isMarkovKernel_kerNat κ hbc
--       convert measure_univ
--       · ext z
--         simpa only [Set.mem_setOf_eq, Set.mem_univ, iff_true, restrict₂_er] using hy
--       · infer_instance
--     · convert measure_empty
--       · ext z
--         simpa [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, restrict₂_er] using hy
--       · infer_instance

end kerNat

end Kernel
end ProbabilityTheory

end compProdNat

section ptraj

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
variable (κ : (n : ℕ) → Kernel ((i : Iic n) → X i) (X (n + 1)))

namespace ProbabilityTheory
namespace Kernel

section Basic

-- /-- Given a family of kernels `κ : (n : ℕ) → Kernel ((i : Iic n) → X i) (X (n + 1))`, we can
-- compose them: if `a < b`, then `(κ a) ⊗ₖ ... ⊗ₖ (κ (b - 1))` is a kernel from
-- `(i : Iic a) → X i` to `(i : Ioc a b) → X i`. This composition is called `kerNat κ a b`.

-- In order to make manipulations easier, we define
-- `ptraj κ a b : Kernel ((i : Iic a) → X i) ((i : Iic b) → X i)`. Given the trajectory up to
-- time `a`, `ptraj κ a b` gives the distribution of the trajectory up to time `b`. It is
-- the product of a Dirac mass along the trajectory, up to `a`, with `kerNat κ a b`. -/
-- -- noncomputable def ptraj (a b : ℕ) : Kernel ((i : Iic a) → X i) ((i : Iic b) → X i) :=
-- --   if hab : a < b
-- --     then (Kernel.id ×ₖ kerNat κ a b).map (el a b hab.le)
-- --     else deterministic (frestrictLe₂ (not_lt.1 hab)) (measurable_frestrictLe₂ _)

-- -- theorem ptraj_lt {a b : ℕ} (hab : a < b) :
-- --     ptraj κ a b = (Kernel.id ×ₖ kerNat κ a b).map (el a b hab.le) := by
-- --   rw [ptraj, dif_pos hab]

variable {κ}

lemma ptraj_succ_eq (a b : ℕ) :
    ptraj κ a (b + 1) =
    if hab : b + 1 ≤ a
      then deterministic (frestrictLe₂ hab) (measurable_frestrictLe₂ hab)
      else ((Kernel.id ×ₖ ((κ b).map (e b))) ∘ₖ ptraj κ a b).map (el b (b + 1) b.le_succ) := rfl

lemma ptraj_le {a b : ℕ} (hab : b ≤ a) :
    ptraj κ a b = deterministic (frestrictLe₂ hab) (measurable_frestrictLe₂ _) := by
  induction b with
  | zero => rfl
  | succ k hk => rw [ptraj_succ_eq, dif_pos hab]

lemma ptraj_zero (a : ℕ) :
    ptraj κ a 0 = deterministic (frestrictLe₂ (zero_le a)) (measurable_frestrictLe₂ _) := by
  rw [ptraj_le (zero_le a)]

instance [∀ n, IsSFiniteKernel (κ n)] (a b : ℕ) : IsSFiniteKernel (ptraj κ a b) := by
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

instance [∀ n, IsMarkovKernel (κ n)] (a b : ℕ) : IsMarkovKernel (ptraj κ a b) := by
  induction b with
  | zero => rw [ptraj_zero]; infer_instance
  | succ k hk =>
    rw [ptraj_succ_eq]
    split_ifs with hab
    · infer_instance
    · have := IsMarkovKernel.map (κ k) (e k).measurable
      exact IsMarkovKernel.map _ (el ..).measurable

@[simp]
lemma ptraj_self (a : ℕ) : ptraj κ a a = Kernel.id := by
  rw [ptraj_le le_rfl]
  rfl

lemma ptraj_succ {a b : ℕ} (hab : a ≤ b) : ptraj κ a (b + 1) =
    ((Kernel.id ×ₖ ((κ b).map (e b))) ∘ₖ (ptraj κ a b)).map (el b (b + 1) b.le_succ) := by
  rw [ptraj_succ_eq, dif_neg (by omega)]

lemma ptraj_self_succ (a : ℕ) : ptraj κ a (a + 1) =
    (Kernel.id ×ₖ ((κ a).map (e a))).map (el a (a + 1) a.le_succ) := by
  rw [ptraj_succ le_rfl, ptraj_self, comp_id]

theorem ptraj_succ' {a b : ℕ} (hab : a ≤ b) :
    ptraj κ a (b + 1) = ptraj κ b (b + 1) ∘ₖ ptraj κ a b := by
  induction b with
  | zero => rw [le_zero_iff.1 hab, ptraj_self, comp_id]
  | succ k hk =>
    rw [ptraj_self_succ, ← map_comp, ptraj_succ hab]

theorem ptraj_comp [∀ n, IsSFiniteKernel (κ n)] {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    ptraj κ b c ∘ₖ ptraj κ a b = ptraj κ a c := by
  induction c, hbc using Nat.le_induction with
  | base => simp
  | succ k h hk => rw [ptraj_succ' h, comp_assoc, hk, ← ptraj_succ' (hab.trans h)]

lemma ptraj_proj_succ [∀ n, IsMarkovKernel (κ n)] (a b : ℕ) :
    (ptraj κ a (b + 1)).map (frestrictLe₂ b.le_succ) = ptraj κ a b := by
  obtain hab | hba := le_or_lt a b
  · have := IsMarkovKernel.map (κ b) (e b).measurable
    rw [ptraj_succ' hab, map_comp, ptraj_self_succ, map_map, frestrictLe₂_comp_el, ← fst_eq,
      fst_prod, id_comp]
    any_goals fun_prop
  · rw [ptraj_le (Nat.succ_le.2 hba), ptraj_le hba.le, map_deterministic]
    · rfl
    · fun_prop

lemma ptraj_proj [∀ n, IsMarkovKernel (κ n)] (a : ℕ) {b c : ℕ} (hbc : b ≤ c) :
    (ptraj κ a c).map (frestrictLe₂ hbc) = ptraj κ a b := by
  induction c, hbc using Nat.le_induction with
  | base => convert map_id ..
  | succ k h hk =>
    rw [← hk, ← frestrictLe₂_comp_frestrictLe₂ h k.le_succ, ← map_map, ptraj_proj_succ]
    any_goals fun_prop

theorem ptraj_comp' [∀ n, IsMarkovKernel (κ n)] {a b : ℕ} (c : ℕ) (hab : a ≤ b) :
    ptraj κ b c ∘ₖ ptraj κ a b = ptraj κ a c := by
  obtain hbc | hcb := le_total b c
  · rw [ptraj_comp hab hbc]
  · rw [ptraj_le hcb, deterministic_comp_eq_map, ptraj_proj]

theorem ptraj_comp'' [∀ n, IsMarkovKernel (κ n)] (a : ℕ) {b c : ℕ} (hcb : c ≤ b) :
    ptraj κ b c ∘ₖ ptraj κ a b = ptraj κ a c := by
  rw [ptraj_le hcb, deterministic_comp_eq_map, ptraj_proj]

theorem ptraj_lt_eq_prod [∀ n, IsSFiniteKernel (κ n)] {a b : ℕ} (hab : a ≤ b) :
    ptraj κ a b =
      (Kernel.id ×ₖ (ptraj κ a b).map (restrict₂ Ioc_subset_Iic_self)).map (el a b hab) := by
  induction b, hab using Nat.le_induction with
  | base =>
    ext1 x
    rw [ptraj_self, id_map, map_apply, prod_apply, el_self, ← Measure.fst, Measure.fst_prod]
    any_goals fun_prop
  | succ k h hk =>
    rw [← ptraj_comp h k.le_succ, hk]
    ext x s ms
    rw [comp_apply, map_apply, prod_apply, map_apply, map_apply, prod_apply, map_apply, comp_apply,
      map_apply, prod_apply, map_apply, Measure.bind_apply, MeasureTheory.lintegral_map,
      MeasureTheory.lintegral_prod, lintegral_id, MeasureTheory.lintegral_map,
      Measure.map_apply, @Measure.prod_apply _ _ _ _ _ _ ?_, lintegral_id, Measure.map_apply,
      Measure.bind_apply, MeasureTheory.lintegral_map, MeasureTheory.lintegral_prod, lintegral_id,
      MeasureTheory.lintegral_map]
    · congr with y
      rw [ptraj_self_succ, map_apply', prod_apply', lintegral_id, map_apply', map_apply',
        prod_apply', lintegral_id, map_apply']
      · congr
        ext z
        simp only [e, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, el, restrict₂, Set.mem_preimage,
          Set.preimage_setOf_eq, Set.mem_setOf_eq, subset_refl, Set.coe_inclusion]
        congrm (fun i ↦ ?_) ∈ s
        split_ifs with h1 h2 h3 <;> try rfl
        omega
      any_goals fun_prop
      any_goals try exact ms.preimage (by fun_prop)
      · change Measurable fun b ↦ (κ k).map _ _ (Prod.mk b ⁻¹' _)
        conv =>
          enter [1]
          ext b
          rw [← Measure.map_apply measurable_prod_mk_left]
          rfl
          exact ms.preimage (by fun_prop)
        apply Measure.measurable_measure.1 Measurable.map_prod_mk_left
        exact ms.preimage (by fun_prop)
      · change Measurable fun b ↦ (κ k).map _ _ (Prod.mk b ⁻¹' _)
        conv =>
          enter [1]
          ext b
          rw [← Measure.map_apply measurable_prod_mk_left]
          rfl
          exact (el ..).measurable ms
        apply Measure.measurable_measure.1 Measurable.map_prod_mk_left
        exact (el ..).measurable ms
      · exact (el ..).measurable ms
    any_goals fun_prop
    any_goals try exact ms.preimage (by fun_prop)
    · refine (Kernel.measurable_coe _ ?_).comp ?_
      · exact ms.preimage (by fun_prop)
      · fun_prop
    · apply Measurable.lintegral_prod_right' (f := fun z ↦ (ptraj _ _ _) (el _ _ _ z) _)
      refine (Kernel.measurable_coe _ ?_).comp ?_
      · exact ms.preimage (by fun_prop)
      · fun_prop
    · apply Measurable.aemeasurable
      refine (Kernel.measurable_coe _ ?_).comp ?_
      · exact ms.preimage (by fun_prop)
      · fun_prop
    · refine (Kernel.measurable_coe _ ?_).comp ?_
      · exact ms.preimage (by fun_prop)
      · fun_prop
    · exact Kernel.measurable _
    · simp_rw [← Measure.map_apply measurable_prod_mk_left (ms.preimage (el ..).measurable)]
      apply Measure.measurable_measure.1
      · apply @Measurable.map_prod_mk_left _ _ _ _ _ ?_
        apply @Measure.instSFiniteMap _ _ _ _ _ _ ?_
        apply MeasureTheory.Measure.instSFiniteBindCoeKernelOfIsSFiniteKernel


end Basic

section integral

/-- This function computes the integral of a function `f` against `ptraj`,
and allows to view it as a function depending on all the variables. -/
noncomputable def lmarginalPTraj (a b : ℕ) (f : ((n : ℕ) → X n) → ℝ≥0∞)
    (x : (n : ℕ) → X n) : ℝ≥0∞ :=
  ∫⁻ z : (i : Iic b) → X i, f (updateFinset x _ z) ∂(ptraj κ a b (frestrictLe a x))

/-- If `b ≤ a`, then integrating `f` against the `ptraj κ a b` does nothing. -/
theorem lmarginalPTraj_le {a b : ℕ} (hba : b ≤ a)
    {f : ((n : ℕ) → X n) → ℝ≥0∞} (mf : Measurable f) : lmarginalPTraj κ a b f = f := by
  ext x
  rw [lmarginalPTraj, ptraj_le hba, Kernel.lintegral_deterministic']
  · congr with i
    simp [updateFinset]
  · exact mf.comp measurable_updateFinset

theorem lmarginalPTraj_mono (a b : ℕ) {f g : ((n : ℕ) → X n) → ℝ≥0∞} (hfg : f ≤ g)
    (x : (n : ℕ) → X n) : lmarginalPTraj κ a b f x ≤ lmarginalPTraj κ a b g x :=
  lintegral_mono fun _ ↦ hfg _

/-- If `a < b`, then integrating `f` against the `ptraj κ a b` is the same as integrating
  against `kerNat a b`. -/
theorem lmarginalPTraj_lt [∀ n, IsFiniteKernel (κ n)]
    {a b : ℕ} (hab : a < b) {f : ((n : ℕ) → X n) → ℝ≥0∞}
    (mf : Measurable f) (x : (n : ℕ) → X n) :
    lmarginalPTraj κ a b f x =
      ∫⁻ y : (i : Ioc a b) → X i, f (updateFinset x _ y) ∂kerNat κ a b (frestrictLe a x) := by
  rw [lmarginalPTraj, ptraj, dif_pos hab, Kernel.lintegral_map, Kernel.lintegral_id_prod]
  · congrm ∫⁻ y, f (fun i ↦ ?_) ∂_
    simp only [updateFinset, mem_Iic, el, id_eq, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, mem_Ioc]
    split_ifs <;> try rfl
    all_goals omega
  · exact mf.comp <| measurable_updateFinset.comp (el a b hab.le).measurable
  · exact (el ..).measurable
  · exact mf.comp measurable_updateFinset

/-- If `a < b`, then integrating `f` against the `ptraj κ a b` is the same as integrating
  against `kerNat a b`. -/
theorem lmarginalPTraj_succ [∀ n, IsFiniteKernel (κ n)]
    (a : ℕ) {f : ((n : ℕ) → X n) → ℝ≥0∞} (mf : Measurable f) (x₀ : (n : ℕ) → X n) :
    lmarginalPTraj κ a (a + 1) f x₀ =
      ∫⁻ x : X (a + 1), f (update x₀ _ x) ∂κ a (frestrictLe a x₀) := by
  rw [lmarginalPTraj_lt κ a.lt_succ_self mf, kerNat_succ_self, lintegral_map]
  · congrm ∫⁻ y, f (fun i ↦ ?_) ∂_
    simp [updateFinset, e, update]
  · exact (e ..).measurable
  · exact mf.comp measurable_updateFinset

theorem measurable_lmarginalPTraj (a b : ℕ) {f : ((n : ℕ) → X n) → ℝ≥0∞} (hf : Measurable f) :
    Measurable (lmarginalPTraj κ a b f) := by
  unfold lmarginalPTraj
  let g : ((i : Iic b) → X i) × ((n : ℕ) → X n) → ℝ≥0∞ :=
    fun c ↦ f (updateFinset c.2 _ c.1)
  let η : Kernel ((n : ℕ) → X n) ((i : Iic b) → X i) :=
    Kernel.comap (ptraj κ a b) (frestrictLe a) (measurable_frestrictLe _)
  change Measurable fun x ↦ ∫⁻ z : (i : Iic b) → X i, g (z, x) ∂η x
  refine Measurable.lintegral_kernel_prod_left' <| hf.comp ?_
  simp only [updateFinset, measurable_pi_iff]
  intro i
  by_cases h : i ∈ Iic b <;> simp [h]
  · exact (measurable_pi_apply _).comp <| measurable_fst
  · exact measurable_snd.eval

theorem updateFinset_updateFinset_subset {ι : Type*} [DecidableEq ι] {α : ι → Type*}
    (s t : Finset ι) (hst : s ⊆ t) (x : (i : ι) → α i)
    (y : (i : s) → α i) (z : (i : t) → α i) :
    updateFinset (updateFinset x s y) t z = updateFinset x t z := by
  ext i
  simp [updateFinset]
  split_ifs with h1 h2
  · rfl
  · exact (h1 (hst h2)).elim
  · rfl

theorem lmarginalPTraj_self [∀ n, IsMarkovKernel (κ n)] {a b c : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c)
    {f : ((n : ℕ) → X n) → ℝ≥0∞} (hf : Measurable f) :
    lmarginalPTraj κ a b (lmarginalPTraj κ b c f) =
      lmarginalPTraj κ a c f := by
  ext x
  obtain rfl | hab := eq_or_lt_of_le hab <;> obtain rfl | hbc := eq_or_lt_of_le hbc
  · rw [lmarginalPTraj_le κ (_root_.le_refl a) (measurable_lmarginalPTraj _ _ _ hf)]
  · rw [lmarginalPTraj_le κ (_root_.le_refl a) (measurable_lmarginalPTraj _ _ _ hf)]
  · rw [lmarginalPTraj_le κ (_root_.le_refl b) hf]
  simp_rw [lmarginalPTraj, frestrictLe, restrict_updateFinset,
    updateFinset_updateFinset_subset _ _ (Iic_subset_Iic.2 hbc.le)]
  rw [← lintegral_comp, ptraj_comp κ c hab.le]
  exact hf.comp <| measurable_updateFinset

end integral

end Kernel
end ProbabilityTheory

open ProbabilityTheory Kernel

variable [∀ n, IsMarkovKernel (κ n)]

namespace DependsOn

theorem lmarginalPTraj_eq {a b : ℕ} (c : ℕ) {f : ((n : ℕ) → X n) → ℝ≥0∞}
    (mf : Measurable f) (hf : DependsOn f (Iic a)) (hab : a ≤ b) :
    lmarginalPTraj κ b c f = f := by
  rcases le_or_lt c b with hcb | hbc
  · exact lmarginalPTraj_le κ hcb mf
  · ext x
    have := isMarkovKernel_kerNat κ hbc
    rw [lmarginalPTraj_lt κ hbc mf, ← mul_one (f x),
      ← measure_univ (μ := kerNat κ b c (frestrictLe b x)), ← MeasureTheory.lintegral_const]
    refine lintegral_congr fun y ↦ hf fun i hi ↦ ?_
    simp only [updateFinset, mem_Iic, el, id_eq, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk,
      dite_eq_right_iff, dite_eq_left_iff, not_le]
    intro h
    rw [mem_Ioc] at h
    rw [mem_coe, mem_Iic] at hi
    omega

theorem lmarginalPTraj_right {a : ℕ} (b : ℕ) {c d : ℕ}
    (mf : Measurable f) (hf : DependsOn f (Iic a)) (hac : a ≤ c) (had : a ≤ d) :
    lmarginalPTraj κ b c f = lmarginalPTraj κ b d f := by
  wlog hcd : c ≤ d generalizing c d
  · rw [@this d c had hac (le_of_not_le hcd)]
  · obtain hbc | hcb := le_or_lt b c
    · rw [← lmarginalPTraj_self κ hbc hcd mf,
        hf.lmarginalPTraj_eq κ d mf hac]
    · rw [hf.lmarginalPTraj_eq κ c mf (hac.trans hcb.le),
        hf.lmarginalPTraj_eq κ d mf (hac.trans hcb.le)]

theorem dependsOn_lmarginalPTraj (a : ℕ) {b : ℕ} {f : ((n : ℕ) → X n) → ℝ≥0∞}
    (hf : DependsOn f (Iic b)) (mf : Measurable f) :
    DependsOn (lmarginalPTraj κ a b f) (Iic a) := by
  intro x y hxy
  rcases le_or_lt b a with hba | hab
  · rw [lmarginalPTraj_le κ hba mf]
    exact hf fun i hi ↦ hxy i (Iic_subset_Iic.2 hba hi)
  · rw [lmarginalPTraj_lt _ hab mf, lmarginalPTraj_lt _ hab mf]
    congrm ∫⁻ z : _, ?_ ∂kerNat κ a b (fun i ↦ ?_)
    · exact hxy i.1 i.2
    · refine dependsOn_updateFinset hf _ _ ?_
      rwa [← coe_sdiff, Iic_sdiff_Ioc_same hab.le]

end DependsOn

end ptraj
