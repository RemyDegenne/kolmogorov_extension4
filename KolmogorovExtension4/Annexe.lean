/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.Data.Finset.Basic
import Mathlib.MeasureTheory.Constructions.Prod.Integral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.Kernel.Composition
import Mathlib.Probability.Kernel.Integral
import Mathlib.Probability.Kernel.MeasureCompProd
import Mathlib.Probability.Process.Filtration

/-!
New lemmas for mathlib
-/

open MeasureTheory ProbabilityTheory MeasurableSpace ENNReal Finset Function

section indicator

lemma indicator_one_mul_const {α M : Type*} [MonoidWithZero M] (s : Set α) (c : M) (a : α) :
    (s.indicator (1 : α → M) a) * c = s.indicator (fun _ ↦ c) a := by
  simp [Set.indicator]

lemma indicator_one_mul_const' {α M : Type*} [MonoidWithZero M] (s : Set α) (c : M) (a : α) :
    (s.indicator (fun _ ↦ 1 : α → M) a) * c = s.indicator (fun _ ↦ c) a := by
  simp [Set.indicator]

theorem preimage_indicator {α β M : Type*} [Zero M] (f : α → β) (s : Set β) (a : α) (c : M) :
    (f ⁻¹' s).indicator (fun _ ↦ c) a = s.indicator (fun _ ↦ c) (f a) := by
  by_cases h : f a ∈ s <;> simp [h]

theorem indicator_const_eq {α β M : Type*} [Zero M] {s : Set α} {t : Set β} {a : α} {b : β}
    (c : M) (h : a ∈ s ↔ b ∈ t) :
    s.indicator (fun _ ↦ c) a = t.indicator (fun _ ↦ c) b := by
  by_cases h' : a ∈ s
  · simp [h', h.1 h']
  · simp [h', h.not.1 h']

theorem indicator_const_eq_iff {α β M : Type*} [Zero M] {s : Set α} {t : Set β} {a : α} {b : β}
    (c : M) [hc : NeZero c] :
    s.indicator (fun _ ↦ c) a = t.indicator (fun _ ↦ c) b ↔ (a ∈ s ↔ b ∈ t) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · by_contra! h'
    rcases h' with (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · rw [Set.indicator_of_mem h1, Set.indicator_of_not_mem h2] at h
      exact hc.out h
    · rw [Set.indicator_of_not_mem h1, Set.indicator_of_mem h2] at h
      exact hc.out h.symm
  · by_cases h' : a ∈ s
    · simp [h', h.1 h']
    · simp [h', h.not.1 h']

theorem Set.indicator_const_smul_apply' {α R M : Type*} [Zero R] [Zero M] [SMulWithZero R M]
    (s : Set α) (r : R) (f : α → M) (a : α) :
    s.indicator (r • f) a = (s.indicator (fun _ ↦ r : α → R) a) • (f a) := by
  by_cases h : a ∈ s <;> simp [h]

theorem Set.indicator_one_smul_apply {α M β : Type*} [Zero β] [MonoidWithZero M]
    [MulActionWithZero M β] (f : α → β) (s : Set α) (a : α) :
    s.indicator f a = (s.indicator (fun _ ↦ 1 : α → M) a) • (f a) := by
  by_cases h : a ∈ s <;> simp [h]

end indicator

section Measure

variable {X Y Z T U : Type*}
variable [MeasurableSpace Z] [MeasurableSpace T] [MeasurableSpace U]

/-- If a function `g` is measurable with respect to the pullback along some function `f`, then
to prove `g x = g y` it is enough to prove `f x = f y`. -/
theorem eq_of_measurable_comap [m : MeasurableSpace Y] [MeasurableSingletonClass Z]
    (f : X → Y) {g : X → Z} (hg : @Measurable _ _ (m.comap f) _ g)
    {x₁ x₂ : X} (h : f x₁ = f x₂) : g x₁ = g x₂ := by
  rcases hg (measurableSet_singleton (g x₁)) with ⟨s, -, hs⟩
  have : x₁ ∈ f ⁻¹' s := by simp [hs]
  have : x₂ ∈ f ⁻¹' s := by rwa [Set.mem_preimage, ← h]
  rw [hs] at this
  exact (by simpa using this : g x₂ = g x₁).symm

/-- If a function `g` is strongly measurable with respect to the pullback along some function `f`,
then to prove `g x = g y` it is enough to prove `f x = f y`. -/
theorem eq_of_stronglyMeasurable_comap {Z : Type*} [m : MeasurableSpace Y]
    [TopologicalSpace Z] [TopologicalSpace.PseudoMetrizableSpace Z] [T1Space Z]
    (f : X → Y) {g : X → Z} (hg : @StronglyMeasurable _ _ _ (m.comap f) g)
    {x₁ x₂ : X} (h : f x₁ = f x₂) : g x₁ = g x₂ := by
  let _ : MeasurableSpace Z := borel Z
  have : BorelSpace Z := BorelSpace.mk rfl
  exact eq_of_measurable_comap f hg.measurable h

variable [MeasurableSpace X] [MeasurableSpace Y]

theorem Kernel.compProd_apply_prod (κ : Kernel X Y) [IsSFiniteKernel κ]
    (η : Kernel (X × Y) Z) [IsSFiniteKernel η]
    {s : Set Y} (hs : MeasurableSet s) {t : Set Z} (ht : MeasurableSet t) (x : X) :
    (κ ⊗ₖ η) x (s ×ˢ t) = ∫⁻ y in s, η (x, y) t ∂κ x := by
  rw [Kernel.compProd_apply _ _ _ (hs.prod ht), ← lintegral_indicator _ hs]
  congr with y
  by_cases hy : y ∈ s <;> simp [Set.indicator, hy]

theorem Kernel.map_map (κ : Kernel X Y) {f : Y → Z} (hf : Measurable f)
    {g : Z → T} (hg : Measurable g) :
    (κ.map f).map g = κ.map (g ∘ f) := by
  ext1 x
  rw [Kernel.map_apply _ hg, Kernel.map_apply _ hf, Measure.map_map hg hf,
    ← Kernel.map_apply _ (hg.comp hf)]

theorem Measure.map_prod (μ : Measure X) [IsFiniteMeasure μ]
    (ν : Measure Y) [IsFiniteMeasure ν] {f : X → Z} (hf : Measurable f)
    {g : Y → T} (hg : Measurable g) :
    (μ.prod ν).map (Prod.map f g) = (μ.map f).prod (ν.map g) := by
  refine (Measure.prod_eq fun s t ms mt ↦ ?_).symm
  rw [Measure.map_apply (hf.prod_map hg) (ms.prod mt)]
  · have : Prod.map f g ⁻¹' s ×ˢ t = (f ⁻¹' s) ×ˢ (g ⁻¹' t) := Set.prod_preimage_eq.symm
    rw [this, Measure.prod_prod, Measure.map_apply hf ms, Measure.map_apply hg mt]

theorem Kernel.map_prod (κ : Kernel X Y) [IsFiniteKernel κ] (η : Kernel X T) [IsFiniteKernel η]
    {f : Y → Z} (hf : Measurable f) {g : T → U} (hg : Measurable g) :
    (κ ×ₖ η).map (Prod.map f g) = (κ.map f) ×ₖ (η.map g) := by
  ext1 x
  rw [Kernel.map_apply _ (hf.prod_map hg), Kernel.prod_apply, Measure.map_prod _ _ hf hg,
    Kernel.prod_apply, Kernel.map_apply _ hf, Kernel.map_apply _ hg]

theorem Kernel.map_prod_fst (κ : Kernel X Y) [IsSFiniteKernel κ]
    (η : Kernel X Z) [IsMarkovKernel η] :
    (κ ×ₖ η).map Prod.fst = κ := by
  rw [← Kernel.fst_eq, Kernel.fst_prod κ η]

theorem Kernel.map_prod_snd (κ : Kernel X Y) [IsMarkovKernel κ]
    (η : Kernel X Z) [IsSFiniteKernel η] :
    (κ ×ₖ η).map Prod.snd = η := by
  rw [← Kernel.snd_eq, Kernel.snd_prod κ η]

theorem Kernel.map_deterministic {f : X → Y} (hf : Measurable f)
    {g : Y → Z} (hg : Measurable g) :
    (Kernel.deterministic f hf).map g = Kernel.deterministic (g ∘ f) (hg.comp hf) := by
  ext x s ms
  rw [Kernel.map_apply' _ hg _ ms, Kernel.deterministic_apply' _ _ (hg ms),
    Kernel.deterministic_apply' _ _ ms, preimage_indicator]
  rfl

theorem Kernel.deterministic_prod_apply' {f : X → Y} (mf : Measurable f)
    (η : Kernel X Z) [IsSFiniteKernel η] (x : X)
    {s : Set (Y × Z)} (ms : MeasurableSet s) :
    ((Kernel.deterministic f mf) ×ₖ η) x s = η x {z | (f x, z) ∈ s} := by
  rw [Kernel.prod_apply' _ _ _ ms, Kernel.lintegral_deterministic']
  exact measurable_measure_prod_mk_left ms

theorem Kernel.prod_apply_symm' (κ : Kernel X Y) [IsSFiniteKernel κ]
    (η : Kernel X Z) [IsSFiniteKernel η]
    (x : X) {s : Set (Y × Z)} (hs : MeasurableSet s) :
    (κ ×ₖ η) x s = ∫⁻ z, κ x ((fun y ↦ (y, z)) ⁻¹' s) ∂η x := by
  rw [Kernel.prod_apply, Measure.prod_apply_symm hs]

theorem Kernel.prod_deterministic_apply' {f : X → Z} (mf : Measurable f)
    (η : Kernel X Y) [IsSFiniteKernel η] (x : X)
    {s : Set (Y × Z)} (ms : MeasurableSet s) :
    (η ×ₖ (Kernel.deterministic f mf)) x s = η x {y | (y, f x) ∈ s} := by
  rw [Kernel.prod_apply_symm' _ _ _ ms, Kernel.lintegral_deterministic']
  · rfl
  · exact measurable_measure_prod_mk_right ms

theorem Measure.map_snd_compProd (μ : Measure X) [IsProbabilityMeasure μ] (κ : Kernel X Y)
    [IsSFiniteKernel κ] {f : Y → Z} (hf : Measurable f) :
    (μ ⊗ₘ κ).snd.map f = (μ ⊗ₘ (κ.map f)).snd := by
  ext s ms
  rw [Measure.map_apply hf ms, Measure.snd_apply (hf ms), ← Set.univ_prod,
    Measure.compProd_apply_prod MeasurableSet.univ (hf ms), Measure.snd_apply ms, ← Set.univ_prod,
    Measure.compProd_apply_prod MeasurableSet.univ ms]
  simp_rw [Kernel.map_apply' _ hf _ ms]

theorem Measure.fst_compProd (μ : Measure X) [SFinite μ]
    (κ : Kernel X Y) [IsMarkovKernel κ] :
    (μ ⊗ₘ κ).fst = μ := by
  ext s ms
  rw [Measure.fst_apply ms, ← Set.prod_univ, Measure.compProd_apply_prod ms MeasurableSet.univ]
  simp

theorem Kernel.comap_const (μ : Measure Z) {f : X → Y} (hf : Measurable f) :
    Kernel.comap (Kernel.const Y μ) f hf = Kernel.const X μ := by
  ext1 x
  rw [Kernel.const_apply, Kernel.comap_apply, Kernel.const_apply]

variable {E : Type*} [NormedAddCommGroup E]

theorem Kernel.integrable_prod_iff (κ : Kernel X Y) [IsFiniteKernel κ]
    (η : Kernel X Z) [IsFiniteKernel η] (x : X) {f : (Y × Z) → E}
    (hf : AEStronglyMeasurable f ((κ ×ₖ η) x)) : Integrable f ((κ ×ₖ η) x) ↔
      (∀ᵐ y ∂κ x, Integrable (fun z ↦ f (y, z)) (η x)) ∧
      Integrable (fun y ↦ ∫ z, ‖f (y, z)‖ ∂η x) (κ x) := by
  rwa [Kernel.prod_apply, MeasureTheory.integrable_prod_iff] at *

theorem Kernel.integrable_prod_iff' (κ : Kernel X Y) [IsFiniteKernel κ]
    (η : Kernel X Z) [IsFiniteKernel η] (x : X) {f : (Y × Z) → E}
    (hf : AEStronglyMeasurable f ((κ ×ₖ η) x)) : Integrable f ((κ ×ₖ η) x) ↔
      (∀ᵐ z ∂η x, Integrable (fun y ↦ f (y, z)) (κ x)) ∧
      Integrable (fun z ↦ ∫ y, ‖f (y, z)‖ ∂κ x) (η x) := by
  rwa [Kernel.prod_apply, MeasureTheory.integrable_prod_iff'] at *

theorem integrable_dirac {f : X → E} (mf : StronglyMeasurable f) {x : X} :
    Integrable f (Measure.dirac x) := by
    let _ : MeasurableSpace E := borel E
    have _ : BorelSpace E := BorelSpace.mk rfl
    have : f =ᵐ[Measure.dirac x] (fun _ ↦ f x) := ae_eq_dirac' mf.measurable
    rw [integrable_congr this]
    exact integrable_const _

theorem Kernel.integrable_deterministic_prod {f : X → Y} (mf : Measurable f)
    (κ : Kernel X Z) [IsFiniteKernel κ] (x : X)
    {g : (Y × Z) → E} (mg : StronglyMeasurable g) :
    Integrable g (((Kernel.deterministic f mf) ×ₖ κ) x) ↔
      Integrable (fun z ↦ g (f x, z)) (κ x) := by
  rw [Kernel.integrable_prod_iff]
  · constructor
    · rintro ⟨h, -⟩
      rwa [Kernel.deterministic_apply, ae_dirac_iff] at h
      exact measurableSet_integrable mg
    · intro h
      constructor
      · rwa [Kernel.deterministic_apply, ae_dirac_iff]
        exact measurableSet_integrable mg
      · rw [Kernel.deterministic_apply]
        apply integrable_dirac
        exact mg.norm.integral_prod_right'
  · exact mg.aestronglyMeasurable

theorem Kernel.integrable_comp_iff (η : Kernel Y Z) [IsSFiniteKernel η]
    (κ : Kernel X Y) [IsSFiniteKernel κ] (x : X)
    {f : Z → E} (hf : AEStronglyMeasurable f ((η ∘ₖ κ) x)) :
    Integrable f ((η ∘ₖ κ) x) ↔
    (∀ᵐ y ∂κ x, Integrable f (η y)) ∧ (Integrable (fun y ↦ ∫ z, ‖f z‖ ∂η y) (κ x)) := by
  rw [Kernel.comp_eq_snd_compProd, Kernel.snd_eq, Kernel.map_apply _ measurable_snd] at *
  rw [integrable_map_measure, ProbabilityTheory.integrable_compProd_iff]
  · rfl
  · exact hf.comp_measurable measurable_snd
  · exact hf
  · exact measurable_snd.aemeasurable

variable [NormedSpace ℝ E]

theorem Kernel.integral_prod (κ : Kernel X Y) [IsFiniteKernel κ]
    (η : Kernel X Z) [IsFiniteKernel η] (x : X)
    {f : (Y × Z) → E} (hf : Integrable f ((κ ×ₖ η) x)) :
    ∫ p, f p ∂(κ ×ₖ η) x = ∫ y, ∫ z, f (y, z) ∂η x ∂κ x := by
  rw [Kernel.prod_apply, MeasureTheory.integral_prod]
  rwa [← Kernel.prod_apply]

theorem Kernel.integral_comp (η : Kernel Y Z) [IsFiniteKernel η]
    (κ : Kernel X Y) [IsFiniteKernel κ]
    (x : X) {g : Z → E} (hg : Integrable g ((η ∘ₖ κ) x)) :
    ∫ z, g z ∂(η ∘ₖ κ) x = ∫ y, ∫ z, g z ∂η y ∂κ x := by
  rw [Kernel.comp_eq_snd_compProd, Kernel.snd_apply, integral_map,
    ProbabilityTheory.integral_compProd]
  · simp_rw [Kernel.prodMkLeft_apply η]
  · apply Integrable.comp_measurable
    · convert hg
      rw [Kernel.comp_eq_snd_compProd, Kernel.snd_apply]
    · exact measurable_snd
  · exact measurable_snd.aemeasurable
  · convert hg.aestronglyMeasurable
    rw [Kernel.comp_eq_snd_compProd, Kernel.snd_apply]

variable [CompleteSpace E]

theorem Kernel.integral_deterministic_prod {f : X → Y} (mf : Measurable f)
    (κ : Kernel X Z) [IsFiniteKernel κ] (x : X)
    {g : (Y × Z) → E} (mg : StronglyMeasurable g)
    (i_g : Integrable (fun z ↦ g (f x, z)) (κ x)) :
    ∫ p, g p ∂((Kernel.deterministic f mf) ×ₖ κ) x = ∫ z, g (f x, z) ∂κ x := by
  rw [Kernel.integral_prod, Kernel.integral_deterministic']
  · exact mg.integral_prod_right'
  · rwa [Kernel.integrable_deterministic_prod _ _ _ mg]

theorem Kernel.lintegral_deterministic_prod {f : X → Y} (mf : Measurable f)
    (κ : Kernel X Z) [IsFiniteKernel κ] (x : X)
    {g : (Y × Z) → ℝ≥0∞} (mg : Measurable g) :
    ∫⁻ p, g p ∂((Kernel.deterministic f mf) ×ₖ κ) x = ∫⁻ z, g (f x, z) ∂κ x := by
  rw [Kernel.lintegral_prod _ _ _ mg, Kernel.lintegral_deterministic']
  exact mg.lintegral_prod_right'

theorem MeasureTheory.Filtration.condexp_condexp {ι : Type*} [Preorder ι]
    (f : X → E) {μ : Measure X} (ℱ : @Filtration X ι _ inferInstance)
    {i j : ι} (hij : i ≤ j) [SigmaFinite (μ.trim (ℱ.le j))] :
    μ[μ[f|ℱ j]|ℱ i] =ᵐ[μ] μ[f|ℱ i] := condexp_condexp_of_le (ℱ.mono hij) (ℱ.le j)

end Measure

section Finset

lemma mem_Ioc_succ {n i : ℕ} : i ∈ Ioc n (n + 1) ↔ i = n + 1 := by
  rw [mem_Ioc]
  omega

theorem updateFinset_self {ι : Type*} [DecidableEq ι] {α : ι → Type*} (x : (i : ι) → α i)
    {s : Finset ι} (y : (i : s) → α i) : (fun i : s ↦ updateFinset x s y i) = y := by
  ext i
  simp [updateFinset, i.2]

lemma Finset.sub_Iic (I : Finset ℕ) : I ⊆ (Iic (I.sup id)) :=
  fun _ hi ↦ mem_Iic.2 <| le_sup (f := id) hi

theorem Set.Iic_diff_Ioc_same {α : Type*} [LinearOrder α]
    {a b : α} (hab : a ≤ b) : (Set.Iic b) \ (Set.Ioc a b) = Set.Iic a := by
  ext x
  simp only [mem_diff, mem_Iic, mem_Ioc, not_and, not_le]
  refine ⟨fun ⟨h1, h2⟩ ↦ ?_, fun h ↦ ⟨h.trans hab, fun h' ↦ (not_le.2 h' h).elim⟩⟩
  · by_contra h3
    exact (not_le.2 (h2 (not_le.1 h3))) h1

theorem Finset.Iic_sdiff_Ioc_same {α : Type*} [LinearOrder α] [OrderBot α] [LocallyFiniteOrder α]
    {a b : α} (hab : a ≤ b) : (Iic b) \ (Ioc a b) = Iic a := by
  rw [← coe_inj, coe_sdiff, coe_Iic, coe_Ioc, coe_Iic, Set.Iic_diff_Ioc_same hab]

theorem Finset.right_mem_Iic {α : Type*} [Preorder α] [LocallyFiniteOrderBot α] (a : α) :
    a ∈ Iic a := mem_Iic.2 <| le_refl a

theorem Finset.Iic_union_Ioc_eq_Iic {α : Type*} [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α]
    {a b : α} (h : a ≤ b) : Iic a ∪ Ioc a b = Iic b := by
  rw [← coe_inj, coe_union, coe_Iic, coe_Iic, coe_Ioc, Set.Iic_union_Ioc_eq_Iic h]

theorem Finset.disjoint_Iic_Ioc {α : Type*} [Preorder α] [LocallyFiniteOrder α] [OrderBot α]
    {a b c : α} (h : a ≤ b) : Disjoint (Iic a) (Ioc b c) :=
  disjoint_left.2 fun _ hax hbcx ↦ (mem_Iic.1 hax).not_lt <| lt_of_le_of_lt h (mem_Ioc.1 hbcx).1

end Finset

section Product

theorem Finset.prod_congr' {α M : Type*} [CommMonoid M] {s t : Finset α} (hst : s = t)
    (f : t → M) : ∏ i : s, f ⟨i.1, hst ▸ i.2⟩ = ∏ i : t, f i := by cases hst; rfl

theorem Finset.prod_union' {α M : Type*} [DecidableEq α] [CommMonoid M] {s t : Finset α}
    (hst : Disjoint s t) (f : ↑(s ∪ t) → M) :
    (∏ i : s, f ⟨i.1, subset_union_left i.2⟩) * ∏ i : t, f ⟨i.1, subset_union_right i.2⟩ =
    ∏ i : ↑(s ∪ t), f i := by
  let g : α → M := fun a ↦ if ha : a ∈ s ∪ t then f ⟨a, ha⟩ else 1
  have h1 : ∏ i : s, f ⟨i.1, subset_union_left i.2⟩ = ∏ i : s, g i := by simp [g]
  have h2 : ∏ i : t, f ⟨i.1, subset_union_right i.2⟩ = ∏ i : t, g i := by simp [g]
  have h3 : ∏ i : ↑(s ∪ t), f i = ∏ i : ↑(s ∪ t), g i := by simp [g, -mem_union]
  rw [h1, h2, h3, prod_coe_sort, prod_coe_sort, prod_coe_sort, ← disjUnion_eq_union _ _ hst,
    prod_disjUnion hst]

theorem prod_Ioc {M : Type*} [CommMonoid M] (n : ℕ) (f : (Ioc 0 (n + 1)) → M) :
    (f ⟨n + 1, mem_Ioc.2 ⟨n.succ_pos, le_refl _⟩⟩) *
      (∏ i : Ioc 0 n, f ⟨i.1, Ioc_subset_Ioc_right n.le_succ i.2⟩) =
    ∏ i : Ioc 0 (n + 1), f i := by
  let g : ℕ → M := fun k ↦ if hk : k ∈ Ioc 0 (n + 1) then f ⟨k, hk⟩ else 1
  have h1 : ∏ i : Ioc 0 n, f ⟨i.1, Ioc_subset_Ioc_right n.le_succ i.2⟩ =
      ∏ i : Ioc 0 n, g i := by
    refine prod_congr rfl ?_
    simp only [mem_univ, mem_Ioc, true_implies, Subtype.forall, g]
    rintro k ⟨hk1, hk2⟩
    rw [dif_pos ⟨hk1, hk2.trans n.le_succ⟩]
  have h2 : ∏ i : Ioc 0 (n + 1), f i = ∏ i : Ioc 0 (n + 1), g i := by
    refine prod_congr rfl ?_
    simp only [mem_univ, mem_Ioc, Subtype.coe_eta, dite_eq_ite, true_implies, Subtype.forall,
      g]
    intro k hk
    simp [hk]
  rw [h1, h2, prod_coe_sort, prod_coe_sort]
  have : f ⟨n + 1, right_mem_Ioc.2 n.succ_pos⟩ = g (n + 1) := by simp [g]
  rw [this]
  exact mul_prod_Ico_eq_prod_Icc (Nat.le_add_left (0 + 1) n)

end Product
