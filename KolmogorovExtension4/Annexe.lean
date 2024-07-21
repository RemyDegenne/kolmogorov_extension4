/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.Probability.Kernel.Composition
import Mathlib.Probability.Kernel.MeasureCompProd
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Constructions.Prod.Integral
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

variable {X Y Z T U : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable [MeasurableSpace Z] [MeasurableSpace T] [MeasurableSpace U]

theorem kernel.compProd_apply_prod (κ : kernel X Y) [IsSFiniteKernel κ]
    (η : kernel (X × Y) Z) [IsSFiniteKernel η]
    {s : Set Y} (hs : MeasurableSet s) {t : Set Z} (ht : MeasurableSet t) (x : X) :
    (κ ⊗ₖ η) x (s ×ˢ t) = ∫⁻ y in s, η (x, y) t ∂κ x := by
  rw [kernel.compProd_apply _ _ _ (hs.prod ht), ← lintegral_indicator _ hs]
  congr with y
  by_cases hy : y ∈ s <;> simp [Set.indicator, hy]

theorem kernel.map_map (κ : kernel X Y) {f : Y → Z} (hf : Measurable f)
    {g : Z → T} (hg : Measurable g) :
    kernel.map (kernel.map κ f hf) g hg = kernel.map κ (g ∘ f) (hg.comp hf) := by
  ext1 x
  rw [kernel.map_apply, kernel.map_apply, Measure.map_map hg hf, ← kernel.map_apply]

theorem Measure.map_prod (μ : Measure X) [IsFiniteMeasure μ]
    (ν : Measure Y) [IsFiniteMeasure ν] {f : X → Z} (hf : Measurable f)
    {g : Y → T} (hg : Measurable g) :
    (μ.prod ν).map (Prod.map f g) = (μ.map f).prod (ν.map g) := by
  refine (Measure.prod_eq fun s t ms mt ↦ ?_).symm
  rw [Measure.map_apply (hf.prod_map hg) (ms.prod mt)]
  · have : Prod.map f g ⁻¹' s ×ˢ t = (f ⁻¹' s) ×ˢ (g ⁻¹' t) := Set.prod_preimage_eq.symm
    rw [this, Measure.prod_prod, Measure.map_apply hf ms, Measure.map_apply hg mt]

theorem kernel.map_prod (κ : kernel X Y) [IsFiniteKernel κ] (η : kernel X T) [IsFiniteKernel η]
    {f : Y → Z} (hf : Measurable f) {g : T → U} (hg : Measurable g) :
    kernel.map (κ ×ₖ η) (Prod.map f g) (hf.prod_map hg) =
    (kernel.map κ f hf) ×ₖ (kernel.map η g hg) := by
  ext1 x
  rw [kernel.map_apply, kernel.prod_apply, Measure.map_prod _ _ hf hg, kernel.prod_apply,
    kernel.map_apply, kernel.map_apply]

theorem kernel.map_prod_fst (κ : kernel X Y) [IsSFiniteKernel κ]
    (η : kernel X Z) [IsMarkovKernel η] :
    kernel.map (κ ×ₖ η) Prod.fst measurable_fst = κ := kernel.fst_prod κ η

theorem kernel.map_prod_snd (κ : kernel X Y) [IsMarkovKernel κ]
    (η : kernel X Z) [IsSFiniteKernel η] :
    kernel.map (κ ×ₖ η) Prod.snd measurable_snd = η := kernel.snd_prod κ η

theorem kernel.map_deterministic {f : X → Y} (hf : Measurable f)
    {g : Y → Z} (hg : Measurable g) :
    kernel.map (kernel.deterministic f hf) g hg = kernel.deterministic (g ∘ f) (hg.comp hf) := by
  ext x s ms
  rw [kernel.map_apply' _ _ _ ms, kernel.deterministic_apply' _ _ (hg ms),
    kernel.deterministic_apply' _ _ ms, preimage_indicator]
  rfl

theorem kernel.deterministic_prod_apply' {f : X → Y} (mf : Measurable f)
    (η : kernel X Z) [IsSFiniteKernel η] (x : X)
    {s : Set (Y × Z)} (ms : MeasurableSet s) :
    ((kernel.deterministic f mf) ×ₖ η) x s = η x {z | (f x, z) ∈ s} := by
  rw [kernel.prod_apply' _ _ _ ms, kernel.lintegral_deterministic']
  exact measurable_measure_prod_mk_left ms

theorem kernel.prod_apply_symm' (κ : kernel X Y) [IsSFiniteKernel κ]
    (η : kernel X Z) [IsSFiniteKernel η]
    (x : X) {s : Set (Y × Z)} (hs : MeasurableSet s) :
    (κ ×ₖ η) x s = ∫⁻ z, κ x ((fun y ↦ (y, z)) ⁻¹' s) ∂η x := by
  rw [kernel.prod_apply, Measure.prod_apply_symm hs]

theorem kernel.prod_deterministic_apply' {f : X → Z} (mf : Measurable f)
    (η : kernel X Y) [IsSFiniteKernel η] (x : X)
    {s : Set (Y × Z)} (ms : MeasurableSet s) :
    (η ×ₖ (kernel.deterministic f mf)) x s = η x {y | (y, f x) ∈ s} := by
  rw [kernel.prod_apply_symm' _ _ _ ms, kernel.lintegral_deterministic']
  · rfl
  · exact measurable_measure_prod_mk_right ms

theorem Measure.map_snd_compProd (μ : Measure X) [IsProbabilityMeasure μ] (κ : kernel X Y)
    [IsSFiniteKernel κ] {f : Y → Z} (hf : Measurable f) :
    (μ ⊗ₘ κ).snd.map f = (μ ⊗ₘ (kernel.map κ f hf)).snd := by
  ext s ms
  rw [Measure.map_apply hf ms, Measure.snd_apply (hf ms), ← Set.univ_prod,
    Measure.compProd_apply_prod MeasurableSet.univ (hf ms), Measure.snd_apply ms, ← Set.univ_prod,
    Measure.compProd_apply_prod MeasurableSet.univ ms]
  simp_rw [kernel.map_apply' _ _ _ ms]

theorem Measure.fst_compProd (μ : Measure X) [SFinite μ]
    (κ : kernel X Y) [IsMarkovKernel κ] :
    (μ ⊗ₘ κ).fst = μ := by
  ext s ms
  rw [Measure.fst_apply ms, ← Set.prod_univ, Measure.compProd_apply_prod ms MeasurableSet.univ]
  simp

theorem kernel.map_eq (κ : kernel X Y) {f g : Y → Z} (hf : Measurable f) (hfg : f = g) :
    kernel.map κ f hf = kernel.map κ g (hfg ▸ hf) := by cases hfg; rfl

theorem kernel.comap_const (μ : Measure Z) {f : X → Y} (hf : Measurable f) :
    kernel.comap (kernel.const Y μ) f hf = kernel.const X μ := by
  ext1 x
  rw [kernel.const_apply, kernel.comap_apply, kernel.const_apply]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem MeasureTheory.Filtration.condexp_condexp {ι : Type*} [Preorder ι]
    (f : X → E) {μ : Measure X} (ℱ : @Filtration X ι _ inferInstance)
    {i j : ι} (hij : i ≤ j) [SigmaFinite (μ.trim (ℱ.le j))] :
    μ[μ[f|ℱ j]|ℱ i] =ᵐ[μ] μ[f|ℱ i] := condexp_condexp_of_le (ℱ.mono hij) (ℱ.le j)

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

theorem kernel.integrable_prod_iff (κ : kernel X Y) [IsFiniteKernel κ]
    (η : kernel X Z) [IsFiniteKernel η] (x : X) {f : (Y × Z) → E}
    (hf : AEStronglyMeasurable f ((κ ×ₖ η) x)) : Integrable f ((κ ×ₖ η) x) ↔
      (∀ᵐ y ∂κ x, Integrable (fun z ↦ f (y, z)) (η x)) ∧
      Integrable (fun y ↦ ∫ z, ‖f (y, z)‖ ∂η x) (κ x) := by
  rwa [kernel.prod_apply, MeasureTheory.integrable_prod_iff] at *

theorem kernel.integrable_prod_iff' (κ : kernel X Y) [IsFiniteKernel κ]
    (η : kernel X Z) [IsFiniteKernel η] (x : X) {f : (Y × Z) → E}
    (hf : AEStronglyMeasurable f ((κ ×ₖ η) x)) : Integrable f ((κ ×ₖ η) x) ↔
      (∀ᵐ z ∂η x, Integrable (fun y ↦ f (y, z)) (κ x)) ∧
      Integrable (fun z ↦ ∫ y, ‖f (y, z)‖ ∂κ x) (η x) := by
  rwa [kernel.prod_apply, MeasureTheory.integrable_prod_iff'] at *

theorem kernel.integral_prod (κ : kernel X Y) [IsFiniteKernel κ]
    (η : kernel X Z) [IsFiniteKernel η] (x : X)
    {f : (Y × Z) → E} (hf : Integrable f ((κ ×ₖ η) x)) :
    ∫ p, f p ∂(κ ×ₖ η) x = ∫ y, ∫ z, f (y, z) ∂η x ∂κ x := by
  rw [kernel.prod_apply, MeasureTheory.integral_prod]
  rwa [← kernel.prod_apply]

theorem integrable_dirac {f : X → E} (mf : StronglyMeasurable f) {x : X} :
    Integrable f (Measure.dirac x) := by
    let _ : MeasurableSpace E := borel E
    have _ : BorelSpace E := BorelSpace.mk rfl
    have : f =ᵐ[Measure.dirac x] (fun _ ↦ f x) := ae_eq_dirac' mf.measurable
    rw [integrable_congr this]
    exact integrable_const _

theorem kernel.integrable_deterministic_prod {f : X → Y} (mf : Measurable f)
    (κ : kernel X Z) [IsFiniteKernel κ] (x : X)
    {g : (Y × Z) → E} (mg : StronglyMeasurable g) :
    Integrable g (((kernel.deterministic f mf) ×ₖ κ) x) ↔
      Integrable (fun z ↦ g (f x, z)) (κ x) := by
  rw [kernel.integrable_prod_iff]
  · constructor
    · rintro ⟨h, -⟩
      rwa [kernel.deterministic_apply, ae_dirac_iff] at h
      exact measurableSet_integrable mg
    · intro h
      constructor
      · rwa [kernel.deterministic_apply, ae_dirac_iff]
        exact measurableSet_integrable mg
      · rw [kernel.deterministic_apply]
        apply integrable_dirac
        exact mg.norm.integral_prod_right'
  · exact mg.aestronglyMeasurable

theorem kernel.integral_deterministic_prod {f : X → Y} (mf : Measurable f)
    (κ : kernel X Z) [IsFiniteKernel κ] (x : X)
    {g : (Y × Z) → E} (mg : StronglyMeasurable g)
    (i_g : Integrable (fun z ↦ g (f x, z)) (κ x)) :
    ∫ p, g p ∂((kernel.deterministic f mf) ×ₖ κ) x = ∫ z, g (f x, z) ∂κ x := by
  rw [kernel.integral_prod, kernel.integral_deterministic']
  · exact mg.integral_prod_right'
  · rwa [kernel.integrable_deterministic_prod _ _ _ mg]

theorem kernel.integrable_comp_iff (η : kernel Y Z) [IsSFiniteKernel η]
    (κ : kernel X Y) [IsSFiniteKernel κ] (x : X)
    {f : Z → E} (hf : AEStronglyMeasurable f ((η ∘ₖ κ) x)) :
    Integrable f ((η ∘ₖ κ) x) ↔
    (∀ᵐ y ∂κ x, Integrable f (η y)) ∧ (Integrable (fun y ↦ ∫ z, ‖f z‖ ∂η y) (κ x)) := by
  rw [kernel.comp_eq_snd_compProd, kernel.snd] at *
  rw [kernel.map_apply, integrable_map_measure, ProbabilityTheory.integrable_compProd_iff]
  · rfl
  · exact hf.comp_measurable measurable_snd
  · exact hf
  · exact measurable_snd.aemeasurable

theorem kernel.integral_comp (η : kernel Y Z) [IsFiniteKernel η]
    (κ : kernel X Y) [IsFiniteKernel κ]
    (x : X) {g : Z → E} (hg : Integrable g ((η ∘ₖ κ) x)) :
    ∫ z, g z ∂(η ∘ₖ κ) x = ∫ y, ∫ z, g z ∂η y ∂κ x := by
  rw [kernel.comp_eq_snd_compProd, kernel.snd_apply, integral_map,
    ProbabilityTheory.integral_compProd]
  · simp_rw [kernel.prodMkLeft_apply η]
  · apply Integrable.comp_measurable
    · convert hg
      rw [kernel.comp_eq_snd_compProd, kernel.snd_apply]
    · exact measurable_snd
  · exact measurable_snd.aemeasurable
  · convert hg.aestronglyMeasurable
    rw [kernel.comp_eq_snd_compProd, kernel.snd_apply]

end Measure

section Finset

lemma mem_Ioc_succ {n i : ℕ} : i ∈ Ioc n (n + 1) ↔ i = n + 1 := by
  rw [mem_Ioc]
  omega

theorem updateFinset_self {ι : Type*} [DecidableEq ι] {α : ι → Type*} (x : (i : ι) → α i)
    {s : Finset ι} (y : (i : s) → α i) : (fun i : s ↦ updateFinset x s y i) = y := by
  ext i
  simp [updateFinset, i.2]

theorem Finset.Iic_subset_Iic {α : Type*} [Preorder α] [LocallyFiniteOrderBot α]
    {a b : α} : Iic a ⊆ Iic b ↔ a ≤ b := by
  rw [← coe_subset, coe_Iic, coe_Iic, Set.Iic_subset_Iic]

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

end Finset

section Product

theorem prod_Iic {M : Type*} [CommMonoid M] (n : ℕ) (f : (Iic n) → M) :
    (∏ i : Ioc 0 n, f ⟨i.1, Ioc_subset_Iic_self i.2⟩) * f ⟨0, mem_Iic.2 <| zero_le _⟩ =
    ∏ i : Iic n, f i := by
  let g : ℕ → M := fun k ↦ if hk : k ∈ Iic n then f ⟨k, hk⟩ else 1
  have h1 : ∏ i : Ioc 0 n, f ⟨i.1, Ioc_subset_Iic_self i.2⟩ = ∏ i : Ioc 0 n, g i := by
    refine prod_congr rfl ?_
    simp only [mem_univ, mem_Ioc, true_implies, Subtype.forall, g]
    rintro k ⟨hk1, hk2⟩
    rw [dif_pos <| mem_Iic.2 hk2]
  have h2 : ∏ i : Iic n, f i = ∏ i : Iic n, g i := by
    refine prod_congr rfl ?_
    simp only [mem_univ, mem_Ioc, Subtype.coe_eta, dite_eq_ite, true_implies, Subtype.forall,
      g]
    intro k hk
    simp [hk]
  rw [h1, h2, prod_coe_sort, prod_coe_sort]
  have : f ⟨0, mem_Iic.2 <| zero_le _⟩ = g 0 := by simp [g]
  rw [this]
  exact prod_Ioc_mul_eq_prod_Icc (zero_le n)

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
