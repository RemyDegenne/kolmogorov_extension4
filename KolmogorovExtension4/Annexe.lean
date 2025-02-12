/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import KolmogorovExtension4.DependsOn
import Mathlib.Data.Finset.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.PreorderRestrict
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Integral
import Mathlib.Probability.Process.Filtration

/-!
New lemmas for mathlib
-/

open MeasureTheory ProbabilityTheory MeasurableSpace ENNReal Finset Function Preorder



section Lemmas

@[measurability, fun_prop]
lemma measurable_cast {X Y : Type u} [mX : MeasurableSpace X] [mY : MeasurableSpace Y] (h : X = Y)
    (hm : HEq mX mY) : Measurable (cast h) := by
  subst h
  subst hm
  exact measurable_id

theorem update_updateFinset_eq {X : ℕ → Type*} (x z : Π n, X n) {m : ℕ} :
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

lemma lintegral_le_mul_ae [MeasurableSpace X] {μ : Measure X} {f : X → ℝ≥0∞}
    {b : ℝ≥0∞} (hf : ∀ᵐ x ∂μ, f x ≤ b) : ∫⁻ x, f x ∂μ ≤ b * (μ Set.univ) := by
  rw [← lintegral_const]
  exact lintegral_mono_ae hf

lemma lintegral_le_mul [MeasurableSpace X] (μ : Measure X) {f : X → ℝ≥0∞}
    {b : ℝ≥0∞} (hf : ∀ x, f x ≤ b) : ∫⁻ x, f x ∂μ ≤ b * (μ Set.univ) :=
  lintegral_le_mul_ae (Filter.Eventually.of_forall hf)

lemma lintegral_le_ae [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    {f : X → ℝ≥0∞} {b : ℝ≥0∞} (hf : ∀ᵐ x ∂μ, f x ≤ b) : ∫⁻ x, f x ∂μ ≤ b := by
  simpa using lintegral_le_mul_ae hf

lemma lintegral_le [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] {f : X → ℝ≥0∞}
    {b : ℝ≥0∞} (hf : ∀ x, f x ≤ b) : ∫⁻ x, f x ∂μ ≤ b := by
  simpa using lintegral_le_mul μ hf

lemma lintegral_eq_const [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] {f : X → ℝ≥0∞}
    {c : ℝ≥0∞} (hf : ∀ x, f x = c) : ∫⁻ x, f x ∂μ = c := by simp [hf]

section Filtration

/-- If a function `g` is measurable with respect to the pullback along some function `f`, then
to prove `g x = g y` it is enough to prove `f x = f y`. -/
theorem eq_of_measurable_comap [m : MeasurableSpace Y] [MeasurableSingletonClass Z]
    (f : X → Y) {g : X → Z} (hg : Measurable[m.comap f] g)
    {x₁ x₂ : X} (h : f x₁ = f x₂) : g x₁ = g x₂ := by
  obtain ⟨s, -, hs⟩ := hg (measurableSet_singleton (g x₁))
  have : x₁ ∈ f ⁻¹' s := by simp [hs]
  have : x₂ ∈ f ⁻¹' s := by rwa [Set.mem_preimage, ← h]
  rw [hs] at this
  exact (by simpa using this : g x₂ = g x₁).symm

/-- If a function `g` is strongly measurable with respect to the pullback along some function `f`,
then to prove `g x = g y` it is enough to prove `f x = f y`. -/
theorem eq_of_stronglyMeasurable_comap {Z : Type*} [m : MeasurableSpace Y]
    [TopologicalSpace Z] [TopologicalSpace.PseudoMetrizableSpace Z] [T1Space Z]
    (f : X → Y) {g : X → Z} (hg : StronglyMeasurable[m.comap f] g)
    {x₁ x₂ : X} (h : f x₁ = f x₂) : g x₁ = g x₂ := by
  let _ : MeasurableSpace Z := borel Z
  have : BorelSpace Z := BorelSpace.mk rfl
  exact eq_of_measurable_comap f hg.measurable h

variable {ι : Type*} [Preorder ι] [LocallyFiniteOrderBot ι]
  {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

/-- The canonical filtration on dependent functions indexed by `ℕ`, where `𝓕 n` consists of
measurable sets depending only on coordinates `≤ n`. -/
def Filtration.pi_preorder : @Filtration ((i : ι) → X i) ι _ inferInstance where
  seq n := (inferInstance : MeasurableSpace (Π i : Iic n, X i)).comap (frestrictLe n)
  mono' i j hij := by
    simp only
    rw [← frestrictLe₂_comp_frestrictLe hij, ← comap_comp]
    exact MeasurableSpace.comap_mono (measurable_frestrictLe₂ _).comap_le
  le' n := (measurable_frestrictLe n).comap_le

variable {E : Type*} [NormedAddCommGroup E]

/-- If a function is strongly measurable with respect to the σ-algebra generated by the
first coordinates, then it only depends on those first coordinates. -/
theorem dependsOn_of_stronglyMeasurable {i : ι} {f : ((i : ι) → X i) → E}
    (mf : StronglyMeasurable[Filtration.pi_preorder i] f) : DependsOn f (Set.Iic i) :=
  fun _ _ h ↦ eq_of_stronglyMeasurable_comap _ mf (dependsOn_frestrictLe i h)

end Filtration

variable [MeasurableSpace X] [MeasurableSpace Y]
  {κ : Kernel X Y} {η : Kernel Y Z} {x : X} {s : Set Z}

theorem comp_null (x : X) (hs : MeasurableSet s) :
    (η ∘ₖ κ) x s = 0 ↔ (fun y ↦ η y s) =ᵐ[κ x] 0 := by
  rw [Kernel.comp_apply' _ _ _ hs, lintegral_eq_zero_iff]
  · exact Kernel.measurable_coe _ hs

theorem ae_null_of_comp_null (h : (η ∘ₖ κ) x s = 0) :
    (fun y => η y s) =ᵐ[κ x] 0 := by
  obtain ⟨t, hst, mt, ht⟩ := exists_measurable_superset_of_null h
  simp_rw [comp_null x mt] at ht
  rw [Filter.eventuallyLE_antisymm_iff]
  exact
    ⟨Filter.EventuallyLE.trans_eq
        (Filter.Eventually.of_forall fun x => measure_mono hst) ht,
      Filter.Eventually.of_forall fun x => zero_le _⟩

theorem ae_ae_of_ae_comp {p : Z → Prop} (h : ∀ᵐ z ∂(η ∘ₖ κ) x, p z) :
    ∀ᵐ y ∂κ x, ∀ᵐ z ∂η y, p z :=
  ae_null_of_comp_null h

lemma ae_comp_of_ae_ae {κ : Kernel X Y} {η : Kernel Y Z}
    {p : Z → Prop} (hp : MeasurableSet {z | p z})
    (h : ∀ᵐ y ∂κ x, ∀ᵐ z ∂η y, p z) :
    ∀ᵐ z ∂(η ∘ₖ κ) x, p z := by
  simp_rw [ae_iff] at h ⊢
  rw [comp_null]
  · exact h
  · exact hp.compl

lemma ae_comp_iff {p : Z → Prop} (hp : MeasurableSet {z | p z}) :
    (∀ᵐ z ∂(η ∘ₖ κ) x, p z) ↔ ∀ᵐ y ∂κ x, ∀ᵐ z ∂η y, p z :=
  ⟨fun h ↦ ae_ae_of_ae_comp h, fun h ↦ ae_comp_of_ae_ae hp h⟩

theorem ProbabilityTheory.Kernel.compProd_apply_prod (κ : Kernel X Y) [IsSFiniteKernel κ]
    (η : Kernel (X × Y) Z) [IsSFiniteKernel η]
    {s : Set Y} (hs : MeasurableSet s) {t : Set Z} (ht : MeasurableSet t) (x : X) :
    (κ ⊗ₖ η) x (s ×ˢ t) = ∫⁻ y in s, η (x, y) t ∂κ x := by
  rw [Kernel.compProd_apply (hs.prod ht), ← lintegral_indicator hs]
  congr with y
  by_cases hy : y ∈ s <;> simp [Set.indicator, hy]

theorem ProbabilityTheory.Kernel.map_map (κ : Kernel X Y) {f : Y → Z} (hf : Measurable f)
    {g : Z → T} (hg : Measurable g) :
    (κ.map f).map g = κ.map (g ∘ f) := by
  ext1 x
  rw [Kernel.map_apply _ hg, Kernel.map_apply _ hf, Measure.map_map hg hf,
    ← Kernel.map_apply _ (hg.comp hf)]

theorem ProbabilityTheory.Kernel.id_map {f : X → Y} (hf : Measurable f) :
    Kernel.id.map f = Kernel.deterministic f hf := by
  ext1 x
  rw [map_apply _ hf, id_apply, Measure.map_dirac hf, deterministic_apply]

theorem ProbabilityTheory.Kernel.lintegral_id {f : X → ℝ≥0∞} (x : X) (hf : Measurable f) :
    ∫⁻ y, f y ∂(@Kernel.id X inferInstance x) = f x := by
  rw [id_apply, lintegral_dirac' _ hf]

theorem ProbabilityTheory.Kernel.lintegral_id_prod (κ : Kernel X Y) [IsSFiniteKernel κ]
    {f : X × Y → ℝ≥0∞} (x : X) (hf : Measurable f) :
    ∫⁻ z, f z ∂((Kernel.id ×ₖ κ) x) = ∫⁻ y, f (x, y) ∂κ x := by
  rw [lintegral_prod _ _ _ hf, lintegral_id]
  exact hf.lintegral_prod_right'

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

theorem ProbabilityTheory.Kernel.map_deterministic {f : X → Y} (hf : Measurable f)
    {g : Y → Z} (hg : Measurable g) :
    (Kernel.deterministic f hf).map g = Kernel.deterministic (g ∘ f) (hg.comp hf) := by
  ext x s ms
  rw [Kernel.map_apply' _ hg _ ms, Kernel.deterministic_apply' _ _ (hg ms),
    Kernel.deterministic_apply' _ _ ms, preimage_indicator]
  rfl

lemma ProbabilityTheory.Kernel.eq_zero_of_isEmpty [IsEmpty Y] (κ : Kernel X Y) :
    κ = 0 := by
  ext1 x
  rw [Measure.eq_zero_of_isEmpty (κ x), zero_apply]

theorem ProbabilityTheory.Kernel.deterministic_prod_apply' {f : X → Y} (mf : Measurable f)
    (η : Kernel X Z) [IsSFiniteKernel η] (x : X)
    {s : Set (Y × Z)} (ms : MeasurableSet s) :
    ((Kernel.deterministic f mf) ×ₖ η) x s = η x {z | (f x, z) ∈ s} := by
  rw [Kernel.prod_apply' _ _ _ ms, Kernel.lintegral_deterministic']
  exact measurable_measure_prod_mk_left ms

theorem ProbabilityTheory.Kernel.id_prod_apply' (η : Kernel X Y) [IsSFiniteKernel η] (x : X)
    {s : Set (X × Y)} (ms : MeasurableSet s) :
    (Kernel.id ×ₖ η) x s = η x (Prod.mk x ⁻¹' s) := by
  rw [Kernel.id, Kernel.deterministic_prod_apply']
  rfl
  exact ms

theorem ProbabilityTheory.Kernel.prod_apply_symm' (κ : Kernel X Y) [IsSFiniteKernel κ]
    (η : Kernel X Z) [IsSFiniteKernel η]
    (x : X) {s : Set (Y × Z)} (hs : MeasurableSet s) :
    (κ ×ₖ η) x s = ∫⁻ z, κ x ((fun y ↦ (y, z)) ⁻¹' s) ∂η x := by
  rw [Kernel.prod_apply, Measure.prod_apply_symm hs]

theorem ProbabilityTheory.Kernel.prod_deterministic_apply' {f : X → Z} (mf : Measurable f)
    (η : Kernel X Y) [IsSFiniteKernel η] (x : X)
    {s : Set (Y × Z)} (ms : MeasurableSet s) :
    (η ×ₖ (Kernel.deterministic f mf)) x s = η x {y | (y, f x) ∈ s} := by
  rw [Kernel.prod_apply_symm' _ _ _ ms, Kernel.lintegral_deterministic']
  · rfl
  · exact measurable_measure_prod_mk_right ms

theorem ProbabilityTheory.Kernel.comp_apply'' (κ : Kernel X Y) (η : Kernel Y Z) (x : X) :
    (η ∘ₖ κ) x = (κ x).bind η := by
  ext s hs
  rw [Kernel.comp_apply' _ _ _ hs, Measure.bind_apply hs η.measurable]

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

/-- from #19639 -/
@[simp]
lemma snd_compProd (μ : Measure X) [SFinite μ] (κ : Kernel X Y) [IsSFiniteKernel κ] :
    (μ ⊗ₘ κ).snd = Measure.bind μ κ := by
  ext s hs
  rw [Measure.bind_apply hs κ.measurable, Measure.snd_apply hs, Measure.compProd_apply]
  · rfl
  · exact measurable_snd hs

lemma snd_compProd_kernel (κ : Kernel X Y) [IsSFiniteKernel κ] (η : Kernel Y Z)
    [IsSFiniteKernel η] (x : X) :
    ((κ x) ⊗ₘ η).snd = (η ∘ₖ κ) x := by
  rw [snd_compProd, Kernel.comp_apply'']

theorem ProbabilityTheory.Kernel.comap_const (μ : Measure Z) {f : X → Y} (hf : Measurable f) :
    Kernel.comap (Kernel.const Y μ) f hf = Kernel.const X μ := by
  ext1 x
  rw [Kernel.const_apply, Kernel.comap_apply, Kernel.const_apply]

lemma ProbabilityTheory.Kernel.comp_map (κ : Kernel X Y) (η : Kernel Z T) {f : Y → Z}
    (hf : Measurable f) :
    η ∘ₖ (κ.map f) = (η.comap f hf) ∘ₖ κ := by
  ext x s ms
  rw [comp_apply' _ _ _ ms, lintegral_map _ hf _ (η.measurable_coe ms), comp_apply' _ _ _ ms]
  simp_rw [comap_apply']

lemma ProbabilityTheory.Kernel.prod_comap (κ : Kernel Y Z) [IsSFiniteKernel κ]
    (η : Kernel Y T) [IsSFiniteKernel η] {f : X → Y} (hf : Measurable f) :
    (κ ×ₖ η).comap f hf = (κ.comap f hf) ×ₖ (η.comap f hf) := by
  ext1 x
  rw [comap_apply, prod_apply, prod_apply, comap_apply, comap_apply]

lemma ProbabilityTheory.Kernel.const_compProd_const (μ : Measure Y) [SFinite μ]
    (ν : Measure Z) [SFinite ν] :
    (const X μ) ⊗ₖ (const (X × Y) ν) = const X (μ.prod ν) := by
  ext x s ms
  simp_rw [compProd_apply ms, const_apply, Measure.prod_apply ms]
  rfl

lemma ProbabilityTheory.Kernel.prod_const_comp (κ : Kernel X Y) [IsSFiniteKernel κ]
    (η : Kernel Y Z) [IsSFiniteKernel η] (μ : Measure T) [SFinite μ] :
    (η ×ₖ (const Y μ)) ∘ₖ κ = (η ∘ₖ κ) ×ₖ (const X μ) := by
  ext x s ms
  simp_rw [comp_apply' _ _ _ ms, prod_apply' _ _ _ ms, const_apply]
  rw [lintegral_comp]
  exact measurable_measure_prod_mk_left ms

instance IsZeroOrMarkovKernel.compProd (κ : Kernel X Y) [IsZeroOrMarkovKernel κ]
    (η : Kernel (X × Y) Z) [IsZeroOrMarkovKernel η] : IsZeroOrMarkovKernel (κ ⊗ₖ η) := by
  obtain rfl | _ := eq_zero_or_isMarkovKernel κ <;> obtain rfl | _ := eq_zero_or_isMarkovKernel η
  all_goals simpa using by infer_instance

instance IsZeroOrMarkovKernel.comp (κ : Kernel X Y) [IsZeroOrMarkovKernel κ]
    (η : Kernel Y Z) [IsZeroOrMarkovKernel η] : IsZeroOrMarkovKernel (η ∘ₖ κ) := by
  obtain rfl | _ := eq_zero_or_isMarkovKernel κ <;> obtain rfl | _ := eq_zero_or_isMarkovKernel η
  all_goals simpa using by infer_instance

variable {E : Type*} [NormedAddCommGroup E]

theorem MeasureTheory.AEStronglyMeasurable.compProd {μ : Measure X} [SFinite μ]
    {κ : Kernel X Y} [IsMarkovKernel κ] {f : X → Y → E}
    (hf : AEStronglyMeasurable f.uncurry (μ ⊗ₘ κ)) :
    ∀ᵐ x ∂μ, AEStronglyMeasurable (f x) (κ x) := by
  rw [Measure.compProd] at hf
  apply compProd_mk_left at hf
  simpa using hf

lemma MeasureTheory.AEStronglyMeasurable.comp {f : Z → E}
    (hf : AEStronglyMeasurable f ((η ∘ₖ κ) x)) :
    ∀ᵐ y ∂κ x, AEStronglyMeasurable f (η y) := by
  filter_upwards [ae_ae_of_ae_comp hf.ae_eq_mk] with x' hx'
  exact hf.stronglyMeasurable_mk.aestronglyMeasurable.congr (ae_eq_symm hx')

theorem MeasureTheory.AEStronglyMeasurable.comp_mk_left [NormedSpace ℝ E]
    [IsSFiniteKernel η] [IsSFiniteKernel κ] {f : Z → E} {x : X}
    (hf : AEStronglyMeasurable f ((η ∘ₖ κ) x)) :
    AEStronglyMeasurable (fun y ↦ ∫ z, f z ∂η y) (κ x) := by
  rw [← Kernel.snd_compProd_prodMkLeft, Kernel.snd_apply] at hf
  replace hf := hf.comp_measurable measurable_snd
  exact hf.integral_kernel_compProd

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

theorem integrable_comp_iff {η : Kernel Y Z} [IsSFiniteKernel η]
    {κ : Kernel X Y} [IsSFiniteKernel κ] {x : X}
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

theorem MeasureTheory.Integrable.integral_comp {η : Kernel Y Z} [IsSFiniteKernel η] {κ : Kernel X Y}
    [IsSFiniteKernel κ] {x : X} {f : Z → E} (hf : Integrable f ((η ∘ₖ κ) x)) :
    Integrable (fun y ↦ ∫ z, f z ∂η y) (κ x) :=
  ((integrable_comp_iff hf.1).1 hf).2.mono' hf.1.comp_mk_left <|
    Filter.Eventually.of_forall fun _ ↦ norm_integral_le_integral_norm _

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

theorem setIntegral_eq {μ : Measure X} (f : X → E) {s : Set X} (hs : MeasurableSet s) :
    ∫ x in s, f x ∂μ = ∫ x, (s.indicator (fun _ ↦ (1 : ℝ)) x) • (f x) ∂μ := by
  simp_rw [← Set.indicator_one_smul_apply]
  rw [integral_indicator hs]

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

theorem MeasureTheory.Filtration.condExp_condExp {ι : Type*} [Preorder ι]
    (f : X → E) {μ : Measure X} (ℱ : @Filtration X ι _ inferInstance)
    {i j : ι} (hij : i ≤ j) [SigmaFinite (μ.trim (ℱ.le j))] :
    μ[μ[f|ℱ j]|ℱ i] =ᵐ[μ] μ[f|ℱ i] := condExp_condExp_of_le (ℱ.mono hij) (ℱ.le j)

end Measure

section Finset

lemma mem_Ioc_succ {n i : ℕ} : i ∈ Ioc n (n + 1) ↔ i = n + 1 := by
  rw [mem_Ioc]
  omega

lemma mem_Ioc_succ' {n : ℕ} (i : Ioc n (n + 1)) : i = ⟨n + 1, mem_Ioc_succ.2 rfl⟩ := by
  simp [← mem_Ioc_succ.1 i.2]

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
    a ∈ Iic a := mem_Iic.2 <| le_rfl

theorem Finset.Iic_union_Ioc_eq_Iic {α : Type*} [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α]
    {a b : α} (h : a ≤ b) : Iic a ∪ Ioc a b = Iic b := by
  rw [← coe_inj, coe_union, coe_Iic, coe_Iic, coe_Ioc, Set.Iic_union_Ioc_eq_Iic h]

theorem Finset.disjoint_Iic_Ioc {α : Type*} [Preorder α] [LocallyFiniteOrder α] [OrderBot α]
    {a b c : α} (h : a ≤ b) : Disjoint (Iic a) (Ioc b c) :=
  disjoint_left.2 fun _ hax hbcx ↦ (mem_Iic.1 hax).not_lt <| lt_of_le_of_lt h (mem_Ioc.1 hbcx).1

theorem restrict_updateFinset' {ι : Type*} [DecidableEq ι] {α : ι → Type*} {s t : Finset ι}
    (hst : s ⊆ t) (x : Π i, α i) (y : Π i : t, α i) :
    s.restrict (updateFinset x t y) = restrict₂ hst y := by
  ext i
  simp only [restrict, updateFinset, restrict₂]
  split_ifs with hi
  · rfl
  · exact (hi (hst i.2)).elim

theorem restrict_updateFinset {ι : Type*} [DecidableEq ι] {α : ι → Type*} {s : Finset ι}
    (x : Π i, α i) (y : Π i : s, α i) :
    s.restrict (updateFinset x s y) = y := by
  rw [restrict_updateFinset' subset_rfl]
  rfl

@[simp]
theorem updateFinset_restrict {ι : Type*} [DecidableEq ι] {α : ι → Type*} {s : Finset ι}
    (x : Π i, α i) : updateFinset x s (s.restrict x) = x := by
  ext i
  simp [updateFinset]

open Preorder

theorem frestrictLe_updateFinset' {ι : Type*} [DecidableEq ι] [Preorder ι] [LocallyFiniteOrderBot ι]
    {α : ι → Type*} {i j : ι} (hij : i ≤ j) (x : Π k, α k) (y : Π k : Iic j, α k) :
    frestrictLe i (updateFinset x _ y) = frestrictLe₂ hij y :=
  restrict_updateFinset' (Iic_subset_Iic.2 hij) ..

theorem frestrictLe_updateFinset {ι : Type*} [DecidableEq ι] [Preorder ι] [LocallyFiniteOrderBot ι]
    {α : ι → Type*} {i : ι} (x : Π j, α j) (y : Π j : Iic i, α j) :
    frestrictLe i (updateFinset x _ y) = y :=
  restrict_updateFinset ..

@[simp]
theorem updateFinset_frestrictLe {ι : Type*} [DecidableEq ι] [Preorder ι] [LocallyFiniteOrderBot ι]
    {α : ι → Type*} {i : ι} (x : Π i, α i) : updateFinset x _ (frestrictLe i x) = x := by
  simp [frestrictLe]

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

theorem prod_Ioc {M : Type*} [CommMonoid M] {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    (f : (Ioc a c) → M) :
    (∏ i : Ioc a b, f (Set.inclusion (Ioc_subset_Ioc_right hbc) i)) *
      (∏ i : Ioc b c, f (Set.inclusion (Ioc_subset_Ioc_left hab) i)) = (∏ i : Ioc a c, f i) := by
  have : Ioc a b ∪ Ioc b c = Ioc a c := by simp [hab, hbc]
  rw [← prod_congr' this, ← prod_union']
  rw [← disjoint_coe, coe_Ioc, coe_Ioc, Set.Ioc_disjoint_Ioc, min_eq_left hbc, max_eq_right hab]

theorem prod_Iic {M : Type*} [CommMonoid M] {a b : ℕ} (hab : a ≤ b)
    (f : (Iic b) → M) :
    (∏ i : Iic a, f (Set.inclusion (Iic_subset_Iic.2 hab) i)) *
      (∏ i : Ioc a b, f (Set.inclusion Ioc_subset_Iic_self i)) = (∏ i, f i) := by
  have : Iic a ∪ Ioc a b = Iic b := by
    rw [← Finset.coe_inj, coe_union, coe_Iic, coe_Ioc, coe_Iic]
    simp [hab]
  rw [← prod_congr' this, ← prod_union']
  rw [← disjoint_coe, coe_Iic, coe_Ioc]
  exact Set.Iic_disjoint_Ioc le_rfl

end Product
