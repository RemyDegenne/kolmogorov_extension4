/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import KolmogorovExtension4.compProdNat
import KolmogorovExtension4.Projective
import KolmogorovExtension4.DependsOn
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import KolmogorovExtension4.KolmogorovExtension

open MeasureTheory ProbabilityTheory Finset ENNReal Filter Topology Function MeasurableSpace

variable {X : ℕ → Type*} [Nonempty (X 0)] [∀ n, MeasurableSpace (X n)]
variable (κ : (k : ℕ) → Kernel ((i : Iic k) → X i) (X (k + 1)))
variable [∀ k, IsMarkovKernel (κ k)]

/-- To check that a measure `ν` is the projective limit of a projective family of measures indexed
by `Finset ℕ`, it is enough to check on intervals of the form `Iic n`, where `n` is larger than
a given integer. -/
theorem isProjectiveLimit_nat_iff' (μ : (I : Finset ℕ) → Measure ((i : I) → X i))
    (hμ : IsProjectiveMeasureFamily μ) (ν : Measure ((n : ℕ) → X n)) (a : ℕ) :
    IsProjectiveLimit ν μ ↔ ∀ n ≥ a, ν.map (fprojNat n) = μ (Iic n) := by
  refine ⟨fun h n _ ↦ h (Iic n), fun h I ↦ ?_⟩
  rw [← fprojSubset_comp_fproj (I.sub_Iic.trans (Iic_subset_Iic.2 (le_max_left (I.sup id) a))),
    ← Measure.map_map (measurable_fprojSubset _) (measurable_fprojNat _),
    h (max (I.sup id) a) (le_max_right _ _)]
  exact (hμ _ _ _).symm

/-- To check that a measure `ν` is the projective limit of a projective family of measures indexed
by `Finset ℕ`, it is enough to check on intervals of the form `Iic n`. -/
theorem isProjectiveLimit_nat_iff (μ : (I : Finset ℕ) → Measure ((i : I) → X i))
    (hμ : IsProjectiveMeasureFamily μ) (ν : Measure ((n : ℕ) → X n)) :
    IsProjectiveLimit ν μ ↔ ∀ n, ν.map (fprojNat n) = μ (Iic n) := by
  rw [isProjectiveLimit_nat_iff' _ hμ _ 0]
  simp

/-- Given a family of measures `μ : (n : ℕ) → Measure ((i : Iic n) → X i)`, we can define a family
of measures indexed by `Finset ℕ` by projecting the measures. -/
noncomputable def inducedFamily (μ : (n : ℕ) → Measure ((i : Iic n) → X i)) :
    (S : Finset ℕ) → Measure ((k : S) → X k) :=
  fun S ↦ (μ (S.sup id)).map (fprojSubset S.sub_Iic)

instance (μ : (n : ℕ) → Measure ((i : Iic n) → X i)) [∀ n, IsFiniteMeasure (μ n)] (I : Finset ℕ) :
    IsFiniteMeasure (inducedFamily μ I) := by
  rw [inducedFamily]
  infer_instance

instance (μ : (n : ℕ) → Measure ((i : Iic n) → X i)) [∀ n, IsFiniteMeasure (μ n)] (I : Finset ℕ) :
     IsFiniteMeasure (inducedFamily μ I) := by
   rw [inducedFamily]
   infer_instance

private lemma Iic_pi_eq {a b : ℕ} (h : a = b) :
    ((i : Iic a) → X i) = ((i : Iic b) → X i) := by cases h; rfl

private lemma measure_cast {a b : ℕ} (h : a = b) (μ : (n : ℕ) → Measure ((i : Iic n) → X i)) :
    (μ a).map (cast (Iic_pi_eq h)) = μ b := by
  subst h
  exact Measure.map_id

private lemma cast_pi {s t : Set ℕ} (h : s = t) (h' : ((i : s) → X i) = ((i : t) → X i))
    (x : (i : s) → X i) (i : t) :
    cast h' x i = x ⟨i.1, h.symm ▸ i.2⟩ := by
  subst h
  rfl

/-- Given a family of measures `μ : (n : ℕ) → Measure ((i : Iic n) → X i)`, the induced family
equals `μ` over the intervals `Iic n`. -/
theorem inducedFamily_Iic (μ : (n : ℕ) → Measure ((i : Iic n) → X i)) (n : ℕ) :
    inducedFamily μ (Iic n) = μ n := by
  rw [inducedFamily, ← measure_cast (sup_Iic n) μ]
  congr with x i
  rw [fprojSubset, cast_pi _ (Iic_pi_eq (sup_Iic n)) x i]
  rw [sup_Iic n]

/-- Given a family of measures `μ : (n : ℕ) → Measure ((i : Iic n) → X i)`, the induced family
will be projective only if `μ` is projective, in the sense that if `a ≤ b`, then projecting
`μ b` gives `μ a`. -/
theorem isProjectiveMeasureFamily_inducedFamily (μ : (n : ℕ) → Measure ((i : Iic n) → X i))
    (h : ∀ a b : ℕ, ∀ hab : a ≤ b, (μ b).map (fprojNat_le hab) = μ a) :
    IsProjectiveMeasureFamily (inducedFamily μ) := by
  intro I J hJI
  have sls : J.sup id ≤ I.sup id := sup_mono hJI
  simp only [inducedFamily]
  rw [Measure.map_map]
  conv_rhs => enter [1]; change fprojSubset (hJI.trans I.sub_Iic)
  rw [← fprojSubset_comp_fprojSubset J.sub_Iic (Iic_subset_Iic.2 sls), ← Measure.map_map,
    h (J.sup id) (I.sup id) sls]
  all_goals exact measurable_fprojSubset _

open Kernel

theorem partialKernel_proj_apply {n : ℕ} (x : (i : Iic n) → X i) (a b : ℕ) (hab : a ≤ b) :
    (partialKernel κ n b x).map (fprojNat_le hab) = partialKernel κ n a x := by
  rw [← partialKernel_proj _ _ hab, Kernel.map_apply]

/-- Given a family of kernels `κ : (n : ℕ) → Kernel ((i : Iic n) → X i) (X (n + 1))`, and the
trajectory up to time `n` we can construct an additive content over cylinders. It corresponds
to composing the kernels by starting at time `n + 1`. -/
noncomputable def ionescuTulceaContent {n : ℕ} (x : (i : Iic n) → X i) : AddContent (cylinders X) :=
  kolContent (isProjectiveMeasureFamily_inducedFamily _ (partialKernel_proj_apply κ x))

private lemma heq_measurableSpace_Iic_pi {a b : ℕ} (h : a = b) :
    HEq (inferInstance : MeasurableSpace ((i : Iic a) → X i))
    (inferInstance : MeasurableSpace ((i : Iic b) → X i)) := by cases h; rfl

/-- The `ionescuTulceaContent κ x` of a cylinder indexed by first coordinates is given by
`partialKernel`. -/
theorem ionescuTulceaContent_cylinder {a b : ℕ} (x : (i : Iic a) → X i)
    {S : Set ((i : Iic b) → X i)} (mS : MeasurableSet S) :
    ionescuTulceaContent κ x (cylinder _ S) = partialKernel κ a b x S := by
  rw [ionescuTulceaContent, kolContent_cylinder _ mS, inducedFamily_Iic]

/-- This function computes the integral of a function `f` against `partialKernel`,
and allows to view it as a function depending on all the variables. -/
noncomputable def lmarginalPartialKernel (a b : ℕ) (f : ((n : ℕ) → X n) → ℝ≥0∞)
    (x : (n : ℕ) → X n) : ℝ≥0∞ :=
  ∫⁻ z : (i : Iic b) → X i, f (updateFinset x _ z) ∂(partialKernel κ a b (fprojNat a x))

/-- If `a < b`, then integrating `f` against the `partialKernel κ a b` is the same as integrating
  against `kerNat a b`. -/
theorem lmarginalPartialKernel_lt {a b : ℕ} (hab : a < b) {f : ((n : ℕ) → X n) → ℝ≥0∞}
    (mf : Measurable f) (x : (n : ℕ) → X n) :
    lmarginalPartialKernel κ a b f x =
      ∫⁻ y : (i : Ioc a b) → X i, f (updateFinset x _ y) ∂kerNat κ a b (fprojNat a x) := by
  rw [lmarginalPartialKernel, partialKernel, dif_pos hab, Kernel.lintegral_map,
    Kernel.lintegral_prod, Kernel.lintegral_deterministic']
  · congrm ∫⁻ _, f (fun i ↦ ?_) ∂_
    simp only [updateFinset, mem_Iic, el, id_eq, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, mem_Ioc]
    split_ifs <;> try rfl
    all_goals omega
  · apply Measurable.lintegral_prod_right'
      (f := fun p ↦ f (updateFinset x (Iic b) (el a b hab.le p)))
    exact mf.comp <| measurable_updateFinset.comp (el a b hab.le).measurable
  · exact mf.comp <| measurable_updateFinset.comp (el a b hab.le).measurable
  · exact mf.comp measurable_updateFinset

/-- If `b ≤ a`, then integrating `f` against the `partialKernel κ a b` does nothing. -/
theorem lmarginalPartialKernel_le {a b : ℕ} (hba : b ≤ a)
    {f : ((n : ℕ) → X n) → ℝ≥0∞} (mf : Measurable f) : lmarginalPartialKernel κ a b f = f := by
  ext x
  rw [lmarginalPartialKernel, partialKernel, dif_neg (not_lt.2 hba),
    Kernel.lintegral_deterministic']
  · congr with i
    simp [updateFinset]
  · exact mf.comp measurable_updateFinset

/-- The `ionescuTulceaContent` of a cylinder is equal to the integral of its indicator function. -/
theorem ionescuTulceaContent_eq_lmarginalPartialKernel {N : ℕ} {S : Set ((i : Iic N) → X i)}
    (mS : MeasurableSet S) (x : (n : ℕ) → X n) (n : ℕ) :
    ionescuTulceaContent κ (fprojNat n x) (cylinder _ S) =
    lmarginalPartialKernel κ n N ((cylinder _ S).indicator 1) x := by
  rw [ionescuTulceaContent_cylinder _ _ mS, ← lintegral_indicator_one mS, lmarginalPartialKernel]
  congr with y
  apply indicator_const_eq
  rw [mem_cylinder]
  congrm (fun i ↦ ?_) ∈ S
  simp [updateFinset, i.2]

theorem lmarginalPartialKernel_mono (a b : ℕ) {f g : ((n : ℕ) → X n) → ℝ≥0∞} (hfg : f ≤ g)
    (x : (n : ℕ) → X n) : lmarginalPartialKernel κ a b f x ≤ lmarginalPartialKernel κ a b g x :=
  lintegral_mono fun _ ↦ hfg _

theorem measurable_lmarginalPartialKernel (a b : ℕ) {f : ((n : ℕ) → X n) → ℝ≥0∞}
    (hf : Measurable f) : Measurable (lmarginalPartialKernel κ a b f) := by
  unfold lmarginalPartialKernel
  let g : ((i : Iic b) → X i) × ((n : ℕ) → X n) → ℝ≥0∞ :=
    fun c ↦ f (updateFinset c.2 _ c.1)
  let η : Kernel ((n : ℕ) → X n) ((i : Iic b) → X i) :=
    Kernel.comap (partialKernel κ a b) (fprojNat a) (measurable_fprojNat _)
  change Measurable fun x ↦ ∫⁻ z : (i : Iic b) → X i, g (z, x) ∂η x
  refine Measurable.lintegral_kernel_prod_left' <| hf.comp ?_
  simp only [updateFinset, measurable_pi_iff]
  intro i
  by_cases h : i ∈ Iic b <;> simp [h]
  · exact (measurable_pi_apply _).comp <| measurable_fst
  · exact measurable_snd.eval

theorem DependsOn.lmarginalPartialKernel_eq {a b : ℕ} (c : ℕ) {f : ((n : ℕ) → X n) → ℝ≥0∞}
    (mf : Measurable f) (hf : DependsOn f (Iic a)) (hab : a ≤ b) :
    lmarginalPartialKernel κ b c f = f := by
  rcases le_or_lt c b with hcb | hbc
  · exact lmarginalPartialKernel_le κ hcb mf
  · ext x
    have := isMarkovKernel_kerNat κ hbc
    rw [lmarginalPartialKernel_lt κ hbc mf, ← mul_one (f x),
      ← measure_univ (μ := kerNat κ b c (fprojNat b x)), ← MeasureTheory.lintegral_const]
    refine lintegral_congr fun y ↦ hf fun i hi ↦ ?_
    simp only [updateFinset, mem_Iic, el, id_eq, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk,
      dite_eq_right_iff, dite_eq_left_iff, not_le]
    intro h
    rw [mem_Ioc] at h
    rw [mem_coe, mem_Iic] at hi
    omega

theorem dependsOn_lmarginalPartialKernel (a : ℕ) {b : ℕ} {f : ((n : ℕ) → X n) → ℝ≥0∞}
    (hf : DependsOn f (Iic b)) (mf : Measurable f) :
    DependsOn (lmarginalPartialKernel κ a b f) (Iic a) := by
  intro x y hxy
  rcases le_or_lt b a with hba | hab
  · rw [lmarginalPartialKernel_le κ hba mf]
    exact hf fun i hi ↦ hxy i (Iic_subset_Iic.2 hba hi)
  · rw [lmarginalPartialKernel_lt _ hab mf, lmarginalPartialKernel_lt _ hab mf]
    congrm ∫⁻ z : _, ?_ ∂kerNat κ a b (fun i ↦ ?_)
    · exact hxy i.1 i.2
    · refine dependsOn_updateFinset hf _ _ ?_
      rwa [← coe_sdiff, Iic_sdiff_Ioc_same hab.le]

theorem lmarginalPartialKernel_self {a b c : ℕ} (hab : a < b) (hbc : b < c)
    {f : ((n : ℕ) → X n) → ℝ≥0∞} (hf : Measurable f) :
    lmarginalPartialKernel κ a b (lmarginalPartialKernel κ b c f) =
      lmarginalPartialKernel κ a c f := by
  ext x
  rw [lmarginalPartialKernel_lt _ (hab.trans hbc) hf, lmarginalPartialKernel_lt _ hab]
  simp_rw [lmarginalPartialKernel_lt _ hbc hf]
  rw [← compProdNat_kerNat _ hab hbc, compProdNat_eq _ _  hab hbc, Kernel.map_apply,
    MeasureTheory.lintegral_map _ (er ..).measurable, Kernel.lintegral_compProd]
  · congrm ∫⁻ _, ∫⁻ _, f fun i ↦ ?_ ∂(?_) ∂_
    · rw [split_eq_comap, Kernel.comap_apply]
      congr with i
      simp only [fproj_def, updateFinset, mem_Ioc, el, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk]
      split_ifs with h1 h2 h3 <;> try rfl
      · omega
      · have := mem_Iic.1 i.2
        omega
    · simp only [updateFinset, mem_Ioc, er, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk]
      split_ifs <;> try omega
      rfl; rfl; rfl
  · exact hf.comp <| measurable_updateFinset.comp (er ..).measurable
  · exact hf.comp <| measurable_updateFinset
  · exact measurable_lmarginalPartialKernel _ _ _ hf

theorem update_updateFinset_eq (x z : (n : ℕ) → X n) {m : ℕ} :
    update (updateFinset x (Iic m) (fprojNat m z)) (m + 1) (z (m + 1)) =
    updateFinset x (Iic (m + 1)) (fprojNat (m + 1) z) := by
  ext i
  simp only [update, updateFinset, mem_Iic, dite_eq_ite]
  split_ifs with h1 h2 h3 h4 h5 <;> try omega
  cases h1; rfl; rfl; rfl

/-- This is an auxiliary result for `ionescuTulceaContent_tendsto_zero`.
Consider `f` a sequence of bounded measurable
functions such that `f n` depends only on the first coordinates up to `N n`.
Assume that when integrating `f n` against `partialKernel (k + 1) (N n)`,
one gets a non-increasing sequence of functions wich converges to `l`.
Assume then that there exists `ε` and `y : (n : Iic k) → X n` such that
when integrating `f n` against `partialKernel k (N n)`, you get something at least
`ε` for all. Then there exists `z` such that this remains true when integrating
`f` against `partialKernel (k + 1) (N n) (update y (k + 1) z)`. -/
theorem le_lmarginalPartialKernel_succ {f : ℕ → ((n : ℕ) → X n) → ℝ≥0∞} {N : ℕ → ℕ}
    (hcte : ∀ n, DependsOn (f n) (Iic (N n))) (mf : ∀ n, Measurable (f n))
    {bound : ℝ≥0∞} (fin_bound : bound ≠ ∞) (le_bound : ∀ n x, f n x ≤ bound) {k : ℕ}
    (anti : ∀ x, Antitone (fun n ↦ lmarginalPartialKernel κ (k + 1) (N n) (f n) x))
    {l : ((n : ℕ) → X n) → ℝ≥0∞}
    (htendsto : ∀ x, Tendsto (fun n ↦ lmarginalPartialKernel κ (k + 1) (N n) (f n) x)
      atTop (𝓝 (l x)))
    (ε : ℝ≥0∞) (y : (n : Iic k) → X n)
    (hpos : ∀ x n, ε ≤ lmarginalPartialKernel κ k (N n) (f n) (updateFinset x _ y)) :
    ∃ z, ∀ x n, ε ≤ lmarginalPartialKernel κ (k + 1) (N n) (f n)
      (Function.update (updateFinset x _ y) (k + 1) z) := by
  have _ n : Nonempty (X n) := by
    refine Nat.case_strong_induction_on (p := fun n ↦ Nonempty (X n)) _ inferInstance
      fun n hind ↦ ?_
    have : Nonempty ((i : Iic n) → X i) :=
      Nonempty.intro fun i ↦ @Classical.ofNonempty _ (hind i.1 (mem_Iic.1 i.2))
    exact ProbabilityMeasure.nonempty ⟨κ n Classical.ofNonempty, inferInstance⟩
  let F : ℕ → ((n : ℕ) → X n) → ℝ≥0∞ := fun n ↦ lmarginalPartialKernel κ (k + 1) (N n) (f n)
  -- `Fₙ` converges to `l` by hypothesis.
  have tendstoF x : Tendsto (F · x) atTop (𝓝 (l x)) := htendsto x
  -- Integrating `fₙ` between time `k` and `Nₙ` is the same as integrating
  -- `Fₙ` between time `k` and time `k + 1` variable.
  have f_eq x n : lmarginalPartialKernel κ k (N n) (f n) x =
    lmarginalPartialKernel κ k (k + 1) (F n) x := by
    simp_rw [F]
    rcases lt_trichotomy (k + 1) (N n) with h | h | h
    · rw [← lmarginalPartialKernel_self κ k.lt_succ_self h (mf n)]
    · rw [← h, lmarginalPartialKernel_le _ (le_refl (k + 1)) (mf n)]
    · rw [lmarginalPartialKernel_le _ (by omega) (mf n),
        (hcte n).lmarginalPartialKernel_eq _ _ (mf n) (by omega),
        (hcte n).lmarginalPartialKernel_eq _ _ (mf n) (by omega)]
  -- `F` is also a bounded sequence.
  have F_le n x : F n x ≤ bound := by
    simp_rw [F, lmarginalPartialKernel]
    rw [← mul_one bound, ← measure_univ (μ := partialKernel κ (k + 1) (N n) (fprojNat (k + 1) x)),
        ← MeasureTheory.lintegral_const]
    exact lintegral_mono fun _ ↦ le_bound _ _
  -- By dominated convergence, the integral of `fₙ` between time `k` and time `N n` converges
  -- to the integral of `l` between time `k` and time `k + 1`.
  have tendsto_int x : Tendsto (fun n ↦ lmarginalPartialKernel κ k (N n) (f n) x) atTop
      (𝓝 (lmarginalPartialKernel κ k (k + 1) l x)) := by
    simp_rw [f_eq, lmarginalPartialKernel]
    exact tendsto_lintegral_of_dominated_convergence (fun _ ↦ bound)
      (fun n ↦ (measurable_lmarginalPartialKernel _ _ _ (mf n)).comp measurable_updateFinset)
      (fun n ↦ eventually_of_forall <| fun y ↦ F_le n _)
      (by simp [fin_bound]) (eventually_of_forall (fun _ ↦ tendstoF _))
  -- By hypothesis, we have `ε ≤ lmarginalPartialKernel κ k (k + 1) (F n) (updateFinset x _ y)`,
  -- so this is also true for `l`.
  have ε_le_lint x : ε ≤ lmarginalPartialKernel κ k (k + 1) l (updateFinset x _ y) :=
    ge_of_tendsto (tendsto_int _) (by simp [hpos])
  let x_ : (n : ℕ) → X n := Classical.ofNonempty
  -- We now have that the integral of `l` with respect to a probability measure is greater than `ε`,
  -- therefore there exists `x'` such that `ε ≤ l(y, x')`.
  obtain ⟨x', hx'⟩ : ∃ x', ε ≤ l (Function.update (updateFinset x_ _ y) (k + 1) x') := by
    have aux : ∫⁻ (a : X (k + 1)),
        l (update (updateFinset x_ _ y) (k + 1) a) ∂(κ k y) ≠ ∞ := by
      apply ne_top_of_le_ne_top fin_bound
      rw [← mul_one bound, ← measure_univ (μ := κ k y), ← MeasureTheory.lintegral_const]
      exact lintegral_mono <| fun y ↦ le_of_tendsto' (tendstoF _) <| fun _ ↦ F_le _ _
    rcases exists_lintegral_le aux with ⟨x', hx'⟩
    refine ⟨x', ?_⟩
    calc
      ε ≤ ∫⁻ (z : X (k + 1)),
          l (update (updateFinset x_ _ y) (k + 1) z) ∂(κ k y) := by
          convert ε_le_lint x_
          rw [lmarginalPartialKernel_lt _ k.lt_succ_self, kerNat_succ, Kernel.map_apply,
            lintegral_map_equiv]
          · congrm ∫⁻ z, (l fun i ↦ ?_) ∂κ k (fun i ↦ ?_)
            · simp [i.2, updateFinset]
            · simp [update, updateFinset, e]
          · refine ENNReal.measurable_of_tendsto ?_ (tendsto_pi_nhds.2 htendsto)
            exact fun n ↦ measurable_lmarginalPartialKernel _ _ _ (mf n)
      _ ≤ l (update (updateFinset x_ _ y) (k + 1) x') := hx'
  refine ⟨x', fun x n ↦ ?_⟩
  -- As `F` is a non-increasing sequence, we have `ε ≤ Fₙ(y, x')` for any `n`.
  have := le_trans hx' ((anti _).le_of_tendsto (tendstoF _) n)
  -- This part below is just to say that this is true for any `x : (i : ι) → X i`,
  -- as `Fₙ` technically depends on all the variables, but really depends only on the first `k + 1`.
  convert this using 1
  refine dependsOn_lmarginalPartialKernel _ _ (hcte n) (mf n) fun i hi ↦ ?_
  simp only [update, updateFinset]
  split_ifs with h1 h2 <;> try rfl
  rw [mem_coe, mem_Iic] at *
  omega

/-- The cylinders of a product space indexed by `ℕ` can be seen as depending on the first
corrdinates. -/
theorem cylinders_nat :
    cylinders X = ⋃ (N) (S) (_ : MeasurableSet S), {cylinder (Iic N) S} := by
  ext s
  simp only [mem_cylinders, exists_prop, Set.mem_iUnion, mem_singleton]
  refine ⟨?_, fun ⟨N, S, mS, s_eq⟩ ↦ ⟨Iic N, S, mS, s_eq⟩⟩
  rintro ⟨t, S, mS, rfl⟩
  refine ⟨t.sup id, fprojSubset t.sub_Iic ⁻¹' S, measurable_fprojSubset _ mS, ?_⟩
  unfold cylinder
  rw [← Set.preimage_comp]
  rfl

/-- This function takes a trajectory up to time `p` and a way of building the next step of the
trajectory and returns a whole trajectory whose first steps correspond
to the initial ones provided. -/
def iterate_induction {p : ℕ} (x₀ : (i : Iic p) → X i)
    (ind : (k : ℕ) → ((n : Iic k) → X n) → X (k + 1)) :
    (k : ℕ) → X k := fun k ↦ by
  cases k with
  | zero => exact x₀ ⟨0, mem_Iic.2 <| zero_le p⟩
  | succ q =>
    exact if hq : q + 1 ≤ p
      then x₀ ⟨q + 1, mem_Iic.2 hq⟩
      else ind q (fun i ↦ iterate_induction x₀ ind i)
  decreasing_by
    have := mem_Iic.1 i.2
    rename_i h
    rw [← Nat.lt_succ, Nat.succ_eq_add_one, ← h] at this
    exact this

theorem iterate_induction_le {p : ℕ} (x₀ : (i : Iic p) → X i)
    (ind : (k : ℕ) → ((n : Iic k) → X n) → X (k + 1)) (k : Iic p) :
    iterate_induction x₀ ind k = x₀ k := by
  rcases k with ⟨i, hi⟩
  cases i with
  | zero =>
    rw [iterate_induction, Nat.casesAuxOn_zero]
  | succ j =>
    rw [iterate_induction, Nat.casesAuxOn_succ]
    simp [mem_Iic.1 hi]

/-- The indicator of a cylinder only depends on the variables whose the cylinder depends on. -/
theorem dependsOn_cylinder_indicator {ι : Type*} {α : ι → Type*} {I : Finset ι}
    (S : Set ((i : I) → α i)) :
    DependsOn ((cylinder I S).indicator (1 : ((i : ι) → α i) → ℝ≥0∞)) I :=
  fun x y hxy ↦ indicator_const_eq _ (by simp [hxy])

theorem proj_updateFinset {n : ℕ} (x : (n : ℕ) → X n) (y : (i : Iic n) → X i) :
    fprojNat n (updateFinset x _ y) = y := by
  ext i
  simp [updateFinset, i.2]

/-- This is the key theorem to prove the existence of the `ionescuTulceaKernel`:
the `ionescuTulceaContent` of a decresaing sequence of cylinders with empty intersection
converges to `0`.
This implies the `σ`-additivity of `ionescuTulceaContent`
(see `sigma_additive_addContent_of_tendsto_zero`), which allows to extend it to the
`σ`-algebra by Carathéodory's theorem. -/
theorem ionescuTulceaContent_tendsto_zero (A : ℕ → Set ((n : ℕ) → X n))
    (A_mem : ∀ n, A n ∈ cylinders X) (A_anti : Antitone A) (A_inter : ⋂ n, A n = ∅)
    {p : ℕ} (x₀ : (i : Iic p) → X i) :
    Tendsto (fun n ↦ ionescuTulceaContent κ x₀ (A n)) atTop (𝓝 0) := by
  have _ n : Nonempty (X n) := by
    refine Nat.case_strong_induction_on (p := fun n ↦ Nonempty (X n)) _ inferInstance
      fun n hind ↦ ?_
    have : Nonempty ((i : Iic n) → X i) :=
      Nonempty.intro fun i ↦ @Classical.ofNonempty _ (hind i.1 (mem_Iic.1 i.2))
    exact ProbabilityMeasure.nonempty ⟨κ n Classical.ofNonempty, inferInstance⟩
  -- `Aₙ` is a cylinder, it can be written `cylinder (Iic (N n)) Sₙ`.
  have A_cyl n : ∃ N S, MeasurableSet S ∧ A n = cylinder (Iic N) S := by
    simpa [cylinders_nat] using A_mem n
  choose N S mS A_eq using A_cyl
  -- We write `χₙ` for the indicator function of `Aₙ`.
  let χ n := (A n).indicator (1 : ((n : ℕ) → X n) → ℝ≥0∞)
  -- `χₙ` is measurable.
  have mχ n : Measurable (χ n) := by
    simp_rw [χ, A_eq]
    exact (measurable_indicator_const_iff 1).2 <| measurableSet_cylinder _ _ (mS n)
  -- `χₙ` only depends on the first coordinates.
  have χ_dep n : DependsOn (χ n) (Iic (N n)) := by
    simp_rw [χ, A_eq]
    exact dependsOn_cylinder_indicator _
  -- Therefore its integral against `partialKernel κ k (N n)` is constant.
  have lma_const x y n :
      lmarginalPartialKernel κ p (N n) (χ n) (updateFinset x _ x₀) =
      lmarginalPartialKernel κ p (N n) (χ n) (updateFinset y _ x₀) := by
    apply dependsOn_lmarginalPartialKernel κ p (χ_dep n) (mχ n)
    intro i hi
    rw [mem_coe, mem_Iic] at hi
    simp [updateFinset, hi]
  -- As `(Aₙ)` is non-increasing, so is `(χₙ)`.
  have χ_anti : Antitone χ := by
    intro m n hmn y
    apply Set.indicator_le
    exact fun a ha ↦ by simp [χ, A_anti hmn ha]
  -- Integrating `χₙ` further than the last coordinate it depends on does nothing.
  -- This is used to then show that the integral of `χₙ` from time `k` is non-increasing.
  have lma_inv k M n (h : N n ≤ M) :
      lmarginalPartialKernel κ k M (χ n) = lmarginalPartialKernel κ k (N n) (χ n) := by
    refine Nat.le_induction rfl ?_ M h
    intro K hK hind
    rw [← hind]
    rcases lt_trichotomy k K with hkK | hkK | hkK
    · rw [← lmarginalPartialKernel_self κ hkK K.lt_succ_self (mχ n),
        (χ_dep n).lmarginalPartialKernel_eq _ _ (mχ n) hK]
    · rw [hkK, (χ_dep n).lmarginalPartialKernel_eq _ _ (mχ n) hK,
        (χ_dep n).lmarginalPartialKernel_eq _ _ (mχ n) hK]
    · rw [lmarginalPartialKernel_le _ hkK.le (mχ n),
        lmarginalPartialKernel_le _ (Nat.succ_le.2 hkK) (mχ n)]
  -- the integral of `χₙ` from time `k` is non-increasing.
  have anti_lma k x : Antitone fun n ↦ lmarginalPartialKernel κ k (N n) (χ n) x := by
    intro m n hmn
    simp only
    rw [← lma_inv k ((N n).max (N m)) n (le_max_left _ _),
      ← lma_inv k ((N n).max (N m)) m (le_max_right _ _)]
    exact lmarginalPartialKernel_mono _ _ _ (χ_anti hmn) _
  -- Therefore it converges to some function `lₖ`.
  have this k x : ∃ l,
      Tendsto (fun n ↦ lmarginalPartialKernel κ k (N n) (χ n) x) atTop (𝓝 l) := by
    rcases tendsto_of_antitone <| anti_lma k x with h | h
    · rw [OrderBot.atBot_eq] at h
      exact ⟨0, h.mono_right <| pure_le_nhds 0⟩
    · exact h
  choose l hl using this
  -- `lₚ` is constant because it is the limit of constant functions: we call it `ε`.
  have l_const x y : l p (updateFinset x _ x₀) = l p (updateFinset y _ x₀) := by
    have := hl p (updateFinset x _ x₀)
    simp_rw [lma_const x y] at this
    exact tendsto_nhds_unique this (hl p _)
  obtain ⟨ε, hε⟩ : ∃ ε, ∀ x, l p (updateFinset x _ x₀) = ε :=
      ⟨l p (updateFinset Classical.ofNonempty _ x₀), fun x ↦ l_const _ _⟩
  -- As the sequence is decreasing, `ε ≤ ∫ χₙ`.
  have hpos x n : ε ≤ lmarginalPartialKernel κ p (N n) (χ n) (updateFinset x _ x₀) :=
    hε x ▸ ((anti_lma p _).le_of_tendsto (hl p _)) n
  -- Also, the indicators are bounded by `1`.
  have χ_le n x : χ n x ≤ 1 := by
    apply Set.indicator_le
    simp
  -- We have all the conditions to apply ``. This allows us to recursively
  -- build a sequence `z` with the following property: for any `k ≥ p` and `n`,
  -- integrating `χ n` from time `k` to time `N n` with the trajectory up to `k` being equal to `z`
  -- gives something greater than `ε`.
  choose! ind hind using
    fun k y h ↦ le_lmarginalPartialKernel_succ κ χ_dep mχ (by norm_num : (1 : ℝ≥0∞) ≠ ∞)
      χ_le (anti_lma (k + 1)) (hl (k + 1)) ε y h
  let z := iterate_induction x₀ ind
  have imp k (hk : p ≤ k) : ∀ x n,
      ε ≤ lmarginalPartialKernel κ k (N n) (χ n) (updateFinset x (Iic k) (fprojNat k z)) := by
    refine Nat.le_induction ?_ ?_ k hk
    · intro x n
      convert hpos x n
      ext i
      simp only [fproj_def, z]
      apply iterate_induction_le
    · intro k hn h x n
      rw [← update_updateFinset_eq]
      convert hind k (fun i ↦ z i.1) h x n
      simp_rw [z]
      rw [iterate_induction, Nat.casesAuxOn_succ]
      simp [Nat.lt_succ.2 hn]
  -- We now want to prove that the integral of `χₙ`, which is equal to the `ionescuTulceaContent`
  -- of `Aₙ`, converges to `0`.
  have aux x n : ionescuTulceaContent κ x₀ (A n) =
      lmarginalPartialKernel κ p (N n) (χ n) (updateFinset x _ x₀) := by
    simp_rw [χ, A_eq]
    nth_rw 1 [← proj_updateFinset x x₀]
    exact ionescuTulceaContent_eq_lmarginalPartialKernel κ (mS n) (updateFinset x _ x₀) p
  simp_rw [aux Classical.ofNonempty]
  convert hl p (updateFinset Classical.ofNonempty _ x₀)
  rw [hε]
  by_contra!
  -- Which means that we want to prove that `ε = 0`. But if `ε > 0`, then for any `n`,
  -- choosing `k > Nₙ` we get `ε ≤ χₙ(z₀, ..., z_{Nₙ})` and therefore `z ∈ Aₙ`.
  -- This contradicts the fact that `(Aₙ)` has an empty intersection.
  have ε_pos : 0 < ε := this.symm.bot_lt
  have mem n : z ∈ A n := by
    have : χ n z = lmarginalPartialKernel κ (max p (N n)) (N n) (χ n)
        (updateFinset z (Iic (N n)) (fun i ↦ z i)) := by
      rw [lmarginalPartialKernel_le _ (le_max_right _ _) (mχ n)]
      congr with i
      simp [updateFinset]
    have : 0 < χ n (z) := by
      rw [this]
      convert lt_of_lt_of_le ε_pos (imp _ (le_max_left _ _) z n) using 2
      ext i
      simp [updateFinset]
    exact Set.mem_of_indicator_ne_zero (ne_of_lt this).symm
  exact (A_inter ▸ Set.mem_iInter.2 mem).elim

/-- The `ionescuTulceaContent` is sigma-subadditive. -/
theorem ionescuTulceaContent_sigma_subadditive {p : ℕ} (x₀ : (i : Iic p) → X i)
    ⦃f : ℕ → Set ((n : ℕ) → X n)⦄
    (hf : ∀ n, f n ∈ cylinders X)
    (hf_Union : (⋃ n, f n) ∈ cylinders X) :
    ionescuTulceaContent κ x₀ (⋃ n, f n) ≤ ∑' n, ionescuTulceaContent κ x₀ (f n) := by
  have _ n : Nonempty (X n) := by
    refine Nat.case_strong_induction_on (p := fun n ↦ Nonempty (X n)) _ inferInstance
      fun n hind ↦ ?_
    have : Nonempty ((i : Iic n) → X i) :=
      Nonempty.intro fun i ↦ @Classical.ofNonempty _ (hind i.1 (mem_Iic.1 i.2))
    exact ProbabilityMeasure.nonempty
      ⟨κ n Classical.ofNonempty, inferInstance⟩
  refine (ionescuTulceaContent κ x₀).sigma_subadditive_of_sigma_additive
    isSetRing_cylinders (fun f hf hf_Union hf' ↦ ?_) f hf hf_Union
  refine sigma_additive_addContent_of_tendsto_zero isSetRing_cylinders
    (ionescuTulceaContent κ x₀) (fun h ↦ ?_) ?_ hf hf_Union hf'
  · rename_i s
    obtain ⟨N, S, mS, s_eq⟩ : ∃ N S, MeasurableSet S ∧ s = cylinder (Iic N) S := by
      simpa [cylinders_nat] using h
    let x_ : (n : ℕ) → X n := Classical.ofNonempty
    classical
    rw [s_eq, ← proj_updateFinset x_ x₀,
      ionescuTulceaContent_eq_lmarginalPartialKernel κ mS (updateFinset x_ _ x₀)]
    refine ne_of_lt (lt_of_le_of_lt ?_ (by norm_num : (1 : ℝ≥0∞) < ∞))
    nth_rw 2 [← mul_one 1,
      ← measure_univ (μ := partialKernel κ p N (fun i ↦ updateFinset x_ _ x₀ i))]
    rw [lmarginalPartialKernel, ← MeasureTheory.lintegral_const]
    exact lintegral_mono <| Set.indicator_le (by simp)
  · exact fun s hs anti_s inter_s ↦ ionescuTulceaContent_tendsto_zero κ s hs anti_s inter_s x₀

/-- This function is the kernel given by the Ionescu-Tulcea theorem. -/
noncomputable def ionescuTulceaFun (p : ℕ) (x₀ : (i : Iic p) → X i) :
    Measure ((n : ℕ) → X n) :=
  Measure.ofAddContent isSetSemiring_cylinders generateFrom_cylinders
    (ionescuTulceaContent κ x₀) (ionescuTulceaContent_sigma_subadditive κ x₀)

theorem isProbabilityMeasure_ionescuTulceaFun (p : ℕ) (x₀ : (i : Iic p) → X i) :
    IsProbabilityMeasure (ionescuTulceaFun κ p x₀) := by
  constructor
  rw [← cylinder_univ (Iic 0), ionescuTulceaFun, Measure.ofAddContent_eq,
    ionescuTulceaContent_cylinder]
  · simp
  · exact MeasurableSet.univ
  · rw [mem_cylinders]
    exact ⟨Iic 0, Set.univ, MeasurableSet.univ, rfl⟩

theorem isProjectiveLimit_ionescuTulceaFun (p : ℕ) (x₀ : (i : Iic p) → X i) :
    IsProjectiveLimit (ionescuTulceaFun κ p x₀)
      (inducedFamily (fun n ↦ partialKernel κ p n x₀)) := by
  rw [isProjectiveLimit_nat_iff]
  · intro n
    ext s ms
    rw [Measure.map_apply (measurable_fprojNat n) ms]
    have h_mem : (fprojNat n) ⁻¹' s ∈ cylinders X := by
      rw [mem_cylinders]; exact ⟨Iic n, s, ms, rfl⟩
    rw [ionescuTulceaFun, Measure.ofAddContent_eq _ _ _ _ h_mem, ionescuTulceaContent,
      kolContent_congr _ (_ ⁻¹' s) rfl ms]
  · exact (isProjectiveMeasureFamily_inducedFamily _ (partialKernel_proj_apply κ x₀))

theorem measurable_ionescuTulceaFun (p : ℕ) : Measurable (ionescuTulceaFun κ p) := by
  apply Measure.measurable_of_measurable_coe
  refine MeasurableSpace.induction_on_inter
    (C := fun t ↦ Measurable (fun x₀ ↦ ionescuTulceaFun κ p x₀ t))
    (s := cylinders X) generateFrom_cylinders.symm isPiSystem_cylinders
    (by simp) (fun t ht ↦ ?cylinder) (fun t mt ht ↦ ?compl) (fun f disf mf hf ↦ ?union)
  · obtain ⟨N, S, mS, t_eq⟩ : ∃ N S, MeasurableSet S ∧ t = cylinder (Iic N) S := by
      simpa [cylinders_nat] using ht
    simp_rw [ionescuTulceaFun, Measure.ofAddContent_eq _ _ _ _ ht, ionescuTulceaContent,
      kolContent_congr _ t t_eq mS]
    simp only [inducedFamily]
    refine Measure.measurable_measure.1 ?_ _ mS
    refine (Measure.measurable_map _ ?_).comp (Kernel.measurable _)
    exact measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
  · have := isProbabilityMeasure_ionescuTulceaFun κ p
    simp_rw [measure_compl mt (measure_ne_top _ _), measure_univ]
    exact Measurable.const_sub ht _
  · simp_rw [measure_iUnion disf mf]
    exact Measurable.ennreal_tsum hf

/-- *Ionescu-Tulcea Theorem* : Given a family of kernels `κ k` taking variables in `Iic k` with
value in `X (k+1)`, the kernel `ionescuTulceaKernel κ p` takes a variable `x` depending on the
variables `i ≤ p` and associates to it a kernel on trajectories depending on all variables,
where the entries with index `≤ p` are those of `x`, and then one follows iteratively the
kernels `κ p`, then `κ (p+1)`, and so on.

The fact that such a kernel exists on infinite trajectories is not obvious, and is the content of
the Ionescu-Tulcea theorem. -/
noncomputable def ionescuTulceaKernel (p : ℕ) : Kernel ((i : Iic p) → X i) ((n : ℕ) → X n) :=
  { toFun := ionescuTulceaFun κ p
    measurable' := measurable_ionescuTulceaFun κ p }

theorem ionescuTulceaKernel_apply (p : ℕ) (x₀ : (i : Iic p) → X i) :
    ionescuTulceaKernel κ p x₀ = ionescuTulceaFun κ p x₀ := rfl

instance (p : ℕ) : IsMarkovKernel (ionescuTulceaKernel κ p) :=
  IsMarkovKernel.mk fun _ ↦ isProbabilityMeasure_ionescuTulceaFun ..

theorem ionescuTulceaKernel_proj (a b : ℕ) :
    (ionescuTulceaKernel κ a).map (fprojNat b) (measurable_fprojNat b) = partialKernel κ a b := by
  ext1 x₀
  rw [Kernel.map_apply, ionescuTulceaKernel_apply, isProjectiveLimit_ionescuTulceaFun,
    inducedFamily_Iic]

theorem eq_ionescuTulceaKernel' {a : ℕ} (n : ℕ) (η : Kernel ((i : Iic a) → X i) ((n : ℕ) → X n))
    (hη : ∀ b ≥ n, Kernel.map η (fprojNat b) (measurable_fprojNat b) = partialKernel κ a b) :
    η = ionescuTulceaKernel κ a := by
  ext1 x₀
  refine isProjectiveLimit_unique ?_ (isProjectiveLimit_ionescuTulceaFun _ _ _)
  rw [isProjectiveLimit_nat_iff' _ _ _ n]
  · intro k hk
    rw [inducedFamily_Iic, ← Kernel.map_apply _ (measurable_fprojNat k), hη k hk]
  · exact (isProjectiveMeasureFamily_inducedFamily _ (partialKernel_proj_apply κ x₀))

theorem eq_ionescuTulceaKernel {a : ℕ} (η : Kernel ((i : Iic a) → X i) ((n : ℕ) → X n))
    (hη : ∀ b, Kernel.map η (fprojNat b) (measurable_fprojNat b) = partialKernel κ a b) :
    η = ionescuTulceaKernel κ a := eq_ionescuTulceaKernel' κ 0 η fun b _ ↦ hη b

theorem partialKernel_comp_ionescuTulceaKernel {a b : ℕ} (hab : a ≤ b) :
    (ionescuTulceaKernel κ b) ∘ₖ (partialKernel κ a b) = ionescuTulceaKernel κ a := by
  refine eq_ionescuTulceaKernel _ _ fun n ↦ ?_
  ext x₀ s ms
  rw [Kernel.map_apply' _ _ _ ms, Kernel.comp_apply' _ _ _ (measurable_fprojNat n ms)]
  simp_rw [← Measure.map_apply (measurable_fprojNat n) ms,
    ← Kernel.map_apply (ionescuTulceaKernel κ b) (measurable_fprojNat n), ionescuTulceaKernel_proj κ b n]
  rw [← Kernel.comp_apply' _ _ _ ms, partialKernel_comp _ n hab]

theorem ionescuTulceaKernel_proj_le {a b : ℕ} (hab : a ≤ b) :
    Kernel.map (ionescuTulceaKernel κ b) (@fprojNat X a) (measurable_fprojNat a) =
    Kernel.deterministic (fprojNat_le hab) (measurable_fprojNat_le _) := by
  rw [ionescuTulceaKernel_proj, partialKernel, dif_neg (not_lt.2 hab)]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The canonical filtration on dependent functions indexed by `ℕ`, where `𝓕 n` consists of
measurable sets depending only on coordinates `≤ n`. -/
def ℱ : @Filtration ((n : ℕ) → X n) ℕ _ inferInstance where
  seq n := (inferInstance : MeasurableSpace ((i : Iic n) → X i)).comap (fprojNat n)
  mono' i j hij := by
    simp only
    rw [← fprojNat_le_comp_fprojNat hij, ← comap_comp]
    exact MeasurableSpace.comap_mono (measurable_fprojNat_le _).comap_le
  le' n := (measurable_fprojNat n).comap_le

/-- If a function is strongly measurable with respect to the σ-algebra generated by the
first coordinates, then it only depends on those first coordinates. -/
theorem stronglyMeasurable_dependsOn {n : ℕ} {f : ((n : ℕ) → X n) → E}
    (mf : @StronglyMeasurable _ _ _ (ℱ n) f) : DependsOn f (Iic n) :=
  fun _ _ h ↦ eq_of_stronglyMeasurable_comap _ mf (dependsOn_fprojNat n h)

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
    measurable_invFun := Measurable.prod_mk (measurable_proj _) (measurable_proj _) }

/-- This theorem shows that `ionescuTulceaKernel κ n` is, up to an equivalence, the product of
a determinstic kernel with another kernel. This is an intermediate result to compute integrals
with respect to this kernel. -/
theorem ionescuTulceaKernel_eq (n : ℕ) :
    ionescuTulceaKernel κ n =
    Kernel.map
      (Kernel.deterministic (@id ((i : Iic n) → X i)) measurable_id ×ₖ
        Kernel.map (ionescuTulceaKernel κ n) (proj (Set.Ioi n)) (measurable_proj _))
      (el' n) (el' n).measurable := by
  refine (eq_ionescuTulceaKernel' _ (n + 1) _ fun a ha ↦ ?_).symm
  ext x s ms
  rw [Kernel.map_map, Kernel.map_apply' _ _ _ ms, Kernel.deterministic_prod_apply',
    Kernel.map_apply']
  · have : (fprojNat a) ∘ (el' n) ∘ (Prod.mk x) ∘
        (proj (Set.Ioi n)) =
        (fun y (i : Iic a) ↦ if hi : i.1 ≤ n then x ⟨i.1, mem_Iic.2 hi⟩ else y i) ∘
        (fprojNat a) := by
      ext x i
      by_cases hi : i.1 ≤ n <;> simp [hi, el']
    have aux t : {c : (i : Set.Ioi n) → X i | (id x, c) ∈ t} = Prod.mk x ⁻¹' t := rfl
    have hyp : Measurable
        (fun (y : (i : Iic a) → X i) (i : Iic a) ↦
          if hi : i.1 ≤ n then x ⟨i.1, mem_Iic.2 hi⟩ else y i) := by
      refine measurable_pi_lambda _ (fun i ↦ ?_)
      by_cases hi : i.1 ≤ n <;> simp [hi]
      exact measurable_pi_apply _
    rw [aux, ← Set.preimage_comp, ← Set.preimage_comp, comp.assoc, this,
      ← Kernel.map_apply' _ _ _ ms, ← Kernel.map_map _ (measurable_fprojNat a) hyp,
      ionescuTulceaKernel_proj, Kernel.map_apply' _ _ _ ms, partialKernel_lt κ (by omega),
      Kernel.map_apply' _ _ _ (hyp ms), Kernel.deterministic_prod_apply',
      Kernel.map_apply' _ _ _ ms, Kernel.deterministic_prod_apply']
    · congr with y
      simp only [id_eq, el, Nat.succ_eq_add_one, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk,
        Set.mem_preimage, Set.mem_setOf_eq]
      congrm (fun i ↦ ?_) ∈ s
      by_cases hi : i.1 ≤ n <;> simp [hi]
    · exact (el n a (by omega)).measurable ms
    · exact (el n a (by omega)).measurable <| hyp ms
  · exact measurable_prod_mk_left ((el' n).measurable <| (measurable_fprojNat a) ms)
  · exact (el' n).measurable <| (measurable_fprojNat a) ms

theorem measurable_updateFinset' {ι : Type*} [DecidableEq ι] {I : Finset ι}
    {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    {y : (i : I) → X i} : Measurable (fun x ↦ updateFinset x I y) := by
  refine measurable_pi_lambda _ (fun i ↦ ?_)
  by_cases hi : i ∈ I <;> simp only [updateFinset, hi, ↓reduceDIte, measurable_const]
  exact measurable_pi_apply _

theorem aux {n : ℕ} (x₀ : (i : Iic n) → X i) :
    (el' n ∘ (Prod.mk x₀) ∘ (proj (Set.Ioi n))) =
      fun y ↦ updateFinset y _ x₀ := by
  ext y i
  simp [el', updateFinset]

theorem ionescuTulceaKernel_eq_map_updateFinset {n : ℕ} (x₀ : (i : Iic n) → X i) :
    ionescuTulceaKernel κ n x₀ =
      (ionescuTulceaKernel κ n x₀).map (fun y ↦ updateFinset y _ x₀) := by
  ext s ms
  nth_rw 1 [ionescuTulceaKernel_eq]
  rw [← aux, Kernel.map_apply' _ _ _ ms, ← Measure.map_map, Measure.map_apply _ ms,
    Kernel.deterministic_prod_apply', ← Measure.map_map, Measure.map_apply, Kernel.map_apply]
  · rfl
  · exact measurable_prod_mk_left
  · exact (el' n).measurable ms
  · exact measurable_prod_mk_left
  · exact measurable_proj _
  · exact (el' n).measurable ms
  · exact (el' n).measurable
  · exact (el' n).measurable
  · exact measurable_prod_mk_left.comp (measurable_proj _)

theorem integral_ionescuTulceaKernel {n : ℕ} (x₀ : (i : Iic n) → X i) {f : ((n : ℕ) → X n) → E}
    (mf : AEStronglyMeasurable f (ionescuTulceaKernel κ n x₀)) :
    ∫ x, f x ∂ionescuTulceaKernel κ n x₀ =
      ∫ x, f (updateFinset x _ x₀) ∂ionescuTulceaKernel κ n x₀ := by
  nth_rw 1 [ionescuTulceaKernel_eq_map_updateFinset, integral_map]
  · exact measurable_updateFinset'.aemeasurable
  · convert mf
    nth_rw 2 [ionescuTulceaKernel_eq_map_updateFinset]

theorem partialKernel_comp_ionescuTulceaKernel_apply {a b : ℕ} (hab : a ≤ b)
    (f : ((i : Iic b) → X i) → ((n : ℕ) → X n) → E)
    (hf : StronglyMeasurable f.uncurry)
    (x₀ : (i : Iic a) → X i)
    (i_f : Integrable (fun x ↦ f (fprojNat b x) x) (ionescuTulceaKernel κ a x₀)) :
    ∫ x, ∫ y, f x y ∂ionescuTulceaKernel κ b x ∂partialKernel κ a b x₀ =
      ∫ x, f (fprojNat b x) x ∂ionescuTulceaKernel κ a x₀ := by
  rw [← partialKernel_comp_ionescuTulceaKernel κ hab, Kernel.integral_comp]
  · congr with x
    rw [integral_ionescuTulceaKernel]
    nth_rw 2 [integral_ionescuTulceaKernel]
    congrm ∫ y, f (fun i ↦ ?_) _ ∂_
    simp [updateFinset, i.2]
    · exact hf.aestronglyMeasurable.comp_measurable ((measurable_fprojNat b).prod_mk measurable_id)
    · exact hf.of_uncurry_left.aestronglyMeasurable
  · convert i_f
    rw [partialKernel_comp_ionescuTulceaKernel _ hab]

theorem integrable_ionescuTulceaKernel {a b : ℕ} (hab : a ≤ b) {f : ((n : ℕ) → X n) → E}
    (x₀ : (i : Iic a) → X i)
    (i_f : Integrable f (ionescuTulceaKernel κ a x₀)) :
    ∀ᵐ x ∂ionescuTulceaKernel κ a x₀, Integrable f (ionescuTulceaKernel κ b (fprojNat b x)) := by
  rw [← partialKernel_comp_ionescuTulceaKernel _ hab, Kernel.integrable_comp_iff] at i_f
  · apply ae_of_ae_map (p := fun x ↦ Integrable f (ionescuTulceaKernel κ b x))
    · exact (measurable_fprojNat b).aemeasurable
    · convert i_f.1
      rw [← ionescuTulceaKernel_proj, Kernel.map_apply]
  · exact i_f.aestronglyMeasurable

theorem condexp_ionescuTulceaKernel
    {a b : ℕ} (hab : a ≤ b) (x₀ : (i : Iic a) → X i) {f : ((n : ℕ) → X n) → E}
    (i_f : Integrable f (ionescuTulceaKernel κ a x₀)) (mf : StronglyMeasurable f) :
    ((ionescuTulceaKernel κ a) x₀)[f|ℱ b] =ᵐ[ionescuTulceaKernel κ a x₀]
      fun x ↦ ∫ y, f y ∂ionescuTulceaKernel κ b (fprojNat b x) := by
  refine (ae_eq_condexp_of_forall_setIntegral_eq _ i_f ?_ ?_ ?_).symm
  · rintro s - -
    apply Integrable.integrableOn
    conv => enter [1]; change (fun x ↦ ∫ y, f y ∂ionescuTulceaKernel κ b x) ∘ (fprojNat b)
    rw [← partialKernel_comp_ionescuTulceaKernel κ hab, Kernel.integrable_comp_iff] at i_f
    · rw [← integrable_map_measure, ← Kernel.map_apply, ionescuTulceaKernel_proj,
        ← integrable_norm_iff]
      · apply i_f.2.mono'
        · apply AEStronglyMeasurable.norm
          exact (mf.comp_measurable measurable_snd).integral_kernel_prod_right'.aestronglyMeasurable
        · refine eventually_of_forall fun x ↦ ?_
          rw [norm_norm]
          exact norm_integral_le_integral_norm _
      · exact (mf.comp_measurable measurable_snd).integral_kernel_prod_right'.aestronglyMeasurable
      · exact (mf.comp_measurable measurable_snd).integral_kernel_prod_right'.aestronglyMeasurable
      · exact (measurable_fprojNat b).aemeasurable
    · exact mf.aestronglyMeasurable
  · rintro - ⟨t, mt, rfl⟩ -
    rw [← integral_indicator]
    · have this x : ((fprojNat b) ⁻¹' t).indicator
          (fun x ↦ ∫ y, f y ∂ionescuTulceaKernel κ b (fprojNat b x)) x =
          t.indicator (fun x ↦ ∫ y, f y ∂ionescuTulceaKernel κ b x) ((fprojNat b) x) :=
        Set.indicator_comp_right (fprojNat b) (g := fun x ↦ ∫ y, f y ∂ionescuTulceaKernel κ b x)
      simp_rw [this]
      rw [← integral_map, ← Kernel.map_apply, ionescuTulceaKernel_proj κ]
      simp_rw [Set.indicator_one_smul_apply (M := ℝ)
        (fun x ↦ ∫ y, f y ∂ionescuTulceaKernel κ b x), ← integral_smul]
      · rw [partialKernel_comp_ionescuTulceaKernel_apply _ hab, ← integral_indicator]
        · congr with x
          by_cases h : fprojNat b x ∈ t <;> simp [h, -fproj_def]
        · exact measurable_fprojNat b mt
        · rw [uncurry_def]
          apply StronglyMeasurable.smul
          · exact (stronglyMeasurable_const.indicator mt).comp_measurable measurable_fst
          · exact mf.comp_measurable measurable_snd
        · simp_rw [← Set.indicator_comp_right, Function.comp, ← Set.indicator_one_smul_apply]
          exact i_f.indicator (measurable_fprojNat b mt)
      · exact (measurable_fprojNat b).aemeasurable
      · refine (StronglyMeasurable.indicator ?_ mt).aestronglyMeasurable
        exact (mf.comp_measurable measurable_snd).integral_kernel_prod_right'
    · exact measurable_fprojNat b mt
  · conv => enter [2]; change (fun x ↦ ∫ y, f y ∂ionescuTulceaKernel κ b x) ∘ (fprojNat b)
    apply AEStronglyMeasurable.comp_ae_measurable'
    · exact (mf.comp_measurable measurable_snd).integral_kernel_prod_right'.aestronglyMeasurable
    · exact (measurable_fprojNat b).aemeasurable

theorem condexp_ionescuTulceaKernel' {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    (x₀ : (i : Iic a) → X i) {f : ((n : ℕ) → X n) → E} :
    (ionescuTulceaKernel κ a x₀)[f|ℱ b] =ᵐ[ionescuTulceaKernel κ a x₀]
      fun x ↦ ∫ y, ((ionescuTulceaKernel κ a x₀)[f|ℱ c]) (updateFinset x _ y)
        ∂partialKernel κ b c (fprojNat b x) := by
  have i_cf : Integrable ((ionescuTulceaKernel κ a x₀)[f|ℱ c])
      (ionescuTulceaKernel κ a x₀) := integrable_condexp
  have mcf : StronglyMeasurable ((ionescuTulceaKernel κ a x₀)[f|ℱ c]) :=
    stronglyMeasurable_condexp.mono (ℱ.le c)
  filter_upwards [ℱ.condexp_condexp f hbc, condexp_ionescuTulceaKernel κ hab x₀ i_cf mcf]
  intro x h1 h2
  rw [← h1, h2, ← ionescuTulceaKernel_proj, Kernel.map_apply, integral_map]
  · congr with y
    apply stronglyMeasurable_dependsOn stronglyMeasurable_condexp
    simp [updateFinset]
    exact fun i hi ↦ (if_pos hi).symm
  · exact (measurable_fprojNat c).aemeasurable
  · exact (mcf.comp_measurable measurable_updateFinset).aestronglyMeasurable
