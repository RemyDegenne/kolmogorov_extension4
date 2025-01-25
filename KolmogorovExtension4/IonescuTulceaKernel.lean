/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import KolmogorovExtension4.compProdNat
import KolmogorovExtension4.DependsOn
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import KolmogorovExtension4.KolmogorovExtension
import Batteries.Data.Nat.Lemmas

open MeasureTheory ProbabilityTheory Finset ENNReal Filter Topology Function MeasurableSpace Preorder

section castLemmas

variable {X : ℕ → Type*}

private lemma Iic_pi_eq {a b : ℕ} (h : a = b) :
    ((i : Iic a) → X i) = ((i : Iic b) → X i) := by cases h; rfl

private lemma cast_pi {s t : Set ℕ} (h : s = t) (x : (i : s) → X i) (i : t) :
    cast (congrArg (fun u : Set ℕ ↦ (Π i : u, X i)) h) x i = x ⟨i.1, h.symm ▸ i.2⟩ := by
  subst h
  rfl

/-- This function takes a trajectory up to time `p` and a way of building the next step of the
trajectory and returns a whole trajectory whose first steps correspond
to the initial ones provided. -/
def iterate_induction {p : ℕ} (x₀ : (i : Iic p) → X i)
    (ind : (k : ℕ) → ((n : Iic k) → X n) → X (k + 1)) : (k : ℕ) → X k
  | 0 => x₀ ⟨0, mem_Iic.2 <| zero_le p⟩
  | q + 1 =>
    if hq : q + 1 ≤ p
      then x₀ ⟨q + 1, mem_Iic.2 hq⟩
      else ind q (fun i ↦ iterate_induction x₀ ind i)
  decreasing_by exact Nat.lt_succ.2 (mem_Iic.1 i.2)

theorem iterate_induction_le {p : ℕ} (x₀ : (i : Iic p) → X i)
    (ind : (k : ℕ) → ((n : Iic k) → X n) → X (k + 1)) (k : Iic p) :
    iterate_induction x₀ ind k = x₀ k := by
  obtain ⟨(zero | j), hi⟩ := k
  · rw [iterate_induction]
  · rw [iterate_induction]
    simp [mem_Iic.1 hi]

lemma frestrictLe_iterate_induction {p : ℕ} (x₀ : (i : Iic p) → X i)
    (ind : (k : ℕ) → ((n : Iic k) → X n) → X (k + 1)) :
    frestrictLe p (iterate_induction x₀ ind) = x₀ := by
  ext i
  simp [iterate_induction_le]

variable [∀ n, MeasurableSpace (X n)]

private lemma measure_cast {a b : ℕ} (h : a = b) (μ : (n : ℕ) → Measure ((i : Iic n) → X i)) :
    (μ a).map (cast (Iic_pi_eq h)) = μ b := by
  subst h
  exact Measure.map_id

private lemma heq_measurableSpace_Iic_pi {a b : ℕ} (h : a = b) :
    HEq (inferInstance : MeasurableSpace ((i : Iic a) → X i))
    (inferInstance : MeasurableSpace ((i : Iic b) → X i)) := by cases h; rfl

end castLemmas

section ProjectiveFamily

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]

/-- To check that a measure `ν` is the projective limit of a projective family of measures indexed
by `Finset ℕ`, it is enough to check on intervals of the form `Iic n`, where `n` is larger than
a given integer. -/
theorem isProjectiveLimit_nat_iff' (μ : (I : Finset ℕ) → Measure ((i : I) → X i))
    (hμ : IsProjectiveMeasureFamily μ) (ν : Measure ((n : ℕ) → X n)) (a : ℕ) :
    IsProjectiveLimit ν μ ↔ ∀ ⦃n⦄, n ≥ a → ν.map (frestrictLe n) = μ (Iic n) := by
  refine ⟨fun h n _ ↦ h (Iic n), fun h I ↦ ?_⟩
  have := (I.sub_Iic.trans (Iic_subset_Iic.2 (le_max_left (I.sup id) a)))
  rw [← restrict₂_comp_restrict this, ← Measure.map_map, ← frestrictLe, h (le_max_right _ _), ← hμ]
  any_goals fun_prop

/-- To check that a measure `ν` is the projective limit of a projective family of measures indexed
by `Finset ℕ`, it is enough to check on intervals of the form `Iic n`. -/
theorem isProjectiveLimit_nat_iff (μ : (I : Finset ℕ) → Measure ((i : I) → X i))
    (hμ : IsProjectiveMeasureFamily μ) (ν : Measure ((n : ℕ) → X n)) :
    IsProjectiveLimit ν μ ↔ ∀ n, ν.map (frestrictLe n) = μ (Iic n) := by
  rw [isProjectiveLimit_nat_iff' _ hμ _ 0]
  simp

/-- Given a family of measures `μ : (n : ℕ) → Measure ((i : Iic n) → X i)`, we can define a family
of measures indexed by `Finset ℕ` by projecting the measures. -/
noncomputable def inducedFamily (μ : (n : ℕ) → Measure ((i : Iic n) → X i)) :
    (S : Finset ℕ) → Measure ((k : S) → X k) :=
  fun S ↦ (μ (S.sup id)).map (restrict₂ S.sub_Iic)

instance (μ : (n : ℕ) → Measure ((i : Iic n) → X i)) [∀ n, IsFiniteMeasure (μ n)] (I : Finset ℕ) :
    IsFiniteMeasure (inducedFamily μ I) := by
  rw [inducedFamily]
  infer_instance

/-- Given a family of measures `μ : (n : ℕ) → Measure ((i : Iic n) → X i)`, the induced family
equals `μ` over the intervals `Iic n`. -/
theorem inducedFamily_Iic (μ : (n : ℕ) → Measure ((i : Iic n) → X i)) (n : ℕ) :
    inducedFamily μ (Iic n) = μ n := by
  rw [inducedFamily, ← measure_cast (sup_Iic n) μ]
  congr with x i
  rw [restrict₂, cast_pi (by rw [sup_Iic n])]

/-- Given a family of measures `μ : (n : ℕ) → Measure ((i : Iic n) → X i)`, the induced family
will be projective only if `μ` is projective, in the sense that if `a ≤ b`, then projecting
`μ b` gives `μ a`. -/
theorem isProjectiveMeasureFamily_inducedFamily (μ : (n : ℕ) → Measure ((i : Iic n) → X i))
    (h : ∀ a b : ℕ, ∀ hab : a ≤ b, (μ b).map (frestrictLe₂ hab) = μ a) :
    IsProjectiveMeasureFamily (inducedFamily μ) := by
  intro I J hJI
  have sls : J.sup id ≤ I.sup id := sup_mono hJI
  simp only [inducedFamily]
  rw [Measure.map_map, restrict₂_comp_restrict₂,
    ← restrict₂_comp_restrict₂ J.sub_Iic (Iic_subset_Iic.2 sls), ← Measure.map_map, ← frestrictLe₂,
    h (J.sup id) (I.sup id) sls]
  any_goals fun_prop

end ProjectiveFamily

open Kernel

section definition

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
  (κ : (k : ℕ) → Kernel (Π i : Iic k, X i) (X (k + 1)))
  [∀ k, IsMarkovKernel (κ k)]

/-- Given a family of kernels `κ : (n : ℕ) → Kernel (Π i : Iic k, X i) (X (n + 1))`, and the
trajectory up to time `n` we can construct an additive content over cylinders. It corresponds
to composing the kernels by starting at time `n + 1`. -/
noncomputable def ionescuTulceaContent {n : ℕ} (x₀ : (i : Iic n) → X i) :
    AddContent (measurableCylinders X) :=
  kolContent (isProjectiveMeasureFamily_inducedFamily _ (partialKernel_proj_apply κ x₀))

/-- The `ionescuTulceaContent κ x₀` of a cylinder indexed by first coordinates is given by
`partialKernel`. -/
theorem ionescuTulceaContent_cylinder {a b : ℕ} (x₀ : (i : Iic a) → X i)
    {S : Set ((i : Iic b) → X i)} (mS : MeasurableSet S) :
    ionescuTulceaContent κ x₀ (cylinder _ S) = partialKernel κ a b x₀ S := by
  rw [ionescuTulceaContent, kolContent_cylinder _ mS, inducedFamily_Iic]

/-- The `ionescuTulceaContent` of a cylinder is equal to the integral of its indicator function. -/
theorem ionescuTulceaContent_eq_lmarginalPartialKernel {N : ℕ} {S : Set ((i : Iic N) → X i)}
    (mS : MeasurableSet S) (x₀ : (n : ℕ) → X n) (n : ℕ) :
    ionescuTulceaContent κ (frestrictLe n x₀) (cylinder _ S) =
      lmarginalPartialKernel κ n N ((cylinder _ S).indicator 1) x₀ := by
  rw [ionescuTulceaContent_cylinder _ _ mS, ← lintegral_indicator_one mS, lmarginalPartialKernel]
  congr with x
  apply indicator_const_eq
  rw [mem_cylinder]
  congrm (fun i ↦ ?_) ∈ S
  simp [updateFinset, i.2]

/-- The cylinders of a product space indexed by `ℕ` can be seen as depending on the first
corrdinates. -/
theorem cylinders_nat :
    measurableCylinders X = ⋃ (N) (S) (_ : MeasurableSet S), {cylinder (Iic N) S} := by
  ext s
  simp only [mem_measurableCylinders, exists_prop, Set.mem_iUnion, mem_singleton]
  refine ⟨?_, fun ⟨N, S, mS, s_eq⟩ ↦ ⟨Iic N, S, mS, s_eq⟩⟩
  rintro ⟨t, S, mS, rfl⟩
  refine ⟨t.sup id, restrict₂ t.sub_Iic ⁻¹' S, measurable_restrict₂ _ mS, ?_⟩
  unfold cylinder
  rw [← Set.preimage_comp, restrict₂_comp_restrict]
  exact Set.mem_singleton _

variable [Nonempty (X 0)]

/-- This is an auxiliary result for `ionescuTulceaContent_tendsto_zero`.
Consider `f` a sequence of bounded measurable
functions such that `f n` depends only on the first coordinates up to `N n`.
Assume that when integrating `f n` against `partialKernel (k + 1) (N n)`,
one gets a non-increasing sequence of functions wich converges to `l`.
Assume then that there exists `ε` and `y : (n : Iic k) → X n` such that
when integrating `f n` against `partialKernel k (N n) y`, you get something at least
`ε` for all `n`. Then there exists `z` such that this remains true when integrating
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
      (update (updateFinset x _ y) (k + 1) z) := by
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
    · rw [← lmarginalPartialKernel_self κ k.le_succ h.le (mf n)]
    · rw [← h, lmarginalPartialKernel_le _ (_root_.le_refl (k + 1)) (mf n)]
    · rw [lmarginalPartialKernel_le _ (by omega) (mf n),
        (hcte n).lmarginalPartialKernel_eq _ _ (mf n) (by omega),
        (hcte n).lmarginalPartialKernel_eq _ _ (mf n) (by omega)]
  -- `F` is also a bounded sequence.
  have F_le n x : F n x ≤ bound := by
    simp_rw [F, lmarginalPartialKernel]
    rw [← mul_one bound, ← measure_univ (μ := partialKernel κ (k + 1) (N n) (frestrictLe (k + 1) x)),
        ← MeasureTheory.lintegral_const]
    exact lintegral_mono fun _ ↦ le_bound _ _
  -- By dominated convergence, the integral of `fₙ` between time `k` and time `N n` converges
  -- to the integral of `l` between time `k` and time `k + 1`.
  have tendsto_int x : Tendsto (fun n ↦ lmarginalPartialKernel κ k (N n) (f n) x) atTop
      (𝓝 (lmarginalPartialKernel κ k (k + 1) l x)) := by
    simp_rw [f_eq, lmarginalPartialKernel]
    exact tendsto_lintegral_of_dominated_convergence (fun _ ↦ bound)
      (fun n ↦ (measurable_lmarginalPartialKernel _ _ _ (mf n)).comp measurable_updateFinset)
      (fun n ↦ Eventually.of_forall <| fun y ↦ F_le n _)
      (by simp [fin_bound]) (Eventually.of_forall (fun _ ↦ tendstoF _))
  -- By hypothesis, we have `ε ≤ lmarginalPartialKernel κ k (k + 1) (F n) (updateFinset x _ y)`,
  -- so this is also true for `l`.
  have ε_le_lint x : ε ≤ lmarginalPartialKernel κ k (k + 1) l (updateFinset x _ y) :=
    ge_of_tendsto (tendsto_int _) (by simp [hpos])
  let x_ : (n : ℕ) → X n := Classical.ofNonempty
  -- We now have that the integral of `l` with respect to a probability measure is greater than `ε`,
  -- therefore there exists `x` such that `ε ≤ l(y, x)`.
  obtain ⟨x, hx⟩ : ∃ x, ε ≤ l (update (updateFinset x_ _ y) (k + 1) x) := by
    have : ∫⁻ x, l (update (updateFinset x_ _ y) (k + 1) x) ∂(κ k y) ≠ ∞ :=
      ne_top_of_le_ne_top fin_bound <| lintegral_le_mul' _
        fun y ↦ le_of_tendsto' (tendstoF _) <| fun _ ↦ F_le _ _
    obtain ⟨x, hx⟩ := exists_lintegral_le this
    refine ⟨x, (ε_le_lint x_).trans ?_⟩
    rwa [lmarginalPartialKernel_succ, frestrictLe_updateFinset]
    refine ENNReal.measurable_of_tendsto ?_ (tendsto_pi_nhds.2 htendsto)
    exact fun n ↦ measurable_lmarginalPartialKernel _ _ _ (mf n)
  refine ⟨x, fun x' n ↦ ?_⟩
  -- As `F` is a non-increasing sequence, we have `ε ≤ Fₙ(y, x')` for any `n`.
  have := le_trans hx ((anti _).le_of_tendsto (tendstoF _) n)
  -- This part below is just to say that this is true for any `x : (i : ι) → X i`,
  -- as `Fₙ` technically depends on all the variables, but really depends only on the first `k + 1`.
  convert this using 1
  refine (hcte n).dependsOn_lmarginalPartialKernel _ _ (mf n) fun i hi ↦ ?_
  simp only [update, updateFinset, mem_Iic, F]
  split_ifs with h1 h2 <;> try rfl
  rw [mem_coe, mem_Iic] at hi
  omega

/-- The indicator of a cylinder only depends on the variables whose the cylinder depends on. -/
theorem dependsOn_cylinder_indicator {ι : Type*} {α : ι → Type*} {I : Finset ι}
    (S : Set ((i : I) → α i)) :
    DependsOn ((cylinder I S).indicator (1 : ((i : ι) → α i) → ℝ≥0∞)) I :=
  fun x y hxy ↦ indicator_const_eq _ (by simp [restrict_def, hxy])

/-- This is the key theorem to prove the existence of the `ionescuTulceaKernel`:
the `ionescuTulceaContent` of a decresaing sequence of cylinders with empty intersection
converges to `0`.
This implies the `σ`-additivity of `ionescuTulceaContent`
(see `sigma_additive_addContent_of_tendsto_zero`), which allows to extend it to the
`σ`-algebra by Carathéodory's theorem. -/
theorem ionescuTulceaContent_tendsto_zero (A : ℕ → Set (Π n : ℕ, X n))
    (A_mem : ∀ n, A n ∈ measurableCylinders X) (A_anti : Antitone A) (A_inter : ⋂ n, A n = ∅)
    {p : ℕ} (x₀ : Π i : Iic p, X i) :
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
    exact (measurable_indicator_const_iff 1).2 <| (mS n).cylinder
  -- `χₙ` only depends on the first coordinates.
  have χ_dep n : DependsOn (χ n) (Iic (N n)) := by
    simp_rw [χ, A_eq]
    exact dependsOn_cylinder_indicator _
  -- Therefore its integral against `partialKernel κ k (N n)` is constant.
  have lma_const x y n :
      lmarginalPartialKernel κ p (N n) (χ n) (updateFinset x _ x₀) =
      lmarginalPartialKernel κ p (N n) (χ n) (updateFinset y _ x₀) := by
    refine (χ_dep n).dependsOn_lmarginalPartialKernel κ p (mχ n) fun i hi ↦ ?_
    rw [mem_coe, mem_Iic] at hi
    simp [updateFinset, hi]
  -- As `(Aₙ)` is non-increasing, so is `(χₙ)`.
  have χ_anti : Antitone χ := by
    refine fun m n hmn y ↦ ?_
    apply Set.indicator_le fun a ha ↦ ?_
    simp [χ, A_anti hmn ha]
  -- Integrating `χₙ` further than the last coordinate it depends on does nothing.
  -- This is used to then show that the integral of `χₙ` from time `k` is non-increasing.
  have lma_inv k M n (h : N n ≤ M) :
      lmarginalPartialKernel κ k M (χ n) = lmarginalPartialKernel κ k (N n) (χ n) :=
    (χ_dep n).lmarginalPartialKernel_right κ k (mχ n) h (_root_.le_refl _)
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
  -- We have all the conditions to apply `le_lmarginalPartialKernel_succ`.
  -- This allows us to recursively build a sequence `z` with the following property:
  -- for any `k ≥ p` and `n`, integrating `χ n` from time `k` to time `N n`
  -- with the trajectory up to `k` being equal to `z` gives something greater than `ε`.
  choose! ind hind using
    fun k y h ↦ le_lmarginalPartialKernel_succ κ χ_dep mχ (by norm_num : (1 : ℝ≥0∞) ≠ ∞)
      χ_le (anti_lma (k + 1)) (hl (k + 1)) ε y h
  let z := iterate_induction x₀ ind
  have main k (hk : p ≤ k) : ∀ x n,
      ε ≤ lmarginalPartialKernel κ k (N n) (χ n) (updateFinset x (Iic k) (frestrictLe k z)) := by
    refine Nat.le_induction (fun x n ↦ ?_) (fun k hn h x n ↦ ?_) k hk
    · rw [frestrictLe_iterate_induction]
      exact hpos x n
    · rw [← update_updateFinset_eq]
      convert hind k (fun i ↦ z i.1) h x n
      simp_rw [z, iterate_induction]
      simp [Nat.lt_succ.2 hn]
  -- We now want to prove that the integral of `χₙ`, which is equal to the `ionescuTulceaContent`
  -- of `Aₙ`, converges to `0`.
  have aux x n : ionescuTulceaContent κ x₀ (A n) =
      lmarginalPartialKernel κ p (N n) (χ n) (updateFinset x _ x₀) := by
    simp_rw [χ, A_eq]
    nth_rw 1 [← frestrictLe_updateFinset x x₀]
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
      convert lt_of_lt_of_le ε_pos (main _ (le_max_left _ _) z n) using 2
      ext i
      simp [updateFinset]
    exact Set.mem_of_indicator_ne_zero (ne_of_lt this).symm
  exact (A_inter ▸ Set.mem_iInter.2 mem).elim

/-- The `ionescuTulceaContent` is sigma-subadditive. -/
theorem ionescuTulceaContent_sigma_subadditive {p : ℕ} (x₀ : (i : Iic p) → X i)
    ⦃f : ℕ → Set ((n : ℕ) → X n)⦄
    (hf : ∀ n, f n ∈ measurableCylinders X)
    (hf_Union : (⋃ n, f n) ∈ measurableCylinders X) :
    ionescuTulceaContent κ x₀ (⋃ n, f n) ≤ ∑' n, ionescuTulceaContent κ x₀ (f n) := by
  have _ n : Nonempty (X n) := by
    refine Nat.case_strong_induction_on (p := fun n ↦ Nonempty (X n)) _ inferInstance
      fun n hind ↦ ?_
    have : Nonempty ((i : Iic n) → X i) :=
      Nonempty.intro fun i ↦ @Classical.ofNonempty _ (hind i.1 (mem_Iic.1 i.2))
    exact ProbabilityMeasure.nonempty ⟨κ n Classical.ofNonempty, inferInstance⟩
  refine addContent_iUnion_le_of_addContent_iUnion_eq_tsum
    isSetRing_measurableCylinders (fun f hf hf_Union hf' ↦ ?_) f hf hf_Union
  refine addContent_iUnion_eq_sum_of_tendsto_zero isSetRing_measurableCylinders
    (ionescuTulceaContent κ x₀) (fun s hs ↦ ?_) ?_ hf hf_Union hf'
  · obtain ⟨N, S, mS, s_eq⟩ : ∃ N S, MeasurableSet S ∧ s = cylinder (Iic N) S := by
      simpa [cylinders_nat] using hs
    let x_ : (n : ℕ) → X n := Classical.ofNonempty
    rw [s_eq, ← frestrictLe_updateFinset x_ x₀,
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
  Measure.ofAddContent isSetSemiring_measurableCylinders generateFrom_measurableCylinders
    (ionescuTulceaContent κ x₀) (ionescuTulceaContent_sigma_subadditive κ x₀)

theorem isProbabilityMeasure_ionescuTulceaFun (p : ℕ) (x₀ : (i : Iic p) → X i) :
    IsProbabilityMeasure (ionescuTulceaFun κ p x₀) where
  measure_univ := by
    rw [← cylinder_univ (Iic 0), ionescuTulceaFun, Measure.ofAddContent_eq,
      ionescuTulceaContent_cylinder _ _ MeasurableSet.univ]
    · exact measure_univ
    · exact (mem_measurableCylinders _).2 ⟨Iic 0, Set.univ, MeasurableSet.univ, rfl⟩

theorem isProjectiveLimit_ionescuTulceaFun (p : ℕ) (x₀ : (i : Iic p) → X i) :
    IsProjectiveLimit (ionescuTulceaFun κ p x₀)
      (inducedFamily (fun n ↦ partialKernel κ p n x₀)) := by
  rw [isProjectiveLimit_nat_iff]
  · intro n
    ext s ms
    rw [Measure.map_apply (measurable_frestrictLe n) ms]
    have h_mem : (frestrictLe n) ⁻¹' s ∈ measurableCylinders X := by
      rw [mem_measurableCylinders]; exact ⟨Iic n, s, ms, rfl⟩
    rw [ionescuTulceaFun, Measure.ofAddContent_eq _ _ _ _ h_mem, ionescuTulceaContent,
      kolContent_congr _ (frestrictLe n ⁻¹' s) rfl ms]
  · exact (isProjectiveMeasureFamily_inducedFamily _ (partialKernel_proj_apply κ x₀))

theorem measurable_ionescuTulceaFun (p : ℕ) : Measurable (ionescuTulceaFun κ p) := by
  apply Measure.measurable_of_measurable_coe
  refine MeasurableSpace.induction_on_inter
    (C := fun t ht ↦ Measurable (fun x₀ ↦ ionescuTulceaFun κ p x₀ t))
    (s := measurableCylinders X) generateFrom_measurableCylinders.symm
    isPiSystem_measurableCylinders (by simp) (fun t ht ↦ ?cylinder) (fun t mt ht ↦ ?compl)
    (fun f disf mf hf ↦ ?union)
  · obtain ⟨N, S, mS, t_eq⟩ : ∃ N S, MeasurableSet S ∧ t = cylinder (Iic N) S := by
      simpa [cylinders_nat] using ht
    simp_rw [ionescuTulceaFun, Measure.ofAddContent_eq _ _ _ _ ht, ionescuTulceaContent,
      kolContent_congr _ t t_eq mS, inducedFamily]
    refine Measure.measurable_measure.1 ?_ _ mS
    exact (Measure.measurable_map _ (measurable_restrict₂ _)).comp (Kernel.measurable _)
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
  ⟨fun _ ↦ isProbabilityMeasure_ionescuTulceaFun ..⟩

theorem ionescuTulceaKernel_proj (a b : ℕ) :
    (ionescuTulceaKernel κ a).map (frestrictLe b) = partialKernel κ a b := by
  ext1 x₀
  rw [Kernel.map_apply _ (measurable_frestrictLe _), ionescuTulceaKernel_apply, frestrictLe,
    isProjectiveLimit_ionescuTulceaFun, inducedFamily_Iic]

theorem eq_ionescuTulceaKernel' {a : ℕ} (n : ℕ) (η : Kernel ((i : Iic a) → X i) ((n : ℕ) → X n))
    (hη : ∀ b ≥ n, Kernel.map η (frestrictLe b) = partialKernel κ a b) :
    η = ionescuTulceaKernel κ a := by
  ext1 x₀
  refine ((isProjectiveLimit_ionescuTulceaFun _ _ _).unique ?_).symm
  rw [isProjectiveLimit_nat_iff' _ _ _ n]
  · intro k hk
    rw [inducedFamily_Iic, ← Kernel.map_apply _ (measurable_frestrictLe k), hη k hk]
  · exact (isProjectiveMeasureFamily_inducedFamily _ (partialKernel_proj_apply κ x₀))

theorem eq_ionescuTulceaKernel {a : ℕ} (η : Kernel ((i : Iic a) → X i) ((n : ℕ) → X n))
    (hη : ∀ b, Kernel.map η (frestrictLe b) = partialKernel κ a b) :
    η = ionescuTulceaKernel κ a := eq_ionescuTulceaKernel' κ 0 η fun b _ ↦ hη b

theorem partialKernel_comp_ionescuTulceaKernel {a b : ℕ} (hab : a ≤ b) :
    (ionescuTulceaKernel κ b) ∘ₖ (partialKernel κ a b) = ionescuTulceaKernel κ a := by
  refine eq_ionescuTulceaKernel _ _ fun n ↦ ?_
  ext x₀ s ms
  rw [Kernel.map_apply' _ (measurable_frestrictLe _) _ ms,
    Kernel.comp_apply' _ _ _ (measurable_frestrictLe n ms)]
  simp_rw [← Measure.map_apply (measurable_frestrictLe n) ms,
    ← Kernel.map_apply (ionescuTulceaKernel κ b) (measurable_frestrictLe n),
    ionescuTulceaKernel_proj κ b n]
  rw [← Kernel.comp_apply' _ _ _ ms, partialKernel_comp _ n hab]

theorem ionescuTulceaKernel_proj_le {a b : ℕ} (hab : a ≤ b) :
    Kernel.map (ionescuTulceaKernel κ b) (frestrictLe (π := X) a) =
    Kernel.deterministic (frestrictLe₂ hab) (measurable_frestrictLe₂ _) := by
  rw [ionescuTulceaKernel_proj, partialKernel, dif_neg (not_lt.2 hab)]

end definition

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
variable (κ : (k : ℕ) → Kernel ((i : Iic k) → X i) (X (k + 1)))
variable [∀ k, IsMarkovKernel (κ k)]

variable {E : Type*} [NormedAddCommGroup E]

/-- The canonical filtration on dependent functions indexed by `ℕ`, where `𝓕 n` consists of
measurable sets depending only on coordinates `≤ n`. -/
def ℱ : @Filtration ((n : ℕ) → X n) ℕ _ inferInstance where
  seq n := (inferInstance : MeasurableSpace ((i : Iic n) → X i)).comap (frestrictLe n)
  mono' i j hij := by
    simp only
    rw [← frestrictLe₂_comp_frestrictLe hij, ← comap_comp]
    exact MeasurableSpace.comap_mono (measurable_frestrictLe₂ _).comap_le
  le' n := (measurable_frestrictLe n).comap_le

/-- If a function is strongly measurable with respect to the σ-algebra generated by the
first coordinates, then it only depends on those first coordinates. -/
theorem stronglyMeasurable_dependsOn {n : ℕ} {f : ((n : ℕ) → X n) → E}
    (mf : @StronglyMeasurable _ _ _ (ℱ n) f) : DependsOn f (Set.Iic n) :=
  fun _ _ h ↦ eq_of_stronglyMeasurable_comap _ mf (dependsOn_frestrictLe n h)

variable [Nonempty (X 0)]

/-- This theorem shows that `ionescuTulceaKernel κ n` is, up to an equivalence, the product of
a determinstic kernel with another kernel. This is an intermediate result to compute integrals
with respect to this kernel. -/
theorem ionescuTulceaKernel_eq (n : ℕ) :
    ionescuTulceaKernel κ n =
      (Kernel.id ×ₖ (ionescuTulceaKernel κ n).map (Set.Ioi n).restrict).map (el' n) := by
  refine (eq_ionescuTulceaKernel' _ (n + 1) _ fun a ha ↦ ?_).symm
  ext x s ms
  rw [Kernel.map_map, Kernel.map_apply' _ _ _ ms, Kernel.id_prod_apply',
    Kernel.map_apply']
  · have : (frestrictLe a) ∘ (el' n) ∘ (Prod.mk x) ∘ (Set.Ioi n).restrict =
        (fun y (i : Iic a) ↦ if hi : i.1 ≤ n then x ⟨i.1, mem_Iic.2 hi⟩ else y i) ∘
          (frestrictLe a) := by
      ext x i
      by_cases hi : i.1 ≤ n <;> simp [hi, el']
    have hyp : Measurable (fun (y : (i : Iic a) → X i) (i : Iic a) ↦
        if hi : i.1 ≤ n then x ⟨i.1, mem_Iic.2 hi⟩ else y i) := by
      refine measurable_pi_lambda _ (fun i ↦ ?_)
      by_cases hi : i.1 ≤ n <;> simp [hi]
      exact measurable_pi_apply _
    rw [← Set.preimage_comp, ← Set.preimage_comp, Function.comp_assoc, this,
      ← Kernel.map_apply' _ _ _ ms, ← Kernel.map_map _ _ hyp,
      ionescuTulceaKernel_proj, Kernel.map_apply' _ _ _ ms, partialKernel_lt κ (by omega),
      Kernel.map_apply' _ _ _ (hyp ms), Kernel.deterministic_prod_apply',
      Kernel.map_apply' _ _ _ ms, Kernel.deterministic_prod_apply']
    · congr with y
      simp only [id_eq, el, Nat.succ_eq_add_one, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk,
        Set.mem_preimage, Set.mem_setOf_eq]
      congrm (fun i ↦ ?_) ∈ s
      by_cases hi : i.1 ≤ n <;> simp [hi]
    any_goals fun_prop
    · exact (el ..).measurable ms
    · exact (el ..).measurable <| hyp ms
    · exact hyp
    · exact hyp.comp (measurable_frestrictLe _)
  any_goals fun_prop
  · exact measurable_prod_mk_left <| (el' n).measurable <| (measurable_frestrictLe a) ms
  · exact (el' n).measurable <| (measurable_frestrictLe a) ms

@[measurability, fun_prop]
theorem measurable_updateFinset' {ι : Type*} [DecidableEq ι] {I : Finset ι}
    {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    {y : (i : I) → X i} : Measurable (fun x ↦ updateFinset x I y) := by
  refine measurable_pi_lambda _ (fun i ↦ ?_)
  by_cases hi : i ∈ I <;> simp only [updateFinset, hi, ↓reduceDIte, measurable_const]
  exact measurable_pi_apply _

theorem ionescuTulceaKernel_eq_map_updateFinset {n : ℕ} (x₀ : (i : Iic n) → X i) :
    (ionescuTulceaKernel κ n x₀).map (fun y ↦ updateFinset y _ x₀) =
      ionescuTulceaKernel κ n x₀ := by
  ext s ms
  nth_rw 2 [ionescuTulceaKernel_eq]
  have : (fun y ↦ updateFinset y _ x₀) = (el' n ∘ (Prod.mk x₀) ∘ (Set.Ioi n).restrict) := by
    ext x i
    simp [el', updateFinset]
  rw [this, Kernel.map_apply' _ _ _ ms, ← Measure.map_map,
    Measure.map_apply _ ms, Kernel.id_prod_apply', ← Measure.map_map, Measure.map_apply,
    Kernel.map_apply]
  any_goals fun_prop
  all_goals exact (el' n).measurable ms

theorem integrable_ionescuTulceaKernel {a b : ℕ} (hab : a ≤ b) {f : ((n : ℕ) → X n) → E}
    (x₀ : (i : Iic a) → X i)
    (i_f : Integrable f (ionescuTulceaKernel κ a x₀)) :
    ∀ᵐ x ∂ionescuTulceaKernel κ a x₀, Integrable f (ionescuTulceaKernel κ b (frestrictLe b x)) := by
  rw [← partialKernel_comp_ionescuTulceaKernel _ hab, Kernel.integrable_comp_iff] at i_f
  · apply ae_of_ae_map (p := fun x ↦ Integrable f (ionescuTulceaKernel κ b x))
    · exact (measurable_frestrictLe b).aemeasurable
    · convert i_f.1
      rw [← ionescuTulceaKernel_proj, Kernel.map_apply _ (measurable_frestrictLe _)]
  · exact i_f.aestronglyMeasurable

theorem aestronglyMeasurable_ionescuTulceaKernel {a b : ℕ} (hab : a ≤ b)
    {f : ((n : ℕ) → X n) → E} {x₀ : (i : Iic a) → X i}
    (hf : AEStronglyMeasurable f (ionescuTulceaKernel κ a x₀)) :
    ∀ᵐ x ∂partialKernel κ a b x₀, AEStronglyMeasurable f (ionescuTulceaKernel κ b x) := by
  rw [← partialKernel_comp_ionescuTulceaKernel κ hab] at hf
  exact hf.comp

variable [NormedSpace ℝ E]

theorem integral_ionescuTulceaKernel {n : ℕ} (x₀ : (i : Iic n) → X i) {f : ((n : ℕ) → X n) → E}
    (mf : AEStronglyMeasurable f (ionescuTulceaKernel κ n x₀)) :
    ∫ x, f x ∂ionescuTulceaKernel κ n x₀ =
      ∫ x, f (updateFinset x _ x₀) ∂ionescuTulceaKernel κ n x₀ := by
  nth_rw 1 [← ionescuTulceaKernel_eq_map_updateFinset, integral_map]
  · exact measurable_updateFinset'.aemeasurable
  · convert mf
    nth_rw 2 [← ionescuTulceaKernel_eq_map_updateFinset]

lemma test {a b : ℕ} (hab : a ≤ b) (u : Π i : Iic a, X i) :
    (ionescuTulceaKernel κ a u).map (fun x ↦ (frestrictLe b x, x)) =
    (partialKernel κ a b u) ⊗ₘ (ionescuTulceaKernel κ b) := by
  ext s ms
  rw [Measure.map_apply, Measure.compProd_apply, ← partialKernel_comp_ionescuTulceaKernel κ hab,
    Kernel.comp_apply']
  · conv_rhs =>
      enter [2]
      ext a
      rw [← ionescuTulceaKernel_eq_map_updateFinset,
        Measure.map_apply measurable_updateFinset' (measurable_prod_mk_left ms)]
    conv_lhs =>
      enter [2]
      ext a
      rw [← ionescuTulceaKernel_eq_map_updateFinset, Measure.map_apply measurable_updateFinset']
      rfl
      exact ((measurable_frestrictLe b).prod_mk measurable_id) ms
    simp_rw [← Set.preimage_comp]
    congrm ∫⁻ x, (ionescuTulceaKernel _ _ _) ((fun y ↦ ?_) ⁻¹' _) ∂_
    ext i <;> simp [updateFinset]
  · exact ms.preimage (by fun_prop)
  · exact ms
  · fun_prop
  · exact ms


theorem partialKernel_comp_ionescuTulceaKernel_apply {a b : ℕ} (hab : a ≤ b)
    (f : ((i : Iic b) → X i) → ((n : ℕ) → X n) → E)
    (x₀ : (i : Iic a) → X i)
    (hf : Integrable f.uncurry ((partialKernel κ a b x₀) ⊗ₘ (ionescuTulceaKernel κ b))) :
    ∫ x, ∫ y, f x y ∂ionescuTulceaKernel κ b x ∂partialKernel κ a b x₀ =
      ∫ x, f (frestrictLe b x) x ∂ionescuTulceaKernel κ a x₀ := by
  have := hf.1
  rw [← test] at this
  replace this := this.comp_measurable (by fun_prop)
  apply aestronglyMeasurable_ionescuTulceaKernel κ hab at this
  have aux := hf
  rw [← test] at aux
  replace aux := aux.comp_measurable (by fun_prop)
  rw [← partialKernel_comp_ionescuTulceaKernel κ hab, Kernel.integral_comp]
  · apply integral_congr_ae
    filter_upwards [hf.1.compProd, this]
    intro x h1 h2
    rw [integral_ionescuTulceaKernel]
    · nth_rw 2 [integral_ionescuTulceaKernel]
      · simp_rw [frestrictLe_updateFinset]
      · exact h2
    · exact h1
  · rw [partialKernel_comp_ionescuTulceaKernel _ hab]
    exact aux
  · exact hab
  · exact hab

theorem setIntegral_ionescuTulceaKernel {a b : ℕ} (hab : a ≤ b) (u : (Π i : Iic a, X i))
    {f : (Π n, X n) → E} (i_f : Integrable f (ionescuTulceaKernel κ a u))
    (A : Set (Π i : Iic b, X i)) (hA : MeasurableSet A) :
    ∫ x in A, ∫ y, f y ∂ionescuTulceaKernel κ b x ∂partialKernel κ a b u =
      ∫ y in frestrictLe b ⁻¹' A, f y ∂ionescuTulceaKernel κ a u := by
  rw [setIntegral_eq _ hA]
  simp_rw [← integral_smul]
  rw [partialKernel_comp_ionescuTulceaKernel_apply]
  simp_rw [← preimage_indicator]
  rw [← setIntegral_eq]
  · exact measurable_frestrictLe b hA
  · exact hab
  · apply Integrable.smul_of_top_right
    · apply Integrable.comp_measurable _ measurable_snd
      rwa [← Measure.snd, snd_compProd_kernel, partialKernel_comp_ionescuTulceaKernel _ hab]
    · apply memℒp_top_of_bound (C := 1)
      · exact (((measurable_indicator_const_iff 1).2 hA).comp measurable_fst).aestronglyMeasurable
      · refine Eventually.of_forall fun x ↦ ?_
        by_cases hx : x.1 ∈ A <;> simp [hx]

variable [CompleteSpace E]

theorem condExp_ionescuTulceaKernel
    {a b : ℕ} (hab : a ≤ b) (x₀ : (i : Iic a) → X i) {f : ((n : ℕ) → X n) → E}
    (i_f : Integrable f (ionescuTulceaKernel κ a x₀)) :
    (ionescuTulceaKernel κ a x₀)[f|ℱ b] =ᵐ[ionescuTulceaKernel κ a x₀]
      fun x ↦ ∫ y, f y ∂ionescuTulceaKernel κ b (frestrictLe b x) := by
  have mf : AEStronglyMeasurable
      (fun x => ∫ (y : (n : ℕ) → X n), f y ∂(ionescuTulceaKernel κ b) x)
      ((partialKernel κ a b) x₀) := by
    rw [← partialKernel_comp_ionescuTulceaKernel _ hab] at i_f
    exact i_f.1.comp_mk_left
  have mf' : AEStronglyMeasurable
      (fun x => ∫ (y : (n : ℕ) → X n), f y ∂(ionescuTulceaKernel κ b) x)
      (Measure.map (frestrictLe b) ((ionescuTulceaKernel κ a) x₀)) := by
    rw [← Kernel.map_apply, ionescuTulceaKernel_proj]
    · exact mf
    · exact measurable_frestrictLe _
  refine (ae_eq_condExp_of_forall_setIntegral_eq _ i_f ?_ ?_ ?_).symm
  · rintro s - -
    apply Integrable.integrableOn
    conv => enter [1]; change (fun x ↦ ∫ y, f y ∂ionescuTulceaKernel κ b x) ∘ (frestrictLe b)
    rw [← partialKernel_comp_ionescuTulceaKernel κ hab, Kernel.integrable_comp_iff] at i_f
    · rw [← integrable_map_measure, ← Kernel.map_apply, ionescuTulceaKernel_proj,
        ← integrable_norm_iff]
      · apply i_f.2.mono'
        · exact AEStronglyMeasurable.norm mf
        · refine Eventually.of_forall fun x ↦ ?_
          rw [norm_norm]
          exact norm_integral_le_integral_norm _
      · exact mf
      · exact measurable_frestrictLe _
      · exact mf'
      · exact (measurable_frestrictLe b).aemeasurable
    · exact i_f.1
  · rintro - ⟨t, mt, rfl⟩ -
    rw [← setIntegral_map mt (f := fun x ↦ ∫ y, f y ∂(ionescuTulceaKernel κ _ x)),
      ← Kernel.map_apply, ionescuTulceaKernel_proj, setIntegral_ionescuTulceaKernel κ hab _ i_f]
    · exact mt
    · exact measurable_frestrictLe _
    · rw [← Kernel.map_apply _ (measurable_frestrictLe _)]
      apply AEStronglyMeasurable.comp_mk_left
      rw [ionescuTulceaKernel_proj, partialKernel_comp_ionescuTulceaKernel _ hab]
      exact i_f.1
    · exact (measurable_frestrictLe _).aemeasurable
  · conv => enter [2]; change (fun x ↦ ∫ y, f y ∂ionescuTulceaKernel κ b x) ∘ (frestrictLe b)
    apply AEStronglyMeasurable.comp_ae_measurable'
    · exact mf'
    · exact (measurable_frestrictLe b).aemeasurable


theorem condExp_ionescuTulceaKernel' {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    (x₀ : (i : Iic a) → X i) {f : ((n : ℕ) → X n) → E} :
    (ionescuTulceaKernel κ a x₀)[f|ℱ b] =ᵐ[ionescuTulceaKernel κ a x₀]
      fun x ↦ ∫ y, ((ionescuTulceaKernel κ a x₀)[f|ℱ c]) (updateFinset x _ y)
        ∂partialKernel κ b c (frestrictLe b x) := by
  have i_cf : Integrable ((ionescuTulceaKernel κ a x₀)[f|ℱ c])
      (ionescuTulceaKernel κ a x₀) := integrable_condExp
  have mcf : StronglyMeasurable ((ionescuTulceaKernel κ a x₀)[f|ℱ c]) :=
    stronglyMeasurable_condExp.mono (ℱ.le c)
  filter_upwards [ℱ.condExp_condExp f hbc, condExp_ionescuTulceaKernel κ hab x₀ i_cf]
  intro x h1 h2
  rw [← h1, h2, ← ionescuTulceaKernel_proj, Kernel.map_apply, integral_map]
  · congr with y
    apply stronglyMeasurable_dependsOn stronglyMeasurable_condExp
    simp [updateFinset]
    exact fun i hi ↦ (if_pos hi).symm
  · exact (measurable_frestrictLe c).aemeasurable
  · exact (mcf.comp_measurable measurable_updateFinset).aestronglyMeasurable
  · exact measurable_frestrictLe _
