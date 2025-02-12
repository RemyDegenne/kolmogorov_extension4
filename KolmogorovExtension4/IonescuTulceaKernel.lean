/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import KolmogorovExtension4.PTraj
import KolmogorovExtension4.DependsOn
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import KolmogorovExtension4.KolmogorovExtension
import Batteries.Data.Nat.Lemmas

open ENNReal Filter Finset Function MeasurableSpace MeasureTheory Preorder ProbabilityTheory Topology

variable {X : ℕ → Type*}

section castLemmas

private lemma Iic_pi_eq {a b : ℕ} (h : a = b) :
    (Π i : Iic a, X i) = (Π i : Iic b, X i) := by cases h; rfl

private lemma cast_pi {s t : Set ℕ} (h : s = t) (x : (i : s) → X i) (i : t) :
    cast (congrArg (fun u : Set ℕ ↦ (Π i : u, X i)) h) x i = x ⟨i.1, h.symm ▸ i.2⟩ := by
  cases h; rfl

variable [∀ n, MeasurableSpace (X n)]

private lemma measure_cast {a b : ℕ} (h : a = b) (μ : (n : ℕ) → Measure (Π i : Iic n, X i)) :
    (μ a).map (cast (Iic_pi_eq h)) = μ b := by
  subst h
  exact Measure.map_id

private lemma heq_measurableSpace_Iic_pi {a b : ℕ} (h : a = b) :
    HEq (inferInstance : MeasurableSpace (Π i : Iic a, X i))
    (inferInstance : MeasurableSpace (Π i : Iic b, X i)) := by cases h; rfl

end castLemmas

section iterateInduction

/-- This function takes as input a tuple `(x_₀, ..., x_ₐ)` and `ind` a function which
given `(y_₀, ...,y_ₙ)` outputs `x_{n+1} : X (n + 1)`, and it builds an element of `Π n, X n`
by starting with `(x_₀, ..., x_ₐ)` and then iterating `ind`. -/
def iterateInduction {a : ℕ} (x : Π i : Iic a, X i)
    (ind : (n : ℕ) → (Π i : Iic n, X i) → X (n + 1)) : Π n, X n
  | 0 => x ⟨0, mem_Iic.2 <| zero_le a⟩
  | k + 1 => if h : k + 1 ≤ a
      then x ⟨k + 1, mem_Iic.2 h⟩
      else ind k (fun i ↦ iterateInduction x ind i)
  decreasing_by exact Nat.lt_succ.2 (mem_Iic.1 i.2)

lemma frestrictLe_iterateInduction {a : ℕ} (x : Π i : Iic a, X i)
    (ind : (n : ℕ) → (Π i : Iic n, X i) → X (n + 1)) :
    frestrictLe a (iterateInduction x ind) = x := by
  ext i
  simp only [frestrictLe_apply]
  obtain ⟨(zero | j), hj⟩ := i <;> rw [iterateInduction]
  rw [dif_pos (mem_Iic.1 hj)]

end iterateInduction

section ProjectiveFamily

namespace MeasureTheory

/-! ### Projective families indexed by `Finset ℕ` -/

variable [∀ n, MeasurableSpace (X n)] {μ : (n : ℕ) → Measure (Π i : Iic n, X i)}

/-- To check that a measure `ν` is the projective limit of a projective family of measures indexed
by `Finset ℕ`, it is enough to check on intervals of the form `Iic n`, where `n` is larger than
a given integer. -/
theorem isProjectiveLimit_nat_iff' {μ : (I : Finset ℕ) → Measure (Π i : I, X i)}
    (hμ : IsProjectiveMeasureFamily μ) (ν : Measure (Π n, X n)) (a : ℕ) :
    IsProjectiveLimit ν μ ↔ ∀ ⦃n⦄, n ≥ a → ν.map (frestrictLe n) = μ (Iic n) := by
  refine ⟨fun h n _ ↦ h (Iic n), fun h I ↦ ?_⟩
  have := (I.sub_Iic.trans (Iic_subset_Iic.2 (le_max_left (I.sup id) a)))
  rw [← restrict₂_comp_restrict this, ← Measure.map_map, ← frestrictLe, h (le_max_right _ _), ← hμ]
  all_goals fun_prop

/-- To check that a measure `ν` is the projective limit of a projective family of measures indexed
by `Finset ℕ`, it is enough to check on intervals of the form `Iic n`. -/
theorem isProjectiveLimit_nat_iff {μ : (I : Finset ℕ) → Measure (Π i : I, X i)}
    (hμ : IsProjectiveMeasureFamily μ) (ν : Measure (Π n, X n)) :
    IsProjectiveLimit ν μ ↔ ∀ n, ν.map (frestrictLe n) = μ (Iic n) := by
  rw [isProjectiveLimit_nat_iff' hμ _ 0]
  simp

variable (μ : (n : ℕ) → Measure (Π i : Iic n, X i))

/-- Given a family of measures `μ : (n : ℕ) → Measure (Π i : Iic n, X i)`, we can define a family
of measures indexed by `Finset ℕ` by projecting the measures. -/
noncomputable def inducedFamily (S : Finset ℕ) : Measure ((k : S) → X k) :=
    (μ (S.sup id)).map (restrict₂ S.sub_Iic)

instance [∀ n, SFinite (μ n)] (I : Finset ℕ) :
    SFinite (inducedFamily μ I) := by rw [inducedFamily]; infer_instance

instance [∀ n, IsFiniteMeasure (μ n)] (I : Finset ℕ) :
    IsFiniteMeasure (inducedFamily μ I) := by rw [inducedFamily]; infer_instance

instance [∀ n, IsZeroOrProbabilityMeasure (μ n)] (I : Finset ℕ) :
    IsZeroOrProbabilityMeasure (inducedFamily μ I) := by rw [inducedFamily]; infer_instance

instance [∀ n, IsProbabilityMeasure (μ n)] (I : Finset ℕ) :
    IsProbabilityMeasure (inducedFamily μ I) := by
  rw [inducedFamily]
  exact isProbabilityMeasure_map (measurable_restrict₂ _).aemeasurable

/-- Given a family of measures `μ : (n : ℕ) → Measure (Π i : Iic n, X i)`, the induced family
equals `μ` over the intervals `Iic n`. -/
theorem inducedFamily_Iic (n : ℕ) : inducedFamily μ (Iic n) = μ n := by
  rw [inducedFamily, ← measure_cast (sup_Iic n) μ]
  congr with x i
  rw [restrict₂, cast_pi (by rw [sup_Iic n])]

/-- Given a family of measures `μ : (n : ℕ) → Measure (Π i : Iic n, X i)`, the induced family
will be projective only if `μ` is projective, in the sense that if `a ≤ b`, then projecting
`μ b` gives `μ a`. -/
theorem isProjectiveMeasureFamily_inducedFamily
    (h : ∀ a b : ℕ, ∀ hab : a ≤ b, (μ b).map (frestrictLe₂ hab) = μ a) :
    IsProjectiveMeasureFamily (inducedFamily μ) := by
  intro I J hJI
  have sls : J.sup id ≤ I.sup id := sup_mono hJI
  simp only [inducedFamily]
  rw [Measure.map_map, restrict₂_comp_restrict₂,
    ← restrict₂_comp_restrict₂ J.sub_Iic (Iic_subset_Iic.2 sls), ← Measure.map_map, ← frestrictLe₂,
    h (J.sup id) (I.sup id) sls]
  all_goals fun_prop

end MeasureTheory

end ProjectiveFamily

namespace ProbabilityTheory.Kernel

section definition

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
  (κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1))) [∀ n, IsMarkovKernel (κ n)]

/-- Given a family of kernels `κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1))`, and the
trajectory up to time `a` we can construct an additive content over cylinders. It corresponds
to composing the kernels, starting at time `a + 1`. -/
noncomputable def trajContent {a : ℕ} (x₀ : Π i : Iic a, X i) :
    AddContent (measurableCylinders X) :=
  kolContent (isProjectiveMeasureFamily_inducedFamily _
    (fun _ _ ↦ ptraj_map_frestrictLe₂_apply (κ := κ) x₀))

/-- The `trajContent κ x₀` of a cylinder indexed by first coordinates is given by `ptraj`. -/
theorem trajContent_cylinder {a b : ℕ} (x₀ : Π i : Iic a, X i)
    {S : Set (Π i : Iic b, X i)} (mS : MeasurableSet S) :
    trajContent κ x₀ (cylinder _ S) = ptraj κ a b x₀ S := by
  rw [trajContent, kolContent_cylinder _ mS, inducedFamily_Iic]

/-- The `trajContent` of a cylinder is equal to the integral of its indicator function against
`ptraj`. -/
theorem trajContent_eq_lmarginalPTraj {b : ℕ} {S : Set (Π i : Iic b, X i)}
    (mS : MeasurableSet S) (x₀ : Π n, X n) (a : ℕ) :
    trajContent κ (frestrictLe a x₀) (cylinder _ S) =
      lmarginalPTraj κ a b ((cylinder _ S).indicator 1) x₀ := by
  rw [trajContent_cylinder _ _ mS, ← lintegral_indicator_one mS, lmarginalPTraj]
  congr with x
  apply indicator_const_eq
  rw [mem_cylinder]
  congrm (fun i ↦ ?_) ∈ S
  simp [updateFinset, i.2]

/-- The cylinders of a product space indexed by `ℕ` can be seen as depending on the first
coordinates. -/
theorem cylinders_nat :
    measurableCylinders X = ⋃ (a) (S) (_ : MeasurableSet S), {cylinder (Iic a) S} := by
  ext s
  simp only [mem_measurableCylinders, exists_prop, Set.mem_iUnion, mem_singleton]
  refine ⟨?_, fun ⟨N, S, mS, s_eq⟩ ↦ ⟨Iic N, S, mS, s_eq⟩⟩
  rintro ⟨t, S, mS, rfl⟩
  refine ⟨t.sup id, restrict₂ t.sub_Iic ⁻¹' S, measurable_restrict₂ _ mS, ?_⟩
  unfold cylinder
  rw [← Set.preimage_comp, restrict₂_comp_restrict]
  exact Set.mem_singleton _

lemma trajContent_ne_top {a : ℕ} (x : Π i : Iic a, X i)
    {s : Set (Π n, X n)} (hs : s ∈ measurableCylinders X) :
    trajContent κ x s ≠ ⊤ := by
  obtain ⟨N, S, mS, rfl⟩ : ∃ N S, MeasurableSet S ∧ s = cylinder (Iic N) S := by
    simpa [cylinders_nat] using hs
  simp [trajContent_cylinder _ _ mS]

/-- This is an auxiliary result for `trajContent_tendsto_zero`. Consider `f` a sequence of bounded
measurable functions such that `f n` depends only on the first coordinates up to `a n`.
Assume that when integrating `f n` against `ptraj (k + 1) (a n)`, one gets a non-increasing
sequence of functions wich converges to `l`.
Assume then that there exists `ε` and `y : Π i : Iic k, X i` such that
when integrating `f n` against `ptraj k (a n) y`, you get something at least
`ε` for all `n`. Then there exists `z` such that this remains true when integrating
`f` against `ptraj (k + 1) (a n) (update y (k + 1) z)`. -/
theorem le_lmarginalPTraj_succ {f : ℕ → (Π n, X n) → ℝ≥0∞} {a : ℕ → ℕ}
    (hcte : ∀ n, DependsOn (f n) (Iic (a n))) (mf : ∀ n, Measurable (f n))
    {bound : ℝ≥0∞} (fin_bound : bound ≠ ∞) (le_bound : ∀ n x, f n x ≤ bound) {k : ℕ}
    (anti : ∀ x, Antitone (fun n ↦ lmarginalPTraj κ (k + 1) (a n) (f n) x))
    {l : (Π n, X n) → ℝ≥0∞}
    (htendsto : ∀ x, Tendsto (fun n ↦ lmarginalPTraj κ (k + 1) (a n) (f n) x) atTop (𝓝 (l x)))
    (ε : ℝ≥0∞) (y : Π i : Iic k, X i)
    (hpos : ∀ x n, ε ≤ lmarginalPTraj κ k (a n) (f n) (updateFinset x _ y)) :
    ∃ z, ∀ x n,
      ε ≤ lmarginalPTraj κ (k + 1) (a n) (f n) (update (updateFinset x _ y) (k + 1) z) := by
  have _ n : Nonempty (X n) := by
    induction n using Nat.case_strong_induction_on with
    | hz => exact ⟨y ⟨0, mem_Iic.2 (zero_le _)⟩⟩
    | hi m hm =>
      have : Nonempty (Π i : Iic m, X i) :=
        ⟨fun i ↦ @Classical.ofNonempty _ (hm i.1 (mem_Iic.1 i.2))⟩
      exact ProbabilityMeasure.nonempty ⟨κ m Classical.ofNonempty, inferInstance⟩
  -- `Fₙ` is the integral of `fₙ` from time `k + 1` to `aₙ`.
  let F n : (Π n, X n) → ℝ≥0∞ := lmarginalPTraj κ (k + 1) (a n) (f n)
  -- `Fₙ` converges to `l` by hypothesis.
  have tendstoF x : Tendsto (F · x) atTop (𝓝 (l x)) := htendsto x
  -- Integrating `fₙ` between time `k` and `aₙ` is the same as integrating
  -- `Fₙ` between time `k` and time `k + 1`.
  have f_eq x n : lmarginalPTraj κ k (a n) (f n) x = lmarginalPTraj κ k (k + 1) (F n) x := by
    simp_rw [F]
    obtain h | h | h := lt_trichotomy (k + 1) (a n)
    · rw [← lmarginalPTraj_self k.le_succ h.le (mf n)]
    · rw [← h, lmarginalPTraj_le _ le_rfl (mf n)]
    · rw [lmarginalPTraj_le _ _ (mf n), (hcte n).lmarginalPTraj_le _ (mf n),
        (hcte n).lmarginalPTraj_le _ (mf n)]
      all_goals omega
  -- `F` is also a bounded sequence.
  have F_le n x : F n x ≤ bound := by
    simpa [F, lmarginalPTraj] using lintegral_le _ fun z ↦ le_bound _ _
  -- By dominated convergence, the integral of `fₙ` between time `k` and time `a n` converges
  -- to the integral of `l` between time `k` and time `k + 1`.
  have tendsto_int x : Tendsto (fun n ↦ lmarginalPTraj κ k (a n) (f n) x) atTop
      (𝓝 (lmarginalPTraj κ k (k + 1) l x)) := by
    simp_rw [f_eq, lmarginalPTraj]
    exact tendsto_lintegral_of_dominated_convergence (fun _ ↦ bound)
      (fun n ↦ (measurable_lmarginalPTraj _ _ (mf n)).comp measurable_updateFinset)
      (fun n ↦ Eventually.of_forall <| fun y ↦ F_le n _)
      (by simp [fin_bound]) (Eventually.of_forall (fun _ ↦ tendstoF _))
  -- By hypothesis, we have `ε ≤ lmarginalPTraj κ k (k + 1) (F n) (updateFinset x _ y)`,
  -- so this is also true for `l`.
  have ε_le_lint x : ε ≤ lmarginalPTraj κ k (k + 1) l (updateFinset x _ y) :=
    ge_of_tendsto (tendsto_int _) (by simp [hpos])
  let x_ : Π n, X n := Classical.ofNonempty
  -- We now have that the integral of `l` with respect to a probability measure is greater than `ε`,
  -- therefore there exists `x` such that `ε ≤ l(y, x)`.
  obtain ⟨x, hx⟩ : ∃ x, ε ≤ l (update (updateFinset x_ _ y) (k + 1) x) := by
    have : ∫⁻ x, l (update (updateFinset x_ _ y) (k + 1) x) ∂(κ k y) ≠ ∞ :=
      ne_top_of_le_ne_top fin_bound <| lintegral_le _
        fun y ↦ le_of_tendsto' (tendstoF _) <| fun _ ↦ F_le _ _
    obtain ⟨x, hx⟩ := exists_lintegral_le this
    refine ⟨x, (ε_le_lint x_).trans ?_⟩
    rwa [lmarginalPTraj_succ, frestrictLe_updateFinset]
    exact ENNReal.measurable_of_tendsto (by fun_prop) (tendsto_pi_nhds.2 htendsto)
  refine ⟨x, fun x' n ↦ ?_⟩
  -- As `F` is a non-increasing sequence, we have `ε ≤ Fₙ(y, x)` for any `n`.
  have := le_trans hx ((anti _).le_of_tendsto (tendstoF _) n)
  -- This part below is just to say that this is true for any `x : (i : ι) → X i`,
  -- as `Fₙ` technically depends on all the variables, but really depends only on the first `k + 1`.
  convert this using 1
  refine (hcte n).dependsOn_lmarginalPTraj _ (mf n) fun i hi ↦ ?_
  simp only [update, updateFinset, mem_Iic, F]
  split_ifs with h1 h2 <;> try rfl
  rw [mem_coe, mem_Iic] at hi
  omega

/-- The indicator of a cylinder only depends on the variables whose the cylinder depends on. -/
theorem dependsOn_cylinder_indicator {ι : Type*} {α : ι → Type*} {I : Finset ι}
    (S : Set ((i : I) → α i)) :
    DependsOn ((cylinder I S).indicator (1 : ((Π i, α i) → ℝ≥0∞))) I :=
  fun x y hxy ↦ indicator_const_eq _ (by simp [restrict_def, hxy])

/-- This is the key theorem to prove the existence of the `trajKernel`:
the `trajContent` of a decreasing sequence of cylinders with empty intersection
converges to `0`.

This implies the `σ`-additivity of `trajContent` (see `sigma_additive_addContent_of_tendsto_zero`),
which allows to extend it to the `σ`-algebra by Carathéodory's theorem. -/
theorem trajContent_tendsto_zero {A : ℕ → Set (Π n, X n)}
    (A_mem : ∀ n, A n ∈ measurableCylinders X) (A_anti : Antitone A) (A_inter : ⋂ n, A n = ∅)
    {p : ℕ} (x₀ : Π i : Iic p, X i) :
    Tendsto (fun n ↦ trajContent κ x₀ (A n)) atTop (𝓝 0) := by
  have _ n : Nonempty (X n) := by
    induction n using Nat.case_strong_induction_on with
    | hz => exact ⟨x₀ ⟨0, mem_Iic.2 (zero_le _)⟩⟩
    | hi m hm =>
      have : Nonempty (Π i : Iic m, X i) :=
        ⟨fun i ↦ @Classical.ofNonempty _ (hm i.1 (mem_Iic.1 i.2))⟩
      exact ProbabilityMeasure.nonempty ⟨κ m Classical.ofNonempty, inferInstance⟩
  -- `Aₙ` is a cylinder, it can be written as `cylinder (Iic (a n)) Sₙ`.
  have A_cyl n : ∃ a S, MeasurableSet S ∧ A n = cylinder (Iic a) S := by
    simpa [cylinders_nat] using A_mem n
  choose a S mS A_eq using A_cyl
  -- We write `χₙ` for the indicator function of `Aₙ`.
  let χ n := (A n).indicator (1 : (Π n, X n) → ℝ≥0∞)
  -- `χₙ` is measurable.
  have mχ n : Measurable (χ n) := by
    simp_rw [χ, A_eq]
    exact (measurable_indicator_const_iff 1).2 <| (mS n).cylinder
  -- `χₙ` only depends on the first coordinates.
  have χ_dep n : DependsOn (χ n) (Iic (a n)) := by
    simp_rw [χ, A_eq]
    exact dependsOn_cylinder_indicator _
  -- Therefore its integral against `ptraj κ k (a n)` is constant.
  have lma_const x y n :
      lmarginalPTraj κ p (a n) (χ n) (updateFinset x _ x₀) =
      lmarginalPTraj κ p (a n) (χ n) (updateFinset y _ x₀) := by
    refine (χ_dep n).dependsOn_lmarginalPTraj p (mχ n) fun i hi ↦ ?_
    rw [mem_coe, mem_Iic] at hi
    simp [updateFinset, hi]
  -- As `(Aₙ)` is non-increasing, so is `(χₙ)`.
  have χ_anti : Antitone χ := fun m n hmn y ↦ by
    apply Set.indicator_le fun a ha ↦ ?_
    simp [χ, A_anti hmn ha]
  -- Integrating `χₙ` further than the last coordinate it depends on does nothing.
  -- This is used to then show that the integral of `χₙ` from time `k` is non-increasing.
  have lma_inv k M n (h : a n ≤ M) : lmarginalPTraj κ k M (χ n) = lmarginalPTraj κ k (a n) (χ n) :=
    (χ_dep n).lmarginalPTraj_right (mχ n) h le_rfl
  -- the integral of `χₙ` from time `k` is non-increasing.
  have anti_lma k x : Antitone fun n ↦ lmarginalPTraj κ k (a n) (χ n) x := by
    intro m n hmn
    simp only
    rw [← lma_inv k ((a n).max (a m)) n (le_max_left _ _),
      ← lma_inv k ((a n).max (a m)) m (le_max_right _ _)]
    exact lmarginalPTraj_mono _ _ (χ_anti hmn) _
  -- Therefore it converges to some function `lₖ`.
  have this k x : ∃ l, Tendsto (fun n ↦ lmarginalPTraj κ k (a n) (χ n) x) atTop (𝓝 l) := by
    obtain h | h := tendsto_of_antitone (anti_lma k x)
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
  have hpos x n : ε ≤ lmarginalPTraj κ p (a n) (χ n) (updateFinset x _ x₀) :=
    hε x ▸ ((anti_lma p _).le_of_tendsto (hl p _)) n
  -- Also, the indicators are bounded by `1`.
  have χ_le n x : χ n x ≤ 1 := by
    apply Set.indicator_le
    simp
  -- We have all the conditions to apply `le_lmarginalPTraj_succ`.
  -- This allows us to recursively build a sequence `z` with the following property:
  -- for any `k ≥ p` and `n`, integrating `χ n` from time `k` to time `a n`
  -- with the trajectory up to `k` being equal to `z` gives something greater than `ε`.
  choose! ind hind using
    fun k y h ↦ le_lmarginalPTraj_succ κ χ_dep mχ (by norm_num : (1 : ℝ≥0∞) ≠ ∞)
      χ_le (anti_lma (k + 1)) (hl (k + 1)) ε y h
  let z := iterateInduction x₀ ind
  have main k (hk : p ≤ k) : ∀ x n,
      ε ≤ lmarginalPTraj κ k (a n) (χ n) (updateFinset x _ (frestrictLe k z)) := by
    induction k, hk using Nat.le_induction with
    | base => exact fun x n ↦ by simpa [z, frestrictLe_iterateInduction] using hpos x n
    | succ k hn h =>
      intro x n
      rw [← update_updateFinset_eq]
      convert hind k (fun i ↦ z i.1) h x n
      simp [z, iterateInduction, Nat.lt_succ.2 hn]
  -- We now want to prove that the integral of `χₙ`, which is equal to the `trajContent`
  -- of `Aₙ`, converges to `0`.
  have aux x n : trajContent κ x₀ (A n) = lmarginalPTraj κ p (a n) (χ n) (updateFinset x _ x₀) := by
    simp_rw [χ, A_eq]
    nth_rw 1 [← frestrictLe_updateFinset x x₀]
    exact trajContent_eq_lmarginalPTraj _ (mS n) ..
  simp_rw [aux z]
  convert hl p _
  rw [hε]
  -- Which means that we want to prove that `ε = 0`. But if `ε > 0`, then for any `n`,
  -- choosing `k > aₙ` we get `ε ≤ χₙ(z₀, ..., z_{aₙ})` and therefore `z ∈ Aₙ`.
  -- This contradicts the fact that `(Aₙ)` has an empty intersection.
  by_contra!
  have mem n : z ∈ A n := by
    have : 0 < χ n z := by
      rw [← lmarginalPTraj_le κ (le_max_right p (a n)) (mχ n),
        ← updateFinset_frestrictLe (i := a n) z]
      simpa using lt_of_lt_of_le this.symm.bot_lt (main _ (le_max_left _ _) z n)
    exact Set.mem_of_indicator_ne_zero (ne_of_lt this).symm
  exact (A_inter ▸ Set.mem_iInter.2 mem).elim

/-- The `trajContent` is sigma-subadditive. -/
theorem trajContent_sigma_subadditive {a : ℕ} (x₀ : Π i : Iic a, X i)
    ⦃f : ℕ → Set (Π n, X n)⦄ (hf : ∀ n, f n ∈ measurableCylinders X)
    (hf_Union : (⋃ n, f n) ∈ measurableCylinders X) :
    trajContent κ x₀ (⋃ n, f n) ≤ ∑' n, trajContent κ x₀ (f n) := by
  refine addContent_iUnion_le_of_addContent_iUnion_eq_tsum
    isSetRing_measurableCylinders (fun f hf hf_Union hf' ↦ ?_) f hf hf_Union
  refine addContent_iUnion_eq_sum_of_tendsto_zero isSetRing_measurableCylinders
    (trajContent κ x₀) (fun s hs ↦ trajContent_ne_top _ _ hs) ?_ hf hf_Union hf'
  exact fun s hs anti_s inter_s ↦ trajContent_tendsto_zero κ hs anti_s inter_s x₀

/-- This function is the kernel given by the Ionescu-Tulcea theorem. -/
noncomputable def trajFun (a : ℕ) (x₀ : Π i : Iic a, X i) :
    Measure (Π n, X n) :=
  (trajContent κ x₀).measure isSetSemiring_measurableCylinders generateFrom_measurableCylinders.ge
    (trajContent_sigma_subadditive κ x₀)

theorem isProbabilityMeasure_trajFun (a : ℕ) (x₀ : Π i : Iic a, X i) :
    IsProbabilityMeasure (trajFun κ a x₀) where
  measure_univ := by
    rw [← cylinder_univ (Iic 0), trajFun, AddContent.measure_eq,
      trajContent_cylinder _ _ MeasurableSet.univ]
    · exact measure_univ
    · exact generateFrom_measurableCylinders.symm
    · exact cylinder_mem_measurableCylinders _ _ MeasurableSet.univ

theorem isProjectiveLimit_trajFun (a : ℕ) (x₀ : Π i : Iic a, X i) :
    IsProjectiveLimit (trajFun κ a x₀) (inducedFamily (fun n ↦ ptraj κ a n x₀)) := by
  refine isProjectiveLimit_nat_iff (isProjectiveMeasureFamily_inducedFamily _
    (fun _ _ ↦ ptraj_map_frestrictLe₂_apply x₀)) _ |>.2 fun n ↦ ?_
  ext s ms
  rw [Measure.map_apply (measurable_frestrictLe n) ms]
  have h_mem : (frestrictLe n) ⁻¹' s ∈ measurableCylinders X :=
    cylinder_mem_measurableCylinders _ _ ms
  rw [trajFun, AddContent.measure_eq, trajContent, kolContent_congr _ (frestrictLe n ⁻¹' s) rfl ms]
  · exact generateFrom_measurableCylinders.symm
  · exact cylinder_mem_measurableCylinders _ _ ms

theorem measurable_trajFun (a : ℕ) : Measurable (trajFun κ a) := by
  apply Measure.measurable_of_measurable_coe
  refine MeasurableSpace.induction_on_inter
    (C := fun t ht ↦ Measurable (fun x₀ ↦ trajFun κ a x₀ t))
    (s := measurableCylinders X) generateFrom_measurableCylinders.symm
    isPiSystem_measurableCylinders (by simp) (fun t ht ↦ ?cylinder) (fun t mt ht ↦ ?compl)
    (fun f disf mf hf ↦ ?union)
  · obtain ⟨N, S, mS, t_eq⟩ : ∃ N S, MeasurableSet S ∧ t = cylinder (Iic N) S := by
      simpa [cylinders_nat] using ht
    simp_rw [trajFun, AddContent.measure_eq _ _ generateFrom_measurableCylinders.symm _ ht,
      trajContent, kolContent_congr _ t t_eq mS, inducedFamily]
    refine Measure.measurable_measure.1 ?_ _ mS
    exact (Measure.measurable_map _ (measurable_restrict₂ _)).comp (measurable _)
  · have := isProbabilityMeasure_trajFun κ a
    simpa [measure_compl mt (measure_ne_top _ _)] using Measurable.const_sub ht _
  · simpa [measure_iUnion disf mf] using Measurable.ennreal_tsum hf

/-- *Ionescu-Tulcea Theorem* : Given a family of kernels `κ k` taking variables in `Iic k` with
value in `X (k+1)`, the kernel `trajKernel κ p` takes a variable `x` depending on the
variables `i ≤ p` and associates to it a kernel on trajectories depending on all variables,
where the entries with index `≤ p` are those of `x`, and then one follows iteratively the
kernels `κ p`, then `κ (p+1)`, and so on.

The fact that such a kernel exists on infinite trajectories is not obvious, and is the content of
the Ionescu-Tulcea theorem. -/
noncomputable def trajKernel (a : ℕ) : Kernel (Π i : Iic a, X i) (Π n, X n) where
  toFun := trajFun κ a
  measurable' := measurable_trajFun κ a

theorem trajKernel_apply (a : ℕ) (x₀ : Π i : Iic a, X i) :
    trajKernel κ a x₀ = trajFun κ a x₀ := rfl

instance (p : ℕ) : IsMarkovKernel (trajKernel κ p) :=
  ⟨fun _ ↦ isProbabilityMeasure_trajFun ..⟩

theorem frestrictLe_trajKernel (a b : ℕ) :
    (trajKernel κ a).map (frestrictLe b) = ptraj κ a b := by
  ext1 x₀
  rw [map_apply _ (measurable_frestrictLe _), trajKernel_apply, frestrictLe,
    isProjectiveLimit_trajFun, inducedFamily_Iic]

theorem frestrictLe_trajKernel_le {a b : ℕ} (hab : a ≤ b) :
    (trajKernel κ b).map (frestrictLe a) =
      deterministic (frestrictLe₂ hab) (measurable_frestrictLe₂ _) := by
  rw [frestrictLe_trajKernel, ptraj_le]

theorem eq_trajKernel' {a : ℕ} (n : ℕ) (η : Kernel (Π i : Iic a, X i) (Π n, X n))
    (hη : ∀ b ≥ n, η.map (frestrictLe b) = ptraj κ a b) :
    η = trajKernel κ a := by
  ext1 x₀
  refine ((isProjectiveLimit_trajFun _ _ _).unique ?_).symm
  rw [isProjectiveLimit_nat_iff' _ _ n]
  · intro k hk
    rw [inducedFamily_Iic, ← map_apply _ (measurable_frestrictLe k), hη k hk]
  · exact (isProjectiveMeasureFamily_inducedFamily _ (fun _ _ ↦ ptraj_map_frestrictLe₂_apply x₀))

theorem eq_trajKernel {a : ℕ} (η : Kernel (Π i : Iic a, X i) (Π n, X n))
    (hη : ∀ b, η.map (frestrictLe b) = ptraj κ a b) :
    η = trajKernel κ a := eq_trajKernel' κ 0 η fun b _ ↦ hη b

theorem trajKernel_comp_ptraj {a b : ℕ} (hab : a ≤ b) :
    (trajKernel κ b) ∘ₖ (ptraj κ a b) = trajKernel κ a := by
  refine eq_trajKernel _ _ fun n ↦ ?_
  ext x₀ s ms
  simp_rw [map_apply' _ (measurable_frestrictLe _) _ ms,
    comp_apply' _ _ _ (measurable_frestrictLe n ms),
    ← Measure.map_apply (measurable_frestrictLe n) ms,
    ← map_apply (trajKernel κ b) (measurable_frestrictLe n), frestrictLe_trajKernel κ b n,
    ← comp_apply' _ _ _ ms, ptraj_comp_ptraj' n hab]

end definition

section Filtration

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
theorem stronglyMeasurable_dependsOn {i : ι} {f : ((i : ι) → X i) → E}
    (mf : StronglyMeasurable[Filtration.pi_preorder i] f) : DependsOn f (Set.Iic i) :=
  fun _ _ h ↦ eq_of_stronglyMeasurable_comap _ mf (dependsOn_frestrictLe i h)

end Filtration

open Filtration

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
variable (κ : (k : ℕ) → Kernel ((i : Iic k) → X i) (X (k + 1)))
variable [∀ k, IsMarkovKernel (κ k)]

/-- This theorem shows that `trajKernel κ n` is, up to an equivalence, the product of
a determinstic kernel with another kernel. This is an intermediate result to compute integrals
with respect to this kernel. -/
theorem trajKernel_eq (n : ℕ) :
    trajKernel κ n =
      (Kernel.id ×ₖ (trajKernel κ n).map (Set.Ioi n).restrict).map (IicProdIoi n) := by
  refine (eq_trajKernel' _ (n + 1) _ fun a ha ↦ ?_).symm
  ext x s ms
  rw [Kernel.map_map, map_apply' _ _ _ ms, id_prod_apply', map_apply']
  · have : (frestrictLe a) ∘ (IicProdIoi n) ∘ (Prod.mk x) ∘ (Set.Ioi n).restrict =
        (fun y (i : Iic a) ↦ if hi : i.1 ≤ n then x ⟨i.1, mem_Iic.2 hi⟩ else y i) ∘
          (frestrictLe a) := by
      ext x i
      by_cases hi : i.1 ≤ n <;> simp [hi, IicProdIoi]
    have hyp : Measurable (fun (y : Π i : Iic a, X i) (i : Iic a) ↦
        if hi : i.1 ≤ n then x ⟨i.1, mem_Iic.2 hi⟩ else y i) := by
      refine measurable_pi_lambda _ (fun i ↦ ?_)
      by_cases hi : i.1 ≤ n <;> simp only [hi, ↓reduceDIte, measurable_const]
      exact measurable_pi_apply _
    rw [← Set.preimage_comp, ← Set.preimage_comp, Function.comp_assoc, this,
      ← map_apply' _ _ _ ms, ← map_map _ _ hyp, frestrictLe_trajKernel, map_apply' _ _ _ ms,
      ptraj_eq_prod, map_apply' _ _ _ (hyp ms), id_prod_apply',
      map_apply' _ _ _ ms, id_prod_apply']
    · congr with y
      simp only [IicProdIoc_def, Set.mem_preimage]
      congrm (fun i ↦ ?_) ∈ s
      by_cases hi : i.1 ≤ n <;> simp [hi]
    any_goals fun_prop
    · exact measurable_IicProdIoc ms
    · exact measurable_IicProdIoc <| hyp ms
    · exact hyp
    · exact hyp.comp (measurable_frestrictLe _)
  any_goals fun_prop
  · exact measurable_prod_mk_left <| (IicProdIoi n).measurable <| (measurable_frestrictLe a) ms
  · exact (IicProdIoi n).measurable <| (measurable_frestrictLe a) ms

@[measurability, fun_prop]
theorem measurable_updateFinset' {ι : Type*} [DecidableEq ι] {I : Finset ι}
    {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    {y : Π i : I, X i} : Measurable (fun x ↦ updateFinset x I y) := by
  refine measurable_pi_lambda _ (fun i ↦ ?_)
  by_cases hi : i ∈ I <;> simp only [updateFinset, hi, ↓reduceDIte, measurable_const]
  exact measurable_pi_apply _

theorem trajKernel_map_updateFinset {n : ℕ} (x₀ : Π i : Iic n, X i) :
    (trajKernel κ n x₀).map (fun y ↦ updateFinset y _ x₀) = trajKernel κ n x₀ := by
  ext s ms
  nth_rw 2 [trajKernel_eq]
  have : (fun y ↦ updateFinset y _ x₀) = (IicProdIoi n ∘ (Prod.mk x₀) ∘ (Set.Ioi n).restrict) := by
    ext x i
    simp [IicProdIoi, updateFinset]
  rw [this, map_apply' _ _ _ ms, ← Measure.map_map, Measure.map_apply _ ms, id_prod_apply',
    ← Measure.map_map, Measure.map_apply, map_apply]
  any_goals fun_prop
  all_goals exact (IicProdIoi n).measurable ms

variable {E : Type*} [NormedAddCommGroup E]

theorem integrable_trajKernel {a b : ℕ} (hab : a ≤ b) {f : (Π n, X n) → E}
    (x₀ : Π i : Iic a, X i) (i_f : Integrable f (trajKernel κ a x₀)) :
    ∀ᵐ x ∂trajKernel κ a x₀, Integrable f (trajKernel κ b (frestrictLe b x)) := by
  rw [← trajKernel_comp_ptraj _ hab, integrable_comp_iff] at i_f
  · apply ae_of_ae_map (p := fun x ↦ Integrable f (trajKernel κ b x))
    · exact (measurable_frestrictLe b).aemeasurable
    · convert i_f.1
      rw [← frestrictLe_trajKernel, Kernel.map_apply _ (measurable_frestrictLe _)]
  · exact i_f.aestronglyMeasurable

theorem aestronglyMeasurable_trajKernel {a b : ℕ} (hab : a ≤ b)
    {f : (Π n, X n) → E} {x₀ : Π i : Iic a, X i}
    (hf : AEStronglyMeasurable f (trajKernel κ a x₀)) :
    ∀ᵐ x ∂ptraj κ a b x₀, AEStronglyMeasurable f (trajKernel κ b x) := by
  rw [← trajKernel_comp_ptraj κ hab] at hf
  exact hf.comp

variable [NormedSpace ℝ E]

variable {κ} in
/-- When computing `∫ x, f x ∂trajKernel κ n x₀`, because the trajectory up to time `n` is
determined by `x₀` we can replace `x` by `updateFinset x _ x₀`. -/
theorem integral_trajKernel {n : ℕ} (x₀ : Π i : Iic n, X i) {f : (Π n, X n) → E}
    (mf : AEStronglyMeasurable f (trajKernel κ n x₀)) :
    ∫ x, f x ∂trajKernel κ n x₀ = ∫ x, f (updateFinset x _ x₀) ∂trajKernel κ n x₀ := by
  nth_rw 1 [← trajKernel_map_updateFinset, integral_map]
  · exact measurable_updateFinset'.aemeasurable
  · convert mf
    nth_rw 2 [← trajKernel_map_updateFinset]

lemma ptraj_comp_ptrajProd_trajKernel {a b : ℕ} (hab : a ≤ b) (u : Π i : Iic a, X i) :
    (trajKernel κ a u).map (fun x ↦ (frestrictLe b x, x)) =
      (ptraj κ a b u) ⊗ₘ (trajKernel κ b) := by
  ext s ms
  rw [Measure.map_apply (by fun_prop) ms, Measure.compProd_apply ms, ← trajKernel_comp_ptraj κ hab,
    comp_apply' _ _ _ (ms.preimage (by fun_prop))]
  conv_rhs => enter [2]; ext a; rw [← trajKernel_map_updateFinset]
  conv_lhs =>
    enter [2]
    ext a
    rw [← trajKernel_map_updateFinset, Measure.map_apply measurable_updateFinset']
    rfl
    exact ((measurable_frestrictLe b).prod_mk measurable_id) ms
  simp_rw [Measure.map_apply measurable_updateFinset' (measurable_prod_mk_left ms),
    ← Set.preimage_comp]
  congrm ∫⁻ x, (trajKernel _ _ _) ((fun y ↦ ?_) ⁻¹' _) ∂_
  ext i <;> simp [updateFinset]

variable {κ}

theorem integral_trajKernel_ptraj' {a b : ℕ} (hab : a ≤ b) {x₀ : Π i : Iic a, X i}
    {f : (Π i : Iic b, X i) → (Π n : ℕ, X n) → E}
    (hf : Integrable f.uncurry ((ptraj κ a b x₀) ⊗ₘ (trajKernel κ b))) :
    ∫ x, ∫ y, f x y ∂trajKernel κ b x ∂ptraj κ a b x₀ =
      ∫ x, f (frestrictLe b x) x ∂trajKernel κ a x₀ := by
  have hf1 := hf
  rw [← ptraj_comp_ptrajProd_trajKernel κ hab] at hf1
  replace hf1 := hf1.comp_measurable (by fun_prop)
  have hf2 := aestronglyMeasurable_trajKernel κ hab hf1.1
  rw [← trajKernel_comp_ptraj κ hab, Kernel.integral_comp]
  · apply integral_congr_ae
    filter_upwards [hf.1.compProd, hf2]
    intro x h1 h2
    rw [integral_trajKernel _ h1]
    nth_rw 2 [integral_trajKernel]
    · simp_rw [frestrictLe_updateFinset]
    · exact h2
  · rwa [trajKernel_comp_ptraj _ hab]

theorem integral_trajKernel_ptraj {a b : ℕ} (hab : a ≤ b) {x₀ : Π i : Iic a, X i}
    {f : (Π n : ℕ, X n) → E} (hf : Integrable f (trajKernel κ a x₀)) :
    ∫ x, ∫ y, f y ∂trajKernel κ b x ∂ptraj κ a b x₀ = ∫ x, f x ∂trajKernel κ a x₀ := by
  apply integral_trajKernel_ptraj' hab
  rw [← trajKernel_comp_ptraj κ hab, ← snd_compProd_kernel] at hf
  exact hf.comp_measurable measurable_snd

-- theorem setIntegral_trajKernel_ptraj' {a b : ℕ} (hab : a ≤ b) {u : (Π i : Iic a, X i)}
--     {f : (Π i : Iic b, X i) → (Π n : ℕ, X n) → E}
--     (hf : Integrable f.uncurry ((ptraj κ a b u) ⊗ₘ (trajKernel κ b)))
--     {A : Set (Π n, X n)} (hA : MeasurableSet[pi_preorder b] A) :
--     ∫ x in A, ∫ y, f x y ∂trajKernel κ b (frestrictLe b x) ∂trajKernel κ a u =
--       ∫ y in A, f (frestrictLe b y) y ∂trajKernel κ a u := by
--   simp_rw [setIntegral_eq _ hA, ← integral_smul]
--   rw [integral_trajKernel_ptraj' hab]
--   simp_rw [← preimage_indicator, ← setIntegral_eq _ (measurable_frestrictLe b hA)]
--   refine hf.smul_of_top_right <| memℒp_top_of_bound (C := 1)
--     (((measurable_indicator_const_iff 1).2 hA).comp measurable_fst).aestronglyMeasurable
--     <| Eventually.of_forall fun x ↦ ?_
--   by_cases hx : x.1 ∈ A <;> simp [hx]

theorem setIntegral_trajKernel_ptraj' {a b : ℕ} (hab : a ≤ b) {u : (Π i : Iic a, X i)}
    {f : (Π i : Iic b, X i) → (Π n : ℕ, X n) → E}
    (hf : Integrable f.uncurry ((ptraj κ a b u) ⊗ₘ (trajKernel κ b)))
    {A : Set (Π i : Iic b, X i)} (hA : MeasurableSet A) :
    ∫ x in A, ∫ y, f x y ∂trajKernel κ b x ∂ptraj κ a b u =
      ∫ y in frestrictLe b ⁻¹' A, f (frestrictLe b y) y ∂trajKernel κ a u := by
  simp_rw [setIntegral_eq _ hA, ← integral_smul]
  rw [integral_trajKernel_ptraj' hab]
  simp_rw [← preimage_indicator, ← setIntegral_eq _ (measurable_frestrictLe b hA)]
  refine hf.smul_of_top_right <| memℒp_top_of_bound (C := 1)
    (((measurable_indicator_const_iff 1).2 hA).comp measurable_fst).aestronglyMeasurable
    <| Eventually.of_forall fun x ↦ ?_
  by_cases hx : x.1 ∈ A <;> simp [hx]

theorem setIntegral_trajKernel_ptraj {a b : ℕ} (hab : a ≤ b) {x₀ : (Π i : Iic a, X i)}
    {f : (Π n : ℕ, X n) → E} (hf : Integrable f (trajKernel κ a x₀))
    {A : Set (Π i : Iic b, X i)} (hA : MeasurableSet A) :
    ∫ x in A, ∫ y, f y ∂trajKernel κ b x ∂ptraj κ a b x₀ =
      ∫ y in frestrictLe b ⁻¹' A, f y ∂trajKernel κ a x₀ := by
  refine setIntegral_trajKernel_ptraj' hab ?_ hA
  rw [← trajKernel_comp_ptraj κ hab, ← snd_compProd_kernel] at hf
  exact hf.comp_measurable measurable_snd

variable [CompleteSpace E]

theorem condExp_trajKernel
    {a b : ℕ} (hab : a ≤ b) {x₀ : Π i : Iic a, X i} {f : (Π n, X n) → E}
    (i_f : Integrable f (trajKernel κ a x₀)) :
    (trajKernel κ a x₀)[f|pi_preorder b] =ᵐ[trajKernel κ a x₀]
      fun x ↦ ∫ y, f y ∂trajKernel κ b (frestrictLe b x) := by
  have mf : Integrable (fun x ↦ ∫ y, f y ∂(trajKernel κ b) x)
      (((trajKernel κ a) x₀).map (frestrictLe b)) := by
    rw [← map_apply _ (measurable_frestrictLe _), frestrictLe_trajKernel _ _]
    rw [← trajKernel_comp_ptraj _ hab] at i_f
    exact i_f.integral_comp
  refine ae_eq_condExp_of_forall_setIntegral_eq (pi_preorder.le _) i_f
    (fun s _ _ ↦
      (integrable_map_measure mf.1 (measurable_frestrictLe b).aemeasurable).1 mf |>.integrableOn)
    ?_ (mf.1.comp_ae_measurable' (measurable_frestrictLe b).aemeasurable) |>.symm
  rintro - ⟨t, mt, rfl⟩ -
  simp_rw [Function.comp_apply]
  rw [← setIntegral_map mt mf.1, ← map_apply, frestrictLe_trajKernel,
    setIntegral_trajKernel_ptraj hab i_f mt]
  any_goals fun_prop

variable (κ)

theorem condExp_trajKernel' {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    (x₀ : Π i : Iic a, X i) (f : (Π n, X n) → E) :
    (trajKernel κ a x₀)[f|pi_preorder b] =ᵐ[trajKernel κ a x₀]
      fun x ↦ ∫ y, ((trajKernel κ a x₀)[f|pi_preorder c]) (updateFinset x _ y)
        ∂ptraj κ b c (frestrictLe b x) := by
  have i_cf : Integrable ((trajKernel κ a x₀)[f|pi_preorder c]) (trajKernel κ a x₀) :=
    integrable_condExp
  have mcf : StronglyMeasurable ((trajKernel κ a x₀)[f|pi_preorder c]) :=
    stronglyMeasurable_condExp.mono (pi_preorder.le c)
  filter_upwards [pi_preorder.condExp_condExp f hbc, condExp_trajKernel hab i_cf]
  intro x h1 h2
  rw [← h1, h2, ← frestrictLe_trajKernel, Kernel.map_apply, integral_map]
  · congr with y
    apply stronglyMeasurable_dependsOn stronglyMeasurable_condExp
    simp only [Set.mem_Iic, updateFinset, mem_Iic, frestrictLe_apply, dite_eq_ite]
    exact fun i hi ↦ (if_pos hi).symm
  any_goals fun_prop
  · exact (mcf.comp_measurable measurable_updateFinset).aestronglyMeasurable
