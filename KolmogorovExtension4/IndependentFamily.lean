import KolmogorovExtension4.KolmogorovExtension
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Independence.Basic

open Set

open scoped ENNReal BigOperators

lemma Finset.prod_mem_not_mem_of_eq_one_if_not_mem {β : Type _} {α : Type _} [DecidableEq α] (f g : α → β) {I J : Finset α} (hJI : J ⊆ I) [CommMonoid β] (h1 : ∀ (x : α) (_ : x ∈ J), f x = g x) (h2 : ∀ (x : α) (_ : x ∉ J), f x = 1) : ((∏ i : { x // x ∈ I }, f i) = (∏ i : { x // x ∈ J }, g i)) := by 
  have h : ((Finset.prod I fun x => f x) = (Finset.prod J fun x => g x)) := by 
    apply Eq.symm
    have hg : ∀ (x : α), x ∈ I \ J → f x = 1 := by
      intros x hx1 
      rw [mem_sdiff] at hx1
      exact h2 x hx1.2
    have hfg : ∀ (x : α), x ∈ J → g x = f x := by
      intros x hx1
      exact Eq.symm (h1 x hx1) 
    refine (@Finset.prod_subset_one_on_sdiff β α J I g f _ _ hJI hg hfg)
  simp [h]
  rw [Finset.prod_attach]
  rw [Finset.prod_attach]
  exact h

variable {ι : Type _} {α : ι → Type _}

section Projections

namespace Function

-- projection to an index set I
def projI {I : Set ι} := (fun (f : (i : ι) → α i) (i : I) => f i)

theorem measurable_proj₂' [∀ i, MeasurableSpace (α i)](I J : Finset ι) (hIJ : J ⊆ I) :
    Measurable ((fun (f : (i : I) → α i) (i : J) => f ⟨i, hIJ i.prop⟩)) := by
  rw [measurable_pi_iff]; exact fun i => measurable_pi_apply _

end Function


namespace Set 

theorem pi_univ_Subtype (I : Set ι) : Set.pi (univ : Set I) (fun i => univ) = (univ : Set ((i : I) → α i))  := by
  simp only [pi_univ]

def boxI (I : Set ι) (t : (i : ι) → Set (α i)) : Set ((i : I) → α i) :=
  (univ : Set I).pi (fun (i : I) => t i)

lemma boxI_univ (I : Set ι) : (univ : Set ( (i : I) → α i)) = boxI I (fun (i : ι) => (univ : Set (α i))) := by
  simp only [boxI, pi_univ]

lemma exists_sub_pi [∀ i, Inhabited (α i)] (I : Set ι) (y : (i : I) → α i) : ∃ x : (i : ι) → α i, (fun (f : (i : ι) → α i) (i : I) => f i) x = y := by
  classical
  use fun (i : ι) => dite (i ∈ I) (fun h => y ⟨i, h⟩)  (fun _ => (default : (α i)))
  simp only [Subtype.coe_prop, dite_true]

lemma rightinverse_of_proj [DecidableEq ι] [∀ i, Inhabited (α i)] (I : Set ι) : ∃ f : ((i : I) → α i) →  ((i : ι) → α i), Function.projI ∘ f = id := by
  classical
  use (fun (t : (i : I) → α i) (i : ι) => dite (i ∈ I) (fun h => t ⟨i, h⟩) (fun _ => (default : (α i))))
  simp [Function.projI]
  ext x i
  simp only [Function.comp_apply, Subtype.coe_prop, dite_true, id_eq]
  
lemma exists_sub_pi' [DecidableEq ι] [∀ i, Inhabited (α i)] (I : Set ι) (Y : Set ((i : I) →  (α i))) : ∃ t : Set ((i : ι) → (α i)), Function.projI '' t = Y := by
  obtain f := fun y => (@exists_sub_pi ι α _ I y)
  choose x_from_y _ using f
  rcases @rightinverse_of_proj ι α _ _ I with ⟨f, g⟩ 
  use f '' Y
  rw [Eq.symm (image_comp _ _ _), g]
  simp only [id_eq, image_id']

lemma mem_boxI {I : Set ι} (t : (i : ι) → Set (α i)) (x : (i : ι) → α i) : (Function.projI x ∈ (boxI I t) ↔ (∀ i ∈ I, (x i ∈ t i))) := by
  simp only [Function.projI, boxI, mem_pi, mem_univ, forall_true_left, Subtype.forall]

def boxIJ {I J : Set ι} (hJI : J ⊆ I) (t : (i : ι) → Set (α i)) : Set ((i : I) → α i) := ((fun (f : (i : I) → α i) (i : J) => f ⟨i, hJI i.prop⟩))⁻¹' boxI J t

example (A : Set ι) : A ⊆ univ := subset_univ A

lemma mem_boxIJ {I J : Set ι} (hJI : J ⊆ I) (t : (i : ι) → Set (α i)) (x : (i : ι) → α i) : (Function.projI x ∈ boxIJ hJI t) ↔ (∀ i ∈ J, (x i ∈ t i)) := by
  simp only [Function.projI, boxIJ, boxI, mem_preimage, mem_pi, mem_univ, forall_true_left,
    Subtype.forall]

def boxesI (I : Set ι) (C : (i : ι) → Set (Set (α i))) : Set (Set ((i : I) → α i)) := univ.pi '' univ.pi fun i => C i

@[simp]
theorem mem_boxesI {I : Set ι} (s : Set ((i : I) → α i)) (C : (i : ι) → Set (Set (α i))) (hC : ∀ i : ι, univ ∈ C i) : (s ∈ (boxesI I C)) ↔ (∃ (t : (i : ι) → Set (α i)), s = boxI I t ∧ (∀ i, t i ∈ C i)) := by
  classical
  constructor
  · intro hs
    rw [boxesI] at hs
    rcases hs with ⟨t', ⟨hs1, hs2⟩ ⟩
    simp_rw [← hs2, boxI]
    use fun (i : ι) => dite (i ∈ I) (fun h => t' ⟨i, h⟩)  (fun _ => (univ : Set (α i)))
    constructor
    · simp only [Subtype.coe_prop, dite_true]
    · intro i
      by_cases hi : i ∈ I
      · simp [hi, hs1]
        simp [pi] at hs1
        exact hs1 i _
      · simp [hi]
        exact hC i
  · rintro ⟨t, ⟨ht1, ht2⟩⟩ 
    rw [ht1, boxI, boxesI]
    simp [ht2]
    use fun (i : I) => t i
    constructor
    · intros a _
      refine ht2 a
    · rfl

example (x : ι) (f : ι → ι) (A : Set ι) (hx : x ∈ f⁻¹' A) : f x ∈ A := by
  exact hx

lemma preimage_boxI [DecidableEq ι] {I : Set ι} (t : (i : ι) → Set (α i)) : (fun (f : (i : ι) → α i) (i : I) => f i)⁻¹' (boxI I t) = pi I t := by
  simp [boxI]
  ext x
  simp only [mem_preimage, mem_pi, mem_univ, forall_true_left, Subtype.forall]
 
/-
lemma box_as_pi [DecidableEq ι] {J I : Set ι} (hJI : J ⊆ I)  (t : (i : ι) → Set (α i)) : 
(fun (f : (i : I) → α i) (i : J) => f ⟨i, hJI i.prop⟩)⁻¹' (boxI J t) = pi (fun (i : I) => (i.val ∈ J) : Set I) (fun (i : I) => t i) := by
  convert @preimage_boxI I (fun (i : I) => α i) _ (fun (i : I) => (i.val ∈ J) : Set I) (fun (i : I) => t i)
  have hb : boxI J t = @boxI I (fun (i : I) => α i) (fun (i : I) => (i.val ∈ J) : Set I) (fun (i : I) => t i) := by
    sorry
  

  
  sorry
-/


lemma preimage_boxI' [DecidableEq ι] [∀ i, Inhabited (α i)] {J I : Finset ι} (hJI : J ⊆ I)  (t : (i : ι) → Set (α i)) : (fun (f : (i : I) → α i) (i : J) => f ⟨i, hJI i.prop⟩)⁻¹' (boxI J t) = boxI I (fun (i : ι) => dite (i ∈ J) (fun _ => t i) (fun _ => (univ : Set (α i)))) := by
  let fIJ := fun (f : (i : I) → α i) (i : J) => f ⟨i, hJI i.prop⟩ 
  simp only [dite_eq_ite]
  ext y
  refine ⟨fun h => ?_, fun h => ?_⟩
  · change fIJ y ∈ boxI J t at h 
    rcases (@exists_sub_pi ι α _ I y) with ⟨x, hx⟩
    rw [← hx]
    change Function.projI x ∈ boxI I (fun (i : ι) => dite (i ∈ J) (fun _ => t i) (fun _ => (univ : Set (α i))))
    rw [mem_boxI]
    intros i hi
    simp only [dite_eq_ite, mem_ite_univ_right]
    intro hJ
    simp [boxI] at h
    specialize h i hJ
    have h1 : x i = y ⟨i, hi⟩ := by
      rw [← hx]
    rw [h1]
    exact h
  · change fIJ y ∈ boxI J t
    rcases (@exists_sub_pi ι α _ I y) with ⟨x, hx⟩
    rw [← hx]
    simp only [Finset.coe_sort_coe] 
    rw [← hx] at h
    change Function.projI x ∈ boxI I (fun (i : ι) => dite (i ∈ J) (fun _ => t i) (fun _ => (univ : Set (α i)))) at h
    rw [mem_boxI] at h
    simp only [boxI._eq_1, Finset.coe_sort_coe, mem_pi, mem_univ, forall_true_left, Subtype.forall]
    intros i hi
    specialize h i (hJI hi)
    simp only [dite_eq_ite, mem_ite_univ_right] at h 
    exact h hi

end Set

end Projections


section IsPiSystem

theorem isPiSystem_boxesI (I : Set ι) (C : (i : ι) → Set (Set (α i))) (hC1 : ∀ i : ι, IsPiSystem (C i)) : IsPiSystem (boxesI I C : Set (Set ((i : I) → α i))) := IsPiSystem.pi (fun (i : I) => hC1 i)

theorem isPiSystem_boxesI_of_measurable [∀ i, MeasurableSpace (α i)] (I : Set ι) : IsPiSystem (boxesI I (fun (i : ι) => {s : Set (α i) | MeasurableSet s}) : Set (Set ((i : I) → α i))) := IsPiSystem.pi (fun (i : I) => @MeasurableSpace.isPiSystem_measurableSet (α i) _)

end IsPiSystem


section IndependentFamily

variable [∀ i, MeasurableSpace (α i)]

namespace MeasureTheory

theorem generateFrom_boxesI (I : Finset ι) : (@MeasurableSpace.pi I (fun (i : I) => α i) _) = MeasurableSpace.generateFrom (boxesI I (fun (i : ι) => {s : Set (α i) | MeasurableSet s}) : Set (Set ((i : I) → α i))) := by
  exact Eq.symm generateFrom_pi

variable {ι : Type _} {α : ι → Type _}
variable [∀ i, MeasurableSpace (α i)]
variable [∀ i, Inhabited (α i)]

noncomputable def Measure.subset_pi (P : ∀ i, Measure (α i)) (I : Finset ι) : Measure ((i : I) → (α i)) := Measure.pi (fun (i : I) => (P (i : ι)))

theorem Measure.subset_pi_eval (I : Finset ι) (P : ∀ i : ι, Measure (α i)) [∀ i : ι, IsProbabilityMeasure (P i)]  (A : (i : ι) → Set (α i)) : (Measure.subset_pi P I) (univ.pi (fun i : I => A i)) = (∏ i : I, (P i) (A i)) := by
  simp only [subset_pi, Measure.pi_pi, Finset.univ_eq_attach]

theorem Measure.subset_pi_eval_boxI (I : Finset ι) (P : ∀ i : ι, Measure (α i)) [∀ i : ι, IsProbabilityMeasure (P i)] (t : (i : ι) → Set (α i)) : (Measure.subset_pi P I) (boxI I t) = (∏ i : I, (P i) (t i)) := by
  simp only [subset_pi, boxI._eq_1, Finset.coe_sort_coe, Measure.pi_pi, Finset.univ_eq_attach]



theorem Measure.subset_pi_eval_boxI' [DecidableEq ι] (I J : Finset ι) (hJI : J ⊆ I) (P : ∀ i : ι, Measure (α i)) [∀ i : ι, IsProbabilityMeasure (P i)] (t : (i : ι) → Set (α i)) : (Measure.subset_pi P I) (boxI I (fun (i : ι) => dite (i ∈ J) (fun _ => t i) (fun _ => (univ : Set (α i))))) = (∏ i : J, (P i) (t i)) := by
  rw [Measure.subset_pi_eval_boxI]
  let g := (fun i => (P i) (t i)) 
  let f := (fun i => (P i) (dite (i ∈ J) (fun _ => t i) (fun _ => univ)))
  change ∏ i : { x // x ∈ I }, f i = ∏ i : { x // x ∈ J }, g i
  have h1 : ∀ (x : ι), x ∈ J → f x = g x := by
    intros x hx
    simp only [dite_eq_ite, hx, ite_true]
  have h2 : ∀ (x : ι), ¬x ∈ J → f x = 1 := by
    intros x hx
    simp only [dite_eq_ite, hx, ite_false, measure_univ]
  exact Finset.prod_mem_not_mem_of_eq_one_if_not_mem f g hJI h1 h2

-- product of probability measures is a probability measure
instance Measure.subset_pi_of_ProbabilityMeasure (P : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (P i)] (I : Finset ι) : IsProbabilityMeasure (Measure.subset_pi P I) := by
  constructor
  rw [← pi_univ_Subtype]
  rw [Measure.subset_pi_eval I P (fun i : ι => univ)]
  simp only [Finset.univ_eq_attach, measure_univ, Finset.prod_const_one]

lemma box_measurable (I : Finset ι) {s : Set ((i : I) → α i)} (hs : s ∈ boxesI I  (fun (i : ι) => {s : Set (α i) | MeasurableSet s})) : MeasurableSet s := by
  rcases hs with ⟨t, ⟨h1, h2⟩⟩
  rw [← h2]
  have ht : ∀ i, MeasurableSet (t i) := by
    simp only [Subtype.forall]
    simp [pi] at h1
    exact h1
  apply MeasurableSet.pi countable_univ
  simp only [Finset.coe_sort_coe, mem_univ, ht, forall_true_left, Subtype.forall, Finset.mem_coe, implies_true]

theorem proj' [DecidableEq ι] (P : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (P i)] (J I : Finset ι) (hJI : J ⊆ I) : Measure.subset_pi P J = Measure.map ((fun (f : (i : I) → α i) (i : J) => f ⟨i, hJI i.prop⟩)) (Measure.subset_pi P I) := by
  let C := (fun (i : ι) => { s : Set (α i) | MeasurableSet s})
  have hu : ∀ (i : ι), univ ∈ C i := by
    simp only [mem_setOf_eq, MeasurableSet.univ, implies_true]
  -- let f := (fun (f : (i : I) → α i) (i : J) => f ⟨i, hJI i.prop⟩)
  apply MeasureTheory.ext_of_generate_finite 
  exact generateFrom_boxesI J
  exact @isPiSystem_boxesI_of_measurable ι α _ J
  · intros s hs
    change s ∈ boxesI J C at hs 
    rcases (mem_boxesI s C hu).1 hs with ⟨t, ⟨ht1, _⟩⟩
    rw [Measure.map_apply (measurable_proj₂' I J hJI) (box_measurable J hs)]
    change s = boxI J t at ht1
    rw [ht1]
    classical
    rw [preimage_boxI' hJI t]
    rw [Measure.subset_pi_eval_boxI, Measure.subset_pi_eval_boxI']
    exact hJI
  · let t := fun (i : ι) => (univ : Set (α i))
    rw [Measure.map_apply (measurable_proj₂' I J hJI) (box_measurable J _)]
    simp only [boxI_univ]
    have ht : t = fun (i : ι) => (univ : Set (α i)) := rfl
    rw [←ht]
    change (Measure.subset_pi P J) (boxI J t) = (Measure.subset_pi P I) ((fun (f : (i : I) → α i) (i : J) => f ⟨i, hJI i.prop⟩) ⁻¹' boxI J t)
    rw [preimage_boxI' hJI t]
    simp only [Measure.subset_pi_eval_boxI, Finset.univ_eq_attach, measure_univ, Finset.prod_const_one, dite_eq_ite,
      ite_self]
    change univ ∈ boxesI J C
    rw [mem_boxesI univ C hu]
    use (fun (i : ι) => (univ : Set (α i)))
    constructor
    · refine boxI_univ (J : Set ι)
    · simp only [mem_setOf_eq, MeasurableSet.univ, implies_true]

theorem product_isProjective [DecidableEq ι] (P : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (P i)] :
    IsProjectiveMeasureFamily (fun J : Finset ι => Measure.subset_pi P J) := by
  simp [IsProjectiveMeasureFamily, IsProjective]
  intros I J hJI
  exact proj' P J I hJI 

noncomputable def independentFamily [DecidableEq ι] [∀ i, PseudoEMetricSpace (α i)]
    [∀ i, BorelSpace (α i)] [∀ i, TopologicalSpace.SecondCountableTopology (α i)]
    [∀ i, CompleteSpace (α i)] [Nonempty (∀ i, α i)] (P : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (P i)] : Measure (∀ i, α i) := projectiveLimitWithWeakestHypotheses (fun J : Finset ι => Measure.subset_pi P J) (product_isProjective P)

end MeasureTheory

end IndependentFamily