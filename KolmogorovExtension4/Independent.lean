import KolmogorovExtension4.KolmogorovExtension
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Independence.Basic

open Set

open scoped ENNReal BigOperators

namespace MeasureTheory

variable {ι : Type _} {α : ι → Type _}
variable [∀ i, MeasurableSpace (α i)]

noncomputable def Measure.subset_pi (P : ∀ i, Measure (α i)) (I : Finset ι) : Measure ((i : I) → (α i)) := Measure.pi (fun (i : I) => (P (i : ι)))

theorem Measure.subset_pi_eval (I : Finset ι) (P : ∀ i : ι, Measure (α i)) [∀ i : ι, IsProbabilityMeasure (P i)]  (A : (i : ι) → Set (α i)) : (Measure.subset_pi P I) (univ.pi (fun i : I => A i)) = (∏ i : I, (P i) (A i)) := by
  simp only [subset_pi, pi_pi, Finset.univ_eq_attach]

theorem pi_univ_Subtype (I : Finset ι) : Set.pi (univ : Set I) (fun i => univ) = (univ : Set ((i : I) → α i))  := by
  simp only [pi_univ]


instance Measure.subset_pi_of_ProbabilityMeasure (P : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (P i)] (I : Finset ι) : IsProbabilityMeasure (Measure.subset_pi P I) := by
  constructor
  rw [← pi_univ_Subtype]
  rw [Measure.subset_pi_eval I P (fun i : ι => univ)]
  simp only [Finset.univ_eq_attach, measure_univ, Finset.prod_const_one]




-- lemma Measure.subset_pi_iIndep (Finset ι) (P : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (P i)] : Measure.subset_pi P ι

def J_as_Subtype (I J : Set ι) (hJI : J ⊆ I) : Set I := {x : I | x.val ∈ J}

lemma embedding_inj {ι : Type} (I : Finset ι) : Function.Injective (fun (i : I) => (i.val : ι)) := by
  intros i j hij
  simp only at hij
  sorry

lemma embedding_injOn {ι : Type} (I J : Finset ι) (hIJ : J ⊆ I) : Set.InjOn (fun (i : I) => (i.val : ι)) ((fun (i : I) => (i.val : ι))⁻¹' J) := Function.Injective.injOn (embedding_inj I) ((fun (i : I) => (i.val : ι))⁻¹' J)

noncomputable def  Finset_Subtype_of_subset (I J : Finset ι) : Finset I := Finset.preimage J (fun (i : I) => (i.val : ι)) (Function.Injective.injOn (embedding_inj I) ((fun (i : I) => (i.val : ι))⁻¹' J))

def boxIJ {I : Finset ι} (J : Finset ι) (t : (i : I) → Set (α i)) : Set ((i : I) → α i) := box t (Finset_Subtype_of_subset I J)

def boxesI (I : Finset ι) [∀ (i : I), MeasurableSpace (α i)] : Set (Set ((i : I) → α i)) := univ.pi '' univ.pi fun i => {s : Set (α i)| MeasurableSet s}

theorem isPiSystem_boxesI (I : Finset ι) [∀ (i : I), MeasurableSpace (α i)] : IsPiSystem (boxesI I : Set (Set ((i : I) → α i))) := isPiSystem_pi

def boxI {I : Finset ι} (t : (i : I) → Set (α i)) : Set ((i : I) → α i) := boxIJ I t



-- def boxIJ' {I J : Finset ι} (hJI : J ⊆ I) (t : (i : I) → Set (α i)) : Set ((i : I) → α i) := box t (Finset.preimage J (Set.inclusion hJI) (Function.Injective.injOn (Set.inclusion_injective hJI) J))

lemma proj (P : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (P i)] (J I : Finset ι) (hJI : J ⊆ I) (t : (i : I) → Set (α i)) : (Measure.subset_pi P J) (univ.pi (fun (i : J) => t ⟨i.val, hJI i.prop⟩)) = (Measure.subset_pi P I) (boxIJ J t) := by
  sorry

-- (Measure.subset_pi P J) (univ.pi (fun (i : J) => t ⟨i.val, hJI i.prop⟩)) = (Measure.subset_pi P J) (boxIJ J t)

-- Projection 
def Function.proj (I J : Finset ι) (hJI : J ⊆ I) := fun x : ∀ i : I, α i => fun i : J => x ⟨i.val, hJI i.prop⟩

lemma proj_box (J I : Finset ι) (hJI : J ⊆ I) (t : (i : I) → Set (α i)) : (Function.proj I J hJI) '' (boxIJ J t) = boxIJ J (fun (i : J) => t ⟨i.val, hJI i.prop⟩) := by
  simp only [Function.proj, boxIJ, box, Finset_Subtype_of_subset, Finset.coe_preimage]
  ext pi
  constructor
  · intro h
    simp only [mem_pi, mem_preimage, Finset.mem_coe, Finset.coe_mem, forall_true_left, Subtype.forall]
    intros a ha
    simp only [mem_image, mem_pi, mem_preimage, Finset.mem_coe, Subtype.forall] at h 
    rcases h with ⟨x1, ⟨h1, h2⟩⟩
    rw [← h2]
    simp only
    specialize h1 a (hJI ha) ha
    simp only [h1]
  · intro h
    simp only [mem_image, mem_pi, mem_preimage, Finset.mem_coe, Subtype.forall]
    simp only [mem_pi, mem_preimage, Finset.mem_coe, Finset.coe_mem, forall_true_left, Subtype.forall] at h 
    


    sorry

theorem proj' (P : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (P i)] (J I : Finset ι) (hJI : J ⊆ I) : Measure.subset_pi P J = Measure.map (fun x : ∀ i : I, α i => fun i : J => x ⟨i.val, hJI i.prop⟩) (Measure.subset_pi P I) := by

  sorry

theorem product_isProjective (P : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (P i)] :
    IsProjectiveMeasureFamily (fun J : Finset ι => Measure.subset_pi P J) := by
  simp [IsProjectiveMeasureFamily, IsProjective]
  intros I J hJI
  exact proj' P J I hJI 

noncomputable def independentFamily [∀ i, PseudoEMetricSpace (α i)]
    [∀ i, BorelSpace (α i)] [∀ i, TopologicalSpace.SecondCountableTopology (α i)]
    [∀ i, CompleteSpace (α i)] [Nonempty (∀ i, α i)] (P : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (P i)] : Measure (∀ i, α i) := projectiveLimitWithWeakestHypotheses (fun J : Finset ι => Measure.subset_pi P J) (product_isProjective P)

end MeasureTheory

