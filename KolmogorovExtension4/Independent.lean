import KolmogorovExtension4.Projective
import Mathlib.MeasureTheory.Constructions.Polish
import Mathlib.MeasureTheory.Constructions.Pi

open Set

open scoped ENNReal BigOperators

namespace MeasureTheory

variable {ι : Type _} {α : ι → Type _}
variable [∀ i, MeasurableSpace (α i)]

noncomputable def Measure.subset_pi (P : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (P i)] (s : Finset ι) : Measure (∀ i : s, (α i)) := Measure.pi (fun (i : s) => (P (i : ι)))

theorem product_isProjective (P : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (P i)] :
  IsProjectiveMeasureFamily (fun J : Finset ι => Measure.subset_pi P J) := by
    simp [IsProjectiveMeasureFamily, IsProjective]
    intros i j hij
    sorry

end MeasureTheory

