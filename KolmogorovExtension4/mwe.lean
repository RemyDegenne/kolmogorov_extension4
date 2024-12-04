import Mathlib.MeasureTheory.Constructions.Pi

open MeasureTheory Set

variable {ι : Type _} {α : ι → Type _}
variable [∀ i, MeasurableSpace (α i)]

theorem measurable_proj₂ (I J : Set ι) (hIJ : J ⊆ I) :
    Measurable fun (f : (i : I) → α i) (i : J) => f ⟨i, hIJ i.prop⟩ := by
  rw [measurable_pi_iff]; exact fun i => measurable_pi_apply _

def projIJ (α : ι → Type _) {I J : Set ι} (hIJ : J ⊆ I) : ((i : I) → α i) → ((i : J) → α i) := fun (f : (i : I) → α i) => fun (i : J) => f ⟨i, hIJ i.prop⟩

#check projIJ

-- does not work
example (I J : Set ι) (hIJ : J ⊆ I) : Measurable (projIJ α hIJ) := by
  simp [projIJ]
  exact measurable_proj₂ I J hIJ 

-- works
example (I J : Set ι) (hIJ : J ⊆ I) : @Measurable ((i : I) → α i) ((i : J) → α i) _ _ (projIJ α hIJ) := by
  simp [projIJ]
  exact measurable_proj₂ I J hIJ 
