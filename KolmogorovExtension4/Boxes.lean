/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
import KolmogorovExtension4.Semiring
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! # π-systems generating `MeasurableSpace.pi`

-/


open MeasureTheory Set

variable {ι : Type*} {α : ι → Type*}

section measurableCylinders

variable [∀ i, MeasurableSpace (α i)]

theorem isSetField_measurableCylinders : IsSetField (measurableCylinders α) where
  empty_mem := empty_mem_measurableCylinders α
  univ_mem := univ_mem_measurableCylinders α
  union_mem := fun _ _ ↦ union_mem_measurableCylinders
  diff_mem := fun _ _ ↦ diff_mem_measurableCylinders

theorem isSetRing_measurableCylinders : MeasureTheory.IsSetRing (measurableCylinders α) :=
  isSetField_measurableCylinders.toIsSetRing

theorem isSetSemiring_measurableCylinders : MeasureTheory.IsSetSemiring (measurableCylinders α) :=
  isSetField_measurableCylinders.isSetSemiring

theorem iUnion_le_mem_measurableCylinders {s : ℕ → Set (∀ i : ι, α i)}
    (hs : ∀ n, s n ∈ measurableCylinders α) (n : ℕ) :
    (⋃ i ≤ n, s i) ∈ measurableCylinders α :=
  isSetField_measurableCylinders.iUnion_le_mem hs n

theorem iInter_le_mem_measurableCylinders {s : ℕ → Set (∀ i : ι, α i)}
    (hs : ∀ n, s n ∈ measurableCylinders α) (n : ℕ) :
    (⋂ i ≤ n, s i) ∈ measurableCylinders α :=
  isSetField_measurableCylinders.iInter_le_mem hs n

end measurableCylinders

section closedCompactCylinders

variable [∀ i, TopologicalSpace (α i)]

variable (α)

/-- The set of all cylinders based on closed compact sets. Note that such a set is closed, but
not compact in general (for instance, the whole space is always a closed compact cylinder). -/
def closedCompactCylinders : Set (Set ((i : ι) → α i)) :=
  ⋃ (s) (S) (_ : IsClosed S) (_ : IsCompact S), {cylinder s S}

theorem empty_mem_closedCompactCylinders : ∅ ∈ closedCompactCylinders α := by
  simp_rw [closedCompactCylinders, mem_iUnion, mem_singleton_iff]
  exact ⟨∅, ∅, isClosed_empty, isCompact_empty, (cylinder_empty _).symm⟩

variable {α}

@[simp]
theorem mem_closedCompactCylinders (t : Set ((i : ι) → α i)) :
    t ∈ closedCompactCylinders α
      ↔ ∃ (s S : _) (_ : IsClosed S) (_ : IsCompact S), t = cylinder s S := by
  simp_rw [closedCompactCylinders, mem_iUnion, mem_singleton_iff]

/-- Given a closed compact cylinder, choose a finset of variables such that it only depends on
these variables. -/
noncomputable def closedCompactCylinders.finset {t : Set ((i : ι) → α i)}
    (ht : t ∈ closedCompactCylinders α) :
    Finset ι :=
  ((mem_closedCompactCylinders t).mp ht).choose

/-- Given a closed compact cylinder, choose a set depending on finitely many variables of which it
is a lift. -/
def closedCompactCylinders.set {t : Set ((i : ι) → α i)} (ht : t ∈ closedCompactCylinders α) :
    Set (∀ i : closedCompactCylinders.finset ht, α i) :=
  ((mem_closedCompactCylinders t).mp ht).choose_spec.choose

theorem closedCompactCylinders.isClosed {t : Set ((i : ι) → α i)}
    (ht : t ∈ closedCompactCylinders α) :
    IsClosed (closedCompactCylinders.set ht) :=
  ((mem_closedCompactCylinders t).mp ht).choose_spec.choose_spec.choose

theorem closedCompactCylinders.isCompact {t : Set ((i : ι) → α i)}
    (ht : t ∈ closedCompactCylinders α) :
    IsCompact (closedCompactCylinders.set ht) :=
  ((mem_closedCompactCylinders t).mp ht).choose_spec.choose_spec.choose_spec.choose

theorem closedCompactCylinders.eq_cylinder {t : Set ((i : ι) → α i)}
    (ht : t ∈ closedCompactCylinders α) :
    t = cylinder (closedCompactCylinders.finset ht) (closedCompactCylinders.set ht) :=
  ((mem_closedCompactCylinders t).mp ht).choose_spec.choose_spec.choose_spec.choose_spec

theorem cylinder_mem_closedCompactCylinders (s : Finset ι) (S : Set (∀ i : s, α i))
    (hS_closed : IsClosed S) (hS_compact : IsCompact S) :
    cylinder s S ∈ closedCompactCylinders α := by
  rw [mem_closedCompactCylinders]
  exact ⟨s, S, hS_closed, hS_compact, rfl⟩

theorem mem_cylinder_of_mem_closedCompactCylinders [∀ i, MeasurableSpace (α i)]
    [∀ i, SecondCountableTopology (α i)] [∀ i, OpensMeasurableSpace (α i)]
    {t : Set ((i : ι) → α i)}
    (ht : t ∈ closedCompactCylinders α) :
    t ∈ measurableCylinders α := by
  rw [mem_measurableCylinders]
  refine ⟨closedCompactCylinders.finset ht, closedCompactCylinders.set ht, ?_, ?_⟩
  · exact (closedCompactCylinders.isClosed ht).measurableSet
  · exact closedCompactCylinders.eq_cylinder ht

end closedCompactCylinders
