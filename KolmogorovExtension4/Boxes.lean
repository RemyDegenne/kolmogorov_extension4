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

section ProjectionMaps

section Measurable

variable [∀ i, MeasurableSpace (α i)]

theorem measurable_proj (I : Set ι) : Measurable fun (f : (i : ι) → α i) (i : I) ↦ f i := by
  rw [measurable_pi_iff]; exact fun i ↦ measurable_pi_apply _

theorem measurable_proj' (I : Finset ι) : Measurable fun (f : (i : ι) → α i) (i : I) ↦ f i := by
  rw [measurable_pi_iff]; exact fun i ↦ measurable_pi_apply _

theorem measurable_proj₂ (I J : Set ι) (hIJ : J ⊆ I) :
    Measurable fun (f : (i : I) → α i) (i : J) ↦ f ⟨i, hIJ i.prop⟩ := by
  rw [measurable_pi_iff]; exact fun i ↦ measurable_pi_apply _

theorem measurable_proj₂' (I J : Finset ι) (hIJ : J ⊆ I) :
    Measurable fun (f : (i : I) → α i) (i : J) ↦ f ⟨i, hIJ i.prop⟩ := by
  rw [measurable_pi_iff]; exact fun i ↦ measurable_pi_apply _

end Measurable

section Continuous

variable [∀ i, TopologicalSpace (α i)]

theorem continuous_proj (I : Set ι) : Continuous fun (f : (i : ι) → α i) (i : I) ↦ f i :=
  continuous_pi fun i : ↥I ↦ by apply continuous_apply

theorem continuous_proj₂ (I J : Set ι) (hIJ : J ⊆ I) :
    Continuous fun (f : (i : I) → α i) (i : J) ↦ f ⟨i, hIJ i.prop⟩ :=
  continuous_pi fun i : ↥J ↦ by apply continuous_apply

theorem continuous_proj₂' (I J : Finset ι) (hIJ : J ⊆ I) :
    Continuous fun (f : (i : I) → α i) (i : J) ↦ f ⟨i, hIJ i.prop⟩ :=
  continuous_pi fun i : ↥J ↦ by apply continuous_apply

end Continuous

section isClosed_proj

open Filter

open scoped Topology Filter

variable {ι : Type*} {α : ι → Type*} [∀ i, TopologicalSpace (α i)] {s : Set (∀ i, α i)}

theorem continuous_cast {α β : Type u} [tα : TopologicalSpace α] [tβ : TopologicalSpace β]
    (h : α = β) (ht : HEq tα tβ) : Continuous fun x : α ↦ cast h x := by
  subst h
  convert continuous_id
  rw [← heq_iff_eq]
  exact ht.symm

/-- Given a dependent function of `i`, specialize it as a function on the complement of `{i}`. -/
def projCompl (α : ι → Type*) (i : ι) (x : (i : ι) → α i) :
    (j : { k // k ≠ i }) → α j := fun j ↦ x j

lemma continuous_projCompl {i : ι} : Continuous (projCompl α i) :=
  continuous_pi fun _ ↦ continuous_apply _

/-- Given a set of dependent functions, construct the set of corresponding functions on the
complement of a given `i`. -/
def X (α : ι → Type*) (i : ι) (s : Set ((j : ι) → α j)) :
    Set ((j : { k // k ≠ i }) → α j) := projCompl α i '' s

variable (i : ι) (x : ∀ i, α i)

lemma projCompl_mem (hx : x ∈ s) : projCompl α i x ∈ X α i s := by
  simp only [ne_eq, projCompl, X, mem_image]
  exact ⟨x, hx, rfl⟩

instance : TopologicalSpace (X α i s) := by rw [X]; infer_instance

lemma compactSpace_X (hs_compact : IsCompact s) : CompactSpace (X α i s) := by
  refine isCompact_iff_compactSpace.mp ?_
  refine IsCompact.image hs_compact ?_
  exact continuous_pi fun j ↦ continuous_apply _

/-- Given a set of dependent functions, construct the functions that coincide with one of the
initial functions away from a given `i`. -/
def XY (α : ι → Type*) (i : ι) (s : Set ((j : ι) → α j)) :
    Set ((j : ι) → α j) :=
  {x | projCompl α i x ∈ projCompl α i '' s}

lemma subset_xy : s ⊆ XY α i s := fun x hx ↦ ⟨x, hx, rfl⟩

lemma mem_xy_of_mem (hx : x ∈ s) : x ∈ XY α i s := subset_xy i hx

open Classical in
/-- Given a set of dependent functions, construct a function on a product space separating out
the coordinate `i` from the other ones. -/
noncomputable def fromXProd (α : ι → Type*) (i : ι) (s : Set ((j : ι) → α j)) :
    X α i s × α i → ∀ j, α j :=
  fun p j ↦
    if h : j = i then by refine cast ?_ p.2; rw [h] else (↑(p.1) : ∀ j : { k // k ≠ i }, α j) ⟨j, h⟩

lemma fromXProd_same (p : X α i s × α i) :
    fromXProd α i s p i = p.2 := by
  simp only [fromXProd, ne_eq, cast_eq, dite_true]

lemma projCompl_fromXProd (p : X α i s × α i) :
    projCompl α i (fromXProd α i s p) = p.1 := by
  ext1 j
  have : (j : ι) ≠ i := j.2
  simp only [fromXProd, projCompl]
  rw [dif_neg this]

lemma continuous_fromXProd : Continuous (fromXProd α i s) := by
  refine continuous_pi fun j ↦ ?_
  simp only [fromXProd]
  split_ifs with h
  · refine (continuous_cast _ ?_).comp continuous_snd
    rw [h]
  · exact (Continuous.comp (continuous_apply _) continuous_subtype_val).comp continuous_fst

lemma fromXProd_mem_XY (p : X α i s × α i) :
    fromXProd α i s p ∈ XY α i s := by
  simp only [XY, mem_image, mem_setOf_eq]
  obtain ⟨y, hy_mem_s, hy_eq⟩ := p.1.2
  exact ⟨y, hy_mem_s, hy_eq.trans (projCompl_fromXProd _ _).symm⟩

lemma fromXProd_projCompl (x : XY α i s) :
    fromXProd α i s ⟨⟨projCompl α i x, x.2⟩, (x : ∀ j, α j) i⟩ = (x : ∀ j, α j) := by
  ext1 j
  simp only [fromXProd, projCompl, ne_eq, dite_eq_right_iff]
  intro h
  rw [← heq_iff_eq]
  refine HEq.trans (cast_heq (_ : α i = α j) _) ?_
  rw [h]

/-- Homeomorphism between the set of functions that concide with a given set of functions away
from a given `i`, and dependent functions away from `i` times any value on `i`. -/
noncomputable
def XYEquiv (α : ι → Type*) [∀ i, TopologicalSpace (α i)] (i : ι) (s : Set ((j : ι) → α j)) :
    XY α i s ≃ₜ X α i s × α i :=
{ toFun := fun x ↦ ⟨⟨projCompl α i x, x.2⟩, (x : ∀ j, α j) i⟩
  invFun := fun p ↦ ⟨fromXProd α i s p, fromXProd_mem_XY _ p⟩
  left_inv := fun x ↦ by
    ext j
    simp only [ne_eq]
    rw [fromXProd_projCompl]
  right_inv := fun p ↦ by
    simp only [ne_eq]
    ext x
    · simp only
      rw [projCompl_fromXProd]
    · simp only
      exact fromXProd_same _ _
  continuous_toFun := by
    refine Continuous.prod_mk ?_ ?_
    · exact Continuous.subtype_mk (continuous_projCompl.comp continuous_subtype_val) _
    · exact (continuous_apply _).comp continuous_subtype_val
  continuous_invFun := Continuous.subtype_mk (continuous_fromXProd _) _}

lemma snd_xyEquiv_preimage :
    Prod.snd '' (XYEquiv α i s '' ((fun (x : XY α i s) ↦ (x : ∀ j, α j)) ⁻¹' s))
      = (fun x : ∀ j, α j ↦ x i) '' s := by
  ext1 x
  simp only [ne_eq, XYEquiv, projCompl, Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk, mem_image,
    mem_preimage, Subtype.exists, exists_and_left, Prod.exists, Prod.mk.injEq, exists_and_right,
    exists_eq_right, Subtype.mk.injEq, exists_prop]
  constructor
  · rintro ⟨y, _, z, hz_mem, _, hzx⟩
    exact ⟨z, hz_mem, hzx⟩
  · rintro ⟨z, hz_mem, hzx⟩
    exact ⟨projCompl α i z, projCompl_mem _ _ hz_mem, z, hz_mem, ⟨⟨mem_xy_of_mem _ _ hz_mem, rfl⟩, hzx⟩⟩

theorem isClosed_proj (hs_compact : IsCompact s) (hs_closed : IsClosed s) (i : ι) :
    IsClosed ((fun x : ∀ j, α j ↦ x i) '' s) := by
  let πi : (∀ j, α j) → α i := fun x : ∀ j, α j ↦ x i
  classical
  have h_image_eq : πi '' s
      = Prod.snd '' (XYEquiv α i s '' ((fun (x : XY α i s) ↦ (x : ∀ j, α j)) ⁻¹' s)) := by
    exact (snd_xyEquiv_preimage _).symm
  rw [h_image_eq]
  have : CompactSpace (X α i s) := compactSpace_X _ hs_compact
  refine isClosedMap_snd_of_compactSpace _ ?_
  rw [Homeomorph.isClosed_image]
  exact IsClosed.preimage continuous_subtype_val hs_closed

end isClosed_proj

end ProjectionMaps

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
