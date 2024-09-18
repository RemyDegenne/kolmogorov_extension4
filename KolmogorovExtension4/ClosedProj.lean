/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
import Mathlib.Topology.Homeomorph
import Mathlib.MeasureTheory.MeasurableSpace.Basic

/-! # Results about projections

-/

open MeasureTheory Set

theorem continuous_cast {α β : Type u} [tα : TopologicalSpace α] [tβ : TopologicalSpace β]
    (h : α = β) (ht : HEq tα tβ) : Continuous fun x : α ↦ cast h x := by
  subst h
  convert continuous_id
  rw [← heq_iff_eq]
  exact ht.symm

variable {ι : Type*} {α : ι → Type*}

section Measurable

variable [∀ i, MeasurableSpace (α i)]

theorem measurable_proj (I : Set ι) : Measurable fun (f : Π i, α i) (i : I) ↦ f i := by
  rw [measurable_pi_iff]; exact fun i ↦ measurable_pi_apply _

theorem measurable_proj' (I : Finset ι) : Measurable fun (f : Π i, α i) (i : I) ↦ f i := by
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

theorem continuous_proj (I : Set ι) : Continuous fun (f : Π i, α i) (i : I) ↦ f i :=
  continuous_pi fun i : ↥I ↦ by apply continuous_apply

theorem continuous_proj₂ (I J : Set ι) (hIJ : J ⊆ I) :
    Continuous fun (f : (i : I) → α i) (i : J) ↦ f ⟨i, hIJ i.prop⟩ :=
  continuous_pi fun i : ↥J ↦ by apply continuous_apply

theorem continuous_proj₂' (I J : Finset ι) (hIJ : J ⊆ I) :
    Continuous fun (f : (i : I) → α i) (i : J) ↦ f ⟨i, hIJ i.prop⟩ :=
  continuous_pi fun i : ↥J ↦ by apply continuous_apply

end Continuous

section isClosed_proj

/-! We show that the projection of a compact closed set `s` in a product `Π i, α i` onto one of the
spaces `α j` is a closed set.

The idea of the proof is to use `isClosedMap_snd_of_compactSpace`, which is the fact that if
`X` is a compact topological space, then `Prod.snd : X × Y → Y` is a closed map.
In our application, `Y` is `α j` and `X` is the projection of `s` to the product over all indexes
that are not `j`. We define `projCompl α j` for that projection map.

In order to be able to use the lemma `isClosedMap_snd_of_compactSpace`, we have to make those
`X` and `Y` appear explicitly.
We remark that `s` belongs to the set `projCompl α j ⁻¹' (projCompl α j '' s)`, and we build
an homeomorphism `projCompl α j ⁻¹' (projCompl α j '' s) ≃ₜ projCompl α j '' s × α j`.
`projCompl α j` is a compact space since `s` is compact, and the lemma applies. -/

-- TODO: change names

variable {ι : Type*} {α : ι → Type*} {s : Set (Π i, α i)} {i : ι}

/-- Given a dependent function of `i`, specialize it as a function on the complement of `{i}`. -/
def projCompl (α : ι → Type*) (i : ι) (x : Π i, α i) : Π j : { k // k ≠ i }, α j := fun j ↦ x j

lemma continuous_projCompl [∀ i, TopologicalSpace (α i)] :
    Continuous (projCompl α i) := continuous_pi fun _ ↦ continuous_apply _

open Classical in
/-- Given a set of dependent functions, construct a function on a product space separating out
the coordinate `i` from the other ones. -/
noncomputable def fromXProd (α : ι → Type*) (i : ι) (s : Set (Π j, α j))
    (p : projCompl α i '' s × α i) :
    Π j, α j :=
  fun j ↦ if h : j = i then cast (h ▸ rfl) p.2 else (↑(p.1) : Π j : { k // k ≠ i }, α j) ⟨j, h⟩

@[simp]
lemma fromXProd_same (p : projCompl α i '' s × α i) :
    fromXProd α i s p i = p.2 := by simp only [fromXProd, ne_eq, cast_eq, dite_true]

@[simp]
lemma projCompl_fromXProd (p : projCompl α i '' s × α i) :
    projCompl α i (fromXProd α i s p) = p.1 := by
  ext j; simp only [fromXProd, projCompl, dif_neg j.2]

lemma continuous_fromXProd [∀ i, TopologicalSpace (α i)] : Continuous (fromXProd α i s) := by
  refine continuous_pi fun j ↦ ?_
  simp only [fromXProd]
  split_ifs with h
  · exact (continuous_cast _ (h ▸ HEq.rfl)).comp continuous_snd
  · exact ((continuous_apply _).comp continuous_subtype_val).comp continuous_fst

lemma fromXProd_mem_XY (p : projCompl α i '' s × α i) :
    fromXProd α i s p ∈ projCompl α i ⁻¹' (projCompl α i '' s) := by
  obtain ⟨y, hy_mem_s, hy_eq⟩ := p.1.2
  exact ⟨y, hy_mem_s, hy_eq.trans (projCompl_fromXProd p).symm⟩

@[simp]
lemma fromXProd_projCompl (x : projCompl α i ⁻¹' (projCompl α i '' s)) :
    fromXProd α i s ⟨⟨projCompl α i x, x.2⟩, (x : Π j, α j) i⟩ = (x : Π j, α j) := by
  ext j
  simp only [fromXProd, projCompl, ne_eq, dite_eq_right_iff]
  intro h
  rw [← heq_iff_eq]
  exact HEq.trans (cast_heq (h ▸ rfl) _) (h.symm ▸ HEq.rfl)

/-- Homeomorphism between the set of functions that concide with a given set of functions away
from a given `i`, and dependent functions away from `i` times any value on `i`. -/
noncomputable
def XYEquiv (α : ι → Type*) [∀ i, TopologicalSpace (α i)] (i : ι) (s : Set (Π j, α j)) :
    projCompl α i ⁻¹' (projCompl α i '' s) ≃ₜ projCompl α i '' s × α i where
  toFun x := ⟨⟨projCompl α i x, x.2⟩, (x : Π j, α j) i⟩
  invFun p := ⟨fromXProd α i s p, fromXProd_mem_XY p⟩
  left_inv x := by ext; simp
  right_inv p := by ext <;> simp
  continuous_toFun := by
    refine Continuous.prod_mk ?_ ?_
    · exact (continuous_projCompl.comp continuous_subtype_val).subtype_mk _
    · exact (continuous_apply _).comp continuous_subtype_val
  continuous_invFun := continuous_fromXProd.subtype_mk _

lemma preimage_snd_xyEquiv [∀ i, TopologicalSpace (α i)] :
    Prod.snd '' (XYEquiv α i s ''
        ((fun (x : projCompl α i ⁻¹' (projCompl α i '' s)) ↦ (x : Π j, α j)) ⁻¹' s))
      = (fun x ↦ x i) '' s := by
  ext x
  simp only [ne_eq, XYEquiv, projCompl, Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk, mem_image,
    mem_preimage, Subtype.exists, exists_and_left, Prod.exists, Prod.mk.injEq, exists_and_right,
    exists_eq_right, Subtype.mk.injEq, exists_prop]
  constructor
  · rintro ⟨y, _, z, hz_mem, _, hzx⟩
    exact ⟨z, hz_mem, hzx⟩
  · rintro ⟨z, hz_mem, hzx⟩
    exact ⟨projCompl α i z, mem_image_of_mem (projCompl α i) hz_mem, z, hz_mem,
      ⟨⟨⟨z, hz_mem, rfl⟩, rfl⟩, hzx⟩⟩

/-- The projection of a compact closed set onto a coordinate is closed. -/
theorem isClosed_proj [∀ i, TopologicalSpace (α i)]
    (hs_compact : IsCompact s) (hs_closed : IsClosed s) (i : ι) :
    IsClosed ((fun x ↦ x i) '' s) := by
  rw [← preimage_snd_xyEquiv]
  have : CompactSpace (projCompl α i '' s) :=
    isCompact_iff_compactSpace.mp (hs_compact.image continuous_projCompl)
  refine isClosedMap_snd_of_compactSpace _ ?_
  rw [Homeomorph.isClosed_image]
  exact hs_closed.preimage continuous_subtype_val

end isClosed_proj
