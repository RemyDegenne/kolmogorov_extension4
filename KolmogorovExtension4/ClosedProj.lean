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

/-
-- Commented out since unused. We should use continuous_restrict and measurable_restrict instead.

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
-/

section isClosed_proj

/-! We show that the image of a compact closed set `s` in a product `Π i : ι, α i` by
the restriction to a subset of coordinates `S : Set ι` is a closed set.

The idea of the proof is to use `isClosedMap_snd_of_compactSpace`, which is the fact that if
`X` is a compact topological space, then `Prod.snd : X × Y → Y` is a closed map.
In our application, `Y` is `Π i : S, α i` and `X` is the image of `s` by `Set.restrict Sᶜ`.

In order to be able to use the lemma `isClosedMap_snd_of_compactSpace`, we have to make those
`X` and `Y` appear explicitly.
We remark that `s` belongs to the set `Sᶜ.restrict  ⁻¹' (Sᶜ.restrict '' s)`, and we build
an homeomorphism `Sᶜ.restrict ⁻¹' (Sᶜ.restrict '' s) ≃ₜ Sᶜ.restrict '' s × Π i : S, α i`.
`Sᶜ.restrict '' s` is a compact space since `s` is compact, and the lemma applies. -/

-- TODO: change names

variable {ι : Type*} {α : ι → Type*} {s : Set (Π i, α i)} {i : ι} {S : Set ι}

open Classical in
/-- Given a set of dependent functions, construct a function on a product space separating out
the coordinate `i` from the other ones. -/
noncomputable def fromXProd (S : Set ι) (s : Set (Π j, α j))
    (p : Sᶜ.restrict '' s × (Π i : S, α i)) :
    Π j, α j :=
  fun j ↦ if h : j ∈ S
    then (p.2 : Π j : ↑(S : Set ι), α j) ⟨j, h⟩
    else (p.1 : Π j : ↑(Sᶜ : Set ι), α j) ⟨j, h⟩

@[simp]
lemma fromXProd_same (p : Sᶜ.restrict '' s × (Π i : S, α i)) (j : S) :
    fromXProd S s p j = (p.2 : Π j : ↑(S : Set ι), α j) j := by
  have hj : ↑j ∈ S := j.prop
  simp [fromXProd, hj]

@[simp]
lemma fromXProd_of_compl (p : Sᶜ.restrict '' s × (Π i : S, α i)) (j : (Sᶜ : Set ι)) :
    fromXProd S s p j = (p.1 : Π j : ↑(Sᶜ : Set ι), α j) j := by
  have hj : ↑j ∉ S := j.prop
  simp [fromXProd, hj]

@[simp]
lemma restrict_compl_fromXProd (p : Sᶜ.restrict '' s × (Π i : S, α i)) :
    Sᶜ.restrict (fromXProd S s p) = p.1 := by ext; simp

lemma continuous_fromXProd [∀ i, TopologicalSpace (α i)] : Continuous (fromXProd S s) := by
  refine continuous_pi fun j ↦ ?_
  simp only [fromXProd]
  split_ifs with h
  · exact (continuous_apply _).comp continuous_snd
  · exact ((continuous_apply _).comp continuous_subtype_val).comp continuous_fst

lemma fromXProd_mem_preimage_image_restrict (p : Sᶜ.restrict '' s × (Π i : S, α i)) :
    fromXProd S s p ∈ Sᶜ.restrict ⁻¹' (Sᶜ.restrict '' s) := by
  obtain ⟨y, hy_mem_s, hy_eq⟩ := p.1.2
  exact ⟨y, hy_mem_s, hy_eq.trans (restrict_compl_fromXProd p).symm⟩

@[simp]
lemma fromXProd_restrict_compl (x : Sᶜ.restrict ⁻¹' (Sᶜ.restrict '' s)) :
    fromXProd S s ⟨⟨Sᶜ.restrict x, x.2⟩, fun i ↦ (x : Π j, α j) i⟩ = (x : Π j, α j) := by
  ext; simp [fromXProd]

/-- Homeomorphism between the set of functions that concide with a given set of functions away
from a given `i`, and dependent functions away from `i` times any value on `i`. -/
noncomputable
def XYEquiv (α : ι → Type*) [∀ i, TopologicalSpace (α i)] (S : Set ι) (s : Set (Π j, α j)) :
    Sᶜ.restrict ⁻¹' (Sᶜ.restrict '' s) ≃ₜ Sᶜ.restrict '' s × (Π i : S, α i) where
  toFun x := ⟨⟨Sᶜ.restrict x, x.2⟩, fun i ↦ (x : Π j, α j) i⟩
  invFun p := ⟨fromXProd S s p, fromXProd_mem_preimage_image_restrict p⟩
  left_inv x := by ext; simp
  right_inv p := by ext <;> simp
  continuous_toFun := by
    refine Continuous.prod_mk ?_ ?_
    · exact ((Pi.continuous_restrict _).comp continuous_subtype_val).subtype_mk _
    · rw [continuous_pi_iff]
      intro i
      exact (continuous_apply _).comp continuous_subtype_val
  continuous_invFun := continuous_fromXProd.subtype_mk _

lemma preimage_snd_xyEquiv [∀ i, TopologicalSpace (α i)] :
    Prod.snd '' (XYEquiv α S s ''
        ((fun (x : Sᶜ.restrict ⁻¹' (Sᶜ.restrict '' s)) ↦ (x : Π j, α j)) ⁻¹' s))
      = S.restrict '' s := by
  ext x
  simp only [ne_eq, XYEquiv, Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk, mem_image,
    mem_preimage, Subtype.exists, exists_and_left, Prod.exists, Prod.mk.injEq, exists_and_right,
    exists_eq_right, Subtype.mk.injEq, exists_prop]
  constructor
  · rintro ⟨y, _, z, hz_mem, _, hzx⟩
    exact ⟨z, hz_mem, hzx⟩
  · rintro ⟨z, hz_mem, hzx⟩
    exact ⟨Sᶜ.restrict z, mem_image_of_mem Sᶜ.restrict hz_mem, z, hz_mem,
      ⟨⟨⟨z, hz_mem, rfl⟩, rfl⟩, hzx⟩⟩

/-- The projection of a compact closed set onto a set of coordinates is closed. -/
theorem IsCompact.isClosed_image_restrict [∀ i, TopologicalSpace (α i)] (S : Set ι)
    (hs_compact : IsCompact s) (hs_closed : IsClosed s) :
    IsClosed (S.restrict '' s) := by
  rw [← preimage_snd_xyEquiv]
  have : CompactSpace (Sᶜ.restrict '' s) :=
    isCompact_iff_compactSpace.mp (hs_compact.image (Pi.continuous_restrict _))
  refine isClosedMap_snd_of_compactSpace _ ?_
  rw [Homeomorph.isClosed_image]
  exact hs_closed.preimage continuous_subtype_val

lemma isClosedMap_restrict_of_compactSpace [∀ i, TopologicalSpace (α i)] [∀ i, CompactSpace (α i)]
    {S : Set ι} :
    IsClosedMap (S.restrict : (Π i, α i) → _) := fun s hs ↦ by
  classical
  have : S.restrict (π := α) = Prod.fst ∘ (Homeomorph.piEquivPiSubtypeProd S α) := rfl
  rw [this, image_comp]
  refine isClosedMap_fst_of_compactSpace _ ?_
  exact (Homeomorph.isClosed_image _).mpr hs

lemma IsClosed.isClosed_image_restrict_singleton [∀ i, TopologicalSpace (α i)] (i : ι)
    (hs_compact : IsCompact s) (hs_closed : IsClosed s) :
    IsClosed ((fun x ↦ x i) '' s) := by
  suffices IsClosed (Set.restrict {i} '' s) by
    have : Homeomorph.piUnique _ ∘ Set.restrict {i} = fun (x : Π j, α j) ↦ x i := rfl
    rwa [← this, image_comp, Homeomorph.isClosed_image (Homeomorph.piUnique _)]
  exact hs_compact.isClosed_image_restrict {i} hs_closed

end isClosed_proj
