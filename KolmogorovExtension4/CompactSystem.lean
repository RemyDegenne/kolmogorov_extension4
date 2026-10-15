/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
module

public import Mathlib.Topology.Compactness.CompactSystem

/-!
# Compact systems of square cylinders

We show that a cylinder with a compact closed base is a countable intersection of finite unions of
compact closed square cylinders. Since those form a compact system
(`isCompactSystem_compactClosedSquareCylinders`, `IsCompactSystem.supClosure` and
`IsCompactSystem.countableInfClosure`), we get a compact system which can be used to approximate
measurable cylinders from inside.
-/

@[expose] public section

open Set MeasureTheory

variable {ι : Type*} {α : ι → Type*} [∀ i, TopologicalSpace (α i)]

lemma cylinder_univ_pi_mem_compactClosedSquareCylinders {J : Finset ι}
    {t : ∀ j : J, Set (α j)} (ht : ∀ j, IsCompact (t j) ∧ IsClosed (t j)) :
    cylinder J (univ.pi t) ∈ compactClosedSquareCylinders α := by
  classical
  refine ⟨J, fun i ↦ if h : i ∈ J then t ⟨i, h⟩ else ∅, fun i _ ↦ ?_, ?_⟩
  · by_cases h : i ∈ J <;> simp [h, ht]
  · ext x
    simpa [cylinder] using forall₂_congr fun i hi ↦ by simp [hi]

/-- Countable intersections of finite unions of compact closed square cylinders (and of `∅`)
form a compact system. -/
theorem isCompactSystem_countableInfClosure_supClosure_compactClosedSquareCylinders :
    IsCompactSystem
      (countableInfClosure (supClosure (insert ∅ (compactClosedSquareCylinders α)))) :=
  (isCompactSystem_compactClosedSquareCylinders α).insert_empty.supClosure.countableInfClosure

/-- A cylinder with a compact closed base is a countable intersection of finite unions of compact
closed square cylinders. -/
lemma cylinder_mem_countableInfClosure_supClosure [∀ i, SecondCountableTopology (α i)]
    [∀ i, R1Space (α i)] {J : Finset ι} {K : Set (Π j : J, α j)} (hK_compact : IsCompact K)
    (hK_closed : IsClosed K) :
    cylinder J K ∈ countableInfClosure (supClosure (insert ∅ (compactClosedSquareCylinders α))) := by
  classical
  -- `K` is contained in the box with compact closed sides `A j`
  let A : ∀ j : J, Set (α j) := fun j ↦ closure ((fun y ↦ y j) '' K)
  have hA j : IsCompact (A j) ∧ IsClosed (A j) :=
    ⟨(hK_compact.image (continuous_apply j)).closure, isClosed_closure⟩
  have hKA : K ⊆ univ.pi A := fun y hy j _ ↦ subset_closure (mem_image_of_mem _ hy)
  -- the complement of `K` is a countable union of open boxes which do not meet `K`
  let 𝒰 : Set (∀ j : J, Set (α j)) := {u | (∀ j, IsOpen (u j)) ∧ Disjoint (univ.pi u) K}
  obtain ⟨T, hT𝒰, hT_count, hT⟩ := TopologicalSpace.isOpen_biUnion_countable 𝒰 (fun u ↦ univ.pi u)
    fun u hu ↦ isOpen_set_pi finite_univ fun j _ ↦ hu.1 j
  have hK_compl : Kᶜ = ⋃ u ∈ T, univ.pi u := by
    rw [hT]
    refine Subset.antisymm (fun y hy ↦ ?_)
      (iUnion₂_subset fun u hu ↦ subset_compl_iff_disjoint_right.mpr hu.2)
    obtain ⟨u, hu, hu_sub⟩ := isOpen_pi_iff'.mp hK_closed.isOpen_compl y hy
    exact mem_biUnion (x := u) ⟨fun j ↦ (hu j).1, subset_compl_iff_disjoint_right.mp hu_sub⟩
      fun j _ ↦ (hu j).2
  -- for each such box `univ.pi u`, `K` is covered by the boxes `B u j` for `j : J`, obtained by
  -- replacing the side `A j` by `A j \ u j`
  let B : (∀ j : J, Set (α j)) → J → ∀ k : J, Set (α k) :=
    fun u j k ↦ if k = j then A k \ u k else A k
  have hB u (hu : u ∈ 𝒰) j k : IsCompact (B u j k) ∧ IsClosed (B u j k) := by
    simp only [B]
    split_ifs
    · exact ⟨(hA k).1.diff (hu.1 k), (hA k).2.sdiff (hu.1 k)⟩
    · exact hA k
  have hK_eq : K = univ.pi A ∩ ⋂ u : T, ⋃ j, univ.pi (B u j) := by
    refine Subset.antisymm (fun y hy ↦ ⟨hKA hy, mem_iInter.mpr fun u ↦ ?_⟩)
      fun y ⟨hyA, hy⟩ ↦ ?_
    · have hyu : y ∉ univ.pi u.1 := fun h ↦ (hT𝒰 u.2).2.notMem_of_mem_left h hy
      simp only [mem_univ_pi, not_forall] at hyu
      obtain ⟨j, hj⟩ := hyu
      refine mem_iUnion.mpr ⟨j, fun k _ ↦ ?_⟩
      simp only [B]
      split_ifs with hkj
      · subst hkj
        exact ⟨hKA hy k trivial, hj⟩
      · exact hKA hy k trivial
    · by_contra hyK
      rw [← mem_compl_iff, hK_compl, mem_iUnion₂] at hyK
      obtain ⟨u, hu, hyu⟩ := hyK
      obtain ⟨j, hj⟩ := mem_iUnion.mp (mem_iInter.mp hy ⟨u, hu⟩)
      have hj' := hj j trivial
      simp only [B, ite_true] at hj'
      exact hj'.2 (hyu j trivial)
  -- conclude by taking preimages
  have : Countable T := hT_count.to_subtype
  have h_eq : cylinder J K = ⋂ o : Option T, o.elim (cylinder J (univ.pi A))
      fun u ↦ ⋃ j, cylinder J (univ.pi (B u j)) := by
    rw [iInter_option]
    conv_lhs => rw [hK_eq]
    simp only [cylinder, preimage_inter, preimage_iInter, preimage_iUnion, Option.elim]
  rw [h_eq, ← iInf_eq_iInter]
  refine iInf_mem_countableInfClosure fun o ↦ ?_
  cases o with
  | none =>
    exact subset_supClosure
      (mem_insert_of_mem _ (cylinder_univ_pi_mem_compactClosedSquareCylinders hA))
  | some u =>
    exact supClosed_supClosure.iSup_mem (subset_supClosure (mem_insert _ _)) fun j ↦
      subset_supClosure (mem_insert_of_mem _
        (cylinder_univ_pi_mem_compactClosedSquareCylinders (hB u (hT𝒰 u.2) j)))
