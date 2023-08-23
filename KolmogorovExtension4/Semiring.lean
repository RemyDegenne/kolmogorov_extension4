import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.MeasureTheory.PiSystem
import Mathlib.MeasureTheory.Measure.OuterMeasure
import KolmogorovExtension.AuxLemmas

--#align_import semiring

/-! # Semirings of sets

A semi-ring of sets `C` is a family of sets containing `∅`, stable by intersection and such that
for all `s, t ∈ C`, `t \ s` is equal to a disjoint union of finitely many sets in `C`.

TODO

-/


open Finset Set MeasureTheory Order

open scoped BigOperators NNReal Topology ENNReal

namespace MeasureTheory

variable {α : Type _} {C : Set (Set α)} {s t : Set α}

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (s t «expr ∈ » C) -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (s t «expr ∈ » C) -/
/-- A semi-ring of sets `C` is a family of sets containing `∅`, stable by intersection and such that
for all `s, t ∈ C`, `t \ s` is equal to a disjoint union of finitely many sets in `C`. -/
structure SetSemiring (C : Set (Set α)) : Prop where
  empty_mem : ∅ ∈ C
  inter_mem : ∀ (s) (_ : s ∈ C) (t) (_ : t ∈ C), s ∩ t ∈ C
  diff_eq_Union' :
    ∀ (s) (_ : s ∈ C) (t) (_ : t ∈ C),
      ∃ (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (h_dis : PairwiseDisjoint (I : Set (Set α)) id),
        t \ s = ⋃₀ I

namespace SetSemiring

theorem isPiSystem (hC : SetSemiring C) : IsPiSystem C := fun s hs t ht _ => hC.inter_mem s hs t ht

/-- In a semi-ring of sets `C`, for all `s, t ∈ C`, `t \ s` is equal to a disjoint union of finitely
many sets in `C`. This definitions gives a finset of sets that satisfy that equality.
We remove the empty set to ensure that `s ∉ hC.diff_finset hs ht`. -/
noncomputable def diffFinset (hC : SetSemiring C) {s t : Set α} (hs : s ∈ C) (ht : t ∈ C)
    [DecidableEq (Set α)] : Finset (Set α) :=
  (hC.diff_eq_Union' s hs t ht).some \ {∅}

theorem empty_not_mem_diffFinset (hC : SetSemiring C) (hs : s ∈ C) (ht : t ∈ C)
    [DecidableEq (Set α)] : ∅ ∉ hC.diff_finset hs ht := by
  simp only [set_semiring.diff_finset, mem_sdiff, Finset.mem_singleton, eq_self_iff_true, not_true,
    and_false_iff, not_false_iff]

theorem diffFinset_subset (hC : SetSemiring C) (hs : s ∈ C) (ht : t ∈ C) [DecidableEq (Set α)] :
    ↑(hC.diff_finset hs ht) ⊆ C :=
  by
  simp only [set_semiring.diff_finset, coe_sdiff, coe_singleton, diff_singleton_subset_iff]
  exact (hC.diff_eq_Union' s hs t ht).choose_spec.some.trans (Set.subset_insert _ _)

theorem diffFinset_disjoint (hC : SetSemiring C) (hs : s ∈ C) (ht : t ∈ C) [DecidableEq (Set α)] :
    PairwiseDisjoint (hC.diff_finset hs ht : Set (Set α)) id :=
  by
  simp only [set_semiring.diff_finset, coe_sdiff, coe_singleton]
  exact
    Set.PairwiseDisjoint.subset (hC.diff_eq_Union' s hs t ht).choose_spec.choose_spec.some
      (Set.diff_subset _ _)

theorem diff_eq_sUnion (hC : SetSemiring C) (hs : s ∈ C) (ht : t ∈ C) [DecidableEq (Set α)] :
    t \ s = ⋃₀ hC.diff_finset hs ht :=
  by
  rw [(hC.diff_eq_Union' s hs t ht).choose_spec.choose_spec.choose_spec]
  simp only [set_semiring.diff_finset, coe_sdiff, coe_singleton, diff_singleton_subset_iff]
  rw [sUnion_diff_singleton_empty]

theorem not_mem_diffFinset (hC : SetSemiring C) (hs : s ∈ C) (ht : t ∈ C) [DecidableEq (Set α)] :
    s ∉ hC.diff_finset hs ht := by
  intro hs_mem
  suffices s ⊆ t \ s by
    have h := @disjoint_sdiff_self_right _ s t _
    specialize h le_rfl this
    simp only [Set.bot_eq_empty, Set.le_eq_subset, subset_empty_iff] at h 
    refine' hC.empty_not_mem_diff_finset hs ht _
    rwa [← h]
  rw [hC.diff_eq_sUnion hs ht]
  exact subset_sUnion_of_mem hs_mem

theorem eq_sUnion_insert_diffFinset (hC : SetSemiring C) (hs : s ∈ C) (ht : t ∈ C) (hst : s ⊆ t)
    [DecidableEq (Set α)] : t = ⋃₀ insert s (hC.diff_finset hs ht) :=
  by
  conv_lhs => rw [← union_diff_cancel hst, hC.diff_eq_sUnion hs ht]
  classical rw [sUnion_eq_bUnion, ← bUnion_insert s (hC.diff_finset _ _), ← coe_insert, ←
    sUnion_eq_bUnion]

theorem disjoint_sUnion_diffFinset (hC : SetSemiring C) (hs : s ∈ C) (ht : t ∈ C)
    [DecidableEq (Set α)] : Disjoint s (⋃₀ hC.diff_finset hs ht) := by rw [← hC.diff_eq_sUnion];
  exact disjoint_sdiff_right

theorem pairwiseDisjoint_insert (hC : SetSemiring C) (hs : s ∈ C) (ht : t ∈ C)
    [DecidableEq (Set α)] : (insert s (hC.diff_finset hs ht) : Set (Set α)).PairwiseDisjoint id :=
  by
  have h := hC.diff_finset_disjoint hs ht
  refine' pairwise_disjoint.insert_of_not_mem h (hC.not_mem_diff_finset hs ht) fun u hu => _
  simp_rw [id.def]
  refine' Disjoint.mono_right _ (hC.disjoint_sUnion_diff_finset hs ht)
  simp only [Set.le_eq_subset]
  exact subset_sUnion_of_mem hu

theorem eq_add_diffFinset_of_subset (hC : SetSemiring C) (m : Set α → ℝ≥0∞)
    (m_add :
      ∀ (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (h_dis : PairwiseDisjoint (I : Set (Set α)) id)
        (h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) = ∑ u in I, m u)
    (hs : s ∈ C) (ht : t ∈ C) (hst : s ⊆ t) [DecidableEq (Set α)] :
    m t = m s + ∑ i in hC.diff_finset hs ht, m i := by
  classical
  conv_lhs => rw [hC.eq_sUnion_insert_diff_finset hs ht hst]
  rw [← coe_insert, m_add]
  · rw [sum_insert]
    exact hC.not_mem_diff_finset hs ht
  · rw [coe_insert]
    exact set.insert_subset.mpr ⟨hs, hC.diff_finset_subset hs ht⟩
  · rw [coe_insert]
    exact hC.pairwise_disjoint_insert hs ht
  · rw [coe_insert]
    rwa [← hC.eq_sUnion_insert_diff_finset hs ht hst]

theorem exists_disjoint_finset_diff_eq (hC : SetSemiring C) (hs : s ∈ C) (I : Finset (Set α))
    (hI : ↑I ⊆ C) :
    ∃ (J : Finset (Set α)) (h_ss : ↑J ⊆ C) (h_dis : PairwiseDisjoint (J : Set (Set α)) id),
      s \ ⋃₀ I = ⋃₀ J :=
  by
  classical
  revert hI
  refine' Finset.induction _ _ I
  · intro
    simp only [coe_empty, sUnion_empty, diff_empty, exists_prop]
    refine' ⟨{s}, singleton_subset_set_iff.mpr hs, _⟩
    simp only [coe_singleton, pairwise_disjoint_singleton, sUnion_singleton, eq_self_iff_true,
      and_self_iff]
  intro t I' htI' h h_insert_subset
  rw [coe_insert] at h_insert_subset 
  have ht : t ∈ C := h_insert_subset (Set.mem_insert _ _)
  obtain ⟨J, h_ss, h_dis, h_eq⟩ := h ((Set.subset_insert _ _).trans h_insert_subset)
  let Ju : ∀ (u) (hu : u ∈ C), Finset (Set α) := fun u hu => hC.diff_finset ht hu
  have hJu_subset : ∀ (u) (hu : u ∈ C), ↑(Ju u hu) ⊆ C :=
    by
    intro u hu x hx
    simp_rw [Ju] at hx 
    exact hC.diff_finset_subset ht hu hx
  have hJu_disj : ∀ (u) (hu : u ∈ C), (Ju u hu : Set (Set α)).PairwiseDisjoint id := fun u hu =>
    hC.diff_finset_disjoint ht hu
  have hJu_sUnion : ∀ (u) (hu : u ∈ C), ⋃₀ (Ju u hu : Set (Set α)) = u \ t := fun u hu =>
    (hC.diff_eq_sUnion ht hu).symm
  have hJu_disj' :
    ∀ (u) (hu : u ∈ C) (v) (hv : v ∈ C) (h_dis : Disjoint u v),
      Disjoint (⋃₀ (Ju u hu : Set (Set α))) (⋃₀ ↑(Ju v hv)) :=
    by
    intro u hu v hv huv_disj
    rw [hJu_sUnion, hJu_sUnion]
    exact disjoint_of_subset (Set.diff_subset u t) (Set.diff_subset v t) huv_disj
  let J' : Finset (Set α) := Finset.biUnion (Finset.univ : Finset J) fun u => Ju u (h_ss u.Prop)
  have hJ'_subset : ↑J' ⊆ C := by
    simp_rw [J']
    intro u
    simp only [Subtype.coe_mk, univ_eq_attach, coe_bUnion, mem_coe, mem_attach, Union_true,
      mem_Union, Finset.exists_coe, bex_imp]
    intro v hv huvt
    exact hJu_subset v (h_ss hv) huvt
  refine' ⟨J', hJ'_subset, _, _⟩
  · simp_rw [J']
    rw [Finset.coe_biUnion]
    refine' pairwise_disjoint.bUnion _ _
    · simp only [univ_eq_attach, mem_coe, id.def, supr_eq_Union]
      simp_rw [pairwise_disjoint, Set.Pairwise, Function.onFun]
      intro x _ y _ hxy
      have hxy_disj : Disjoint (x : Set α) y :=
        by
        by_contra h_contra
        refine' hxy _
        refine' Subtype.ext _
        exact h_dis.elim x.prop y.prop h_contra
      convert hJu_disj' (x : Set α) (h_ss x.prop) y (h_ss y.prop) hxy_disj
      · rw [sUnion_eq_bUnion]
        congr
      · rw [sUnion_eq_bUnion]
        congr
    · exact fun u hu => hJu_disj _ _
  · rw [coe_insert, sUnion_insert, Set.union_comm, ← Set.diff_diff, h_eq]
    simp_rw [sUnion_eq_bUnion, Set.iUnion_diff, J']
    simp only [Subtype.coe_mk, mem_coe, Finset.mem_biUnion, Finset.mem_univ, exists_true_left,
      Finset.exists_coe, Union_exists]
    rw [Union_comm]
    congr 1 with i
    by_cases hi : i ∈ J
    · simp only [hi, Union_true, exists_prop]
      rw [← hJu_sUnion i (h_ss hi), sUnion_eq_bUnion]
      simp only [mem_coe]
    · simp only [hi, Union_of_empty, Union_empty]

section Diff₀

/-- In a semiring of sets `C`, for all set `s ∈ C` and finite set of sets `I ⊆ C`, `diff₀` is a
finite set of sets in `C` such that `s \ ⋃₀ I = ⋃₀ (hC.diff₀ hs I hI)`.
`diff_finset` can be seen as a special case of `diff₀` where `I` is a singleton.

todo: names -/
noncomputable def diff₀ (hC : SetSemiring C) (hs : s ∈ C) (I : Finset (Set α)) (hI : ↑I ⊆ C)
    [DecidableEq (Set α)] : Finset (Set α) :=
  (hC.exists_disjoint_finset_diff_eq hs I hI).some \ {∅}

theorem empty_not_mem_diff₀ (hC : SetSemiring C) (hs : s ∈ C) (I : Finset (Set α)) (hI : ↑I ⊆ C)
    [DecidableEq (Set α)] : ∅ ∉ hC.diff₀ hs I hI := by
  simp only [set_semiring.diff₀, mem_sdiff, Finset.mem_singleton, eq_self_iff_true, not_true,
    and_false_iff, not_false_iff]

theorem diff₀_subset (hC : SetSemiring C) (hs : s ∈ C) (I : Finset (Set α)) (hI : ↑I ⊆ C)
    [DecidableEq (Set α)] : ↑(hC.diff₀ hs I hI) ⊆ C :=
  by
  simp only [set_semiring.diff₀, coe_sdiff, coe_singleton, diff_singleton_subset_iff]
  exact (hC.exists_disjoint_finset_diff_eq hs I hI).choose_spec.some.trans (Set.subset_insert _ _)

theorem pairwiseDisjoint_diff₀ (hC : SetSemiring C) (hs : s ∈ C) (I : Finset (Set α)) (hI : ↑I ⊆ C)
    [DecidableEq (Set α)] : (hC.diff₀ hs I hI : Set (Set α)).PairwiseDisjoint id :=
  by
  simp only [set_semiring.diff₀, coe_sdiff, coe_singleton]
  exact
    Set.PairwiseDisjoint.subset
      (hC.exists_disjoint_finset_diff_eq hs I hI).choose_spec.choose_spec.some (Set.diff_subset _ _)

theorem diff_sUnion_eq_sUnion_diff₀ (hC : SetSemiring C) (hs : s ∈ C) (I : Finset (Set α))
    (hI : ↑I ⊆ C) [DecidableEq (Set α)] : s \ ⋃₀ I = ⋃₀ hC.diff₀ hs I hI :=
  by
  rw [(hC.exists_disjoint_finset_diff_eq hs I hI).choose_spec.choose_spec.choose_spec]
  simp only [set_semiring.diff₀, coe_sdiff, coe_singleton, diff_singleton_subset_iff]
  rw [sUnion_diff_singleton_empty]

theorem sUnion_diff₀_subset (hC : SetSemiring C) (hs : s ∈ C) (I : Finset (Set α)) (hI : ↑I ⊆ C)
    [DecidableEq (Set α)] : ⋃₀ (hC.diff₀ hs I hI : Set (Set α)) ⊆ s :=
  by
  rw [← hC.diff_sUnion_eq_sUnion_diff₀]
  exact diff_subset _ _

theorem disjoint_sUnion_diff₀ (hC : SetSemiring C) (hs : s ∈ C) (I : Finset (Set α)) (hI : ↑I ⊆ C)
    [DecidableEq (Set α)] : Disjoint (⋃₀ (I : Set (Set α))) (⋃₀ hC.diff₀ hs I hI) := by
  rw [← hC.diff_sUnion_eq_sUnion_diff₀]; exact Set.disjoint_sdiff_right

theorem disjoint_diff₀ (hC : SetSemiring C) (hs : s ∈ C) (I : Finset (Set α)) (hI : ↑I ⊆ C)
    [DecidableEq (Set α)] : Disjoint I (hC.diff₀ hs I hI) :=
  by
  by_contra h
  rw [Finset.not_disjoint_iff] at h 
  obtain ⟨u, huI, hu_diff₀⟩ := h
  have h_disj : u ≤ ⊥ :=
    hC.disjoint_sUnion_diff₀ hs I hI (subset_sUnion_of_mem huI) (subset_sUnion_of_mem hu_diff₀)
  simp only [Set.bot_eq_empty, Set.le_eq_subset, subset_empty_iff] at h_disj 
  refine' hC.empty_not_mem_diff₀ hs I hI _
  rwa [h_disj] at hu_diff₀ 

theorem pairwiseDisjoint_union_diff₀ (hC : SetSemiring C) (hs : s ∈ C) (I : Finset (Set α))
    (hI : ↑I ⊆ C) (h_dis : PairwiseDisjoint (I : Set (Set α)) id) [DecidableEq (Set α)] :
    (I ∪ hC.diff₀ hs I hI : Set (Set α)).PairwiseDisjoint id :=
  by
  rw [pairwise_disjoint_union]
  refine' ⟨h_dis, hC.pairwise_disjoint_diff₀ hs I hI, fun u hu v hv hu_ne_v => _⟩
  simp_rw [id.def]
  exact
    disjoint_of_subset (subset_sUnion_of_mem hu) (subset_sUnion_of_mem hv)
      (hC.disjoint_sUnion_diff₀ hs I hI)

theorem eq_union_sUnion_diff₀_of_subset (hC : SetSemiring C) (hs : s ∈ C) (I : Finset (Set α))
    (hI : ↑I ⊆ C) (hI_ss : ⋃₀ ↑I ⊆ s) [DecidableEq (Set α)] : s = ⋃₀ I ∪ ⋃₀ hC.diff₀ hs I hI := by
  conv_lhs => rw [← union_diff_cancel hI_ss, hC.diff_sUnion_eq_sUnion_diff₀ hs I hI]

theorem eq_sUnion_union_diff₀_of_subset (hC : SetSemiring C) (hs : s ∈ C) (I : Finset (Set α))
    (hI : ↑I ⊆ C) (hI_ss : ⋃₀ ↑I ⊆ s) [DecidableEq (Set α)] : s = ⋃₀ ↑(I ∪ hC.diff₀ hs I hI) :=
  by
  conv_lhs => rw [eq_union_sUnion_diff₀_of_subset hC hs I hI hI_ss]
  simp_rw [coe_union]
  rw [sUnion_union]

end Diff₀

end SetSemiring

section Ordered

theorem Finset.mem_map_univ_asEmbedding {α β : Type _} [Fintype α] {p : β → Prop}
    (e : α ≃ Subtype p) {b : β} : b ∈ Finset.map e.asEmbedding univ ↔ p b :=
  by
  rw [mem_map]
  simp only [Finset.mem_univ, Equiv.asEmbedding_apply, Function.comp_apply, exists_true_left]
  refine' ⟨fun h => _, fun h => _⟩
  · obtain ⟨a, rfl⟩ := h
    exact (e a).Prop
  · suffices ∃ a, e a = ⟨b, h⟩ by
      obtain ⟨a, ha⟩ := this
      refine' ⟨a, _⟩
      rw [ha]
      rfl
    exact e.surjective _

variable {J : Finset (Set α)}

/-- An ordering of the elements of a finset. -/
noncomputable def Finset.ordered (J : Finset α) : Fin J.card ↪ α :=
  J.equivFin.symm.asEmbedding

theorem map_ordered (J : Finset (Set α)) : Finset.map J.ordered (univ : Finset (Fin J.card)) = J :=
  by ext1 s; simp_rw [finset.ordered, finset.mem_map_univ_as_embedding]

theorem ordered_mem (n : Fin J.card) : J.ordered n ∈ J := by simp_rw [finset.ordered];
  exact coe_mem _

theorem ordered_mem' (hJ : ↑J ⊆ C) (n : Fin J.card) : J.ordered n ∈ C :=
  hJ (ordered_mem n)

theorem iUnion_ordered (J : Finset (Set α)) : (⋃ i : Fin J.card, J.ordered i) = ⋃₀ J :=
  by
  conv_rhs => rw [← map_ordered J]
  simp_rw [sUnion_eq_bUnion, coe_map, Set.biUnion_image]
  simp only [mem_coe, Finset.mem_univ, Union_true]

theorem sum_ordered {β : Type _} [AddCommMonoid β] (J : Finset (Set α)) (m : Set α → β) :
    ∑ i : Fin J.card, m (J.ordered i) = ∑ u in J, m u := by conv_rhs => rw [← map_ordered J];
  rw [sum_map]

/-- The n first sets in `J.ordered`. -/
noncomputable def finsetLt (J : Finset (Set α)) : Fin J.card → Finset (Set α) := fun n =>
  (Finset.filter (fun j : Fin J.card => j < n) univ).map J.ordered

theorem finsetLt_zero {J : Finset (Set α)} (hJ : 0 < J.card) : finsetLt J ⟨0, hJ⟩ = ∅ :=
  by
  rw [finset_lt]
  simp only [univ_eq_attach, map_eq_empty]
  rw [filter_eq_empty_iff]
  intro n hn
  simp only [not_lt]
  rw [← Fin.eta n n.2, Fin.mk_le_mk]
  exact zero_le'

theorem finsetLt_mono (J : Finset (Set α)) : Monotone (finsetLt J) :=
  by
  intro n m hnm s
  rw [finset_lt, mem_map]
  rintro ⟨i, hi, rfl⟩
  simp only [Equiv.asEmbedding_apply, Function.comp_apply, mem_map, mem_filter, Finset.mem_univ,
    true_and_iff, exists_prop]
  refine' ⟨i, _, rfl⟩
  rw [mem_filter] at hi 
  exact hi.2.trans_le hnm

theorem finsetLt_subset (J : Finset (Set α)) (n : Fin J.card) : finsetLt J n ⊆ J := by intro u;
  rw [finset_lt, mem_map]; rintro ⟨i, hi, rfl⟩; exact ordered_mem i

theorem mem_finsetLt (J : Finset (Set α)) (n : Fin J.card) {s : Set α} :
    s ∈ finsetLt J n ↔ ∃ m < n, s = J.ordered m :=
  by
  rw [finset_lt, mem_map]
  simp only [mem_filter, Finset.mem_univ, true_and_iff, Equiv.asEmbedding_apply,
    Function.comp_apply, exists_prop]
  simp_rw [@eq_comm _ _ s]

theorem ordered_mem_finsetLt (J : Finset (Set α)) {n m : Fin J.card} (hnm : n < m) :
    J.ordered n ∈ finsetLt J m := by rw [mem_finset_lt _ _]; exact ⟨n, hnm, rfl⟩

theorem finsetLt_subset' (J : Finset (Set α)) (hJ : ↑J ⊆ C) (n : Fin J.card) :
    ↑(finsetLt J n) ⊆ C :=
  (Finset.coe_subset.mpr (finsetLt_subset J n)).trans hJ

theorem sUnion_finsetLt_eq_bUnion (J : Finset (Set α)) (n : Fin J.card) :
    ⋃₀ (finsetLt J n : Set (Set α)) = ⋃ i < n, J.ordered i :=
  by
  ext1 a
  simp_rw [mem_sUnion, mem_coe, mem_finset_lt, mem_Union]
  constructor
  · rintro ⟨t, ⟨m, hmn, rfl⟩, hat⟩
    exact ⟨m, hmn, hat⟩
  · rintro ⟨m, hmn, hat⟩
    exact ⟨J.ordered m, ⟨m, hmn, rfl⟩, hat⟩

namespace SetSemiring

section IndexedDiff₀

variable [DecidableEq (Set α)]

/-- A finite set of sets in `C` such that
`⋃₀ ↑(hC.indexed_diff₀ J hJ n) = J.ordered n \ ⋃₀ finset_lt J n`. -/
noncomputable def indexedDiff₀ (hC : SetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C)
    (n : Fin J.card) : Finset (Set α) :=
  hC.diff₀ (ordered_mem' hJ n) (finsetLt J n) (finsetLt_subset' J hJ n)

theorem sUnion_indexedDiff₀ (hC : SetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C)
    (n : Fin J.card) : ⋃₀ ↑(hC.indexedDiff₀ J hJ n) = J.ordered n \ ⋃₀ finsetLt J n :=
  (hC.diff_sUnion_eq_sUnion_diff₀ _ _ _).symm

theorem indexedDiff₀_subset (hC : SetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C)
    (n : Fin J.card) : ↑(hC.indexedDiff₀ J hJ n) ⊆ C :=
  hC.diff₀_subset _ _ _

theorem sUnion_indexedDiff₀_subset (hC : SetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C)
    (n : Fin J.card) : ⋃₀ ↑(hC.indexedDiff₀ J hJ n) ⊆ J.ordered n :=
  subset_trans (hC.sUnion_indexedDiff₀ J hJ n).Subset (Set.diff_subset _ _)

theorem empty_not_mem_indexedDiff₀ (hC : SetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C)
    (n : Fin J.card) : ∅ ∉ hC.indexedDiff₀ J hJ n := by rw [set_semiring.indexed_diff₀];
  exact hC.empty_not_mem_diff₀ _ _ _

theorem subset_ordered_of_mem_indexedDiff₀ (hC : SetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C)
    {n : Fin J.card} (h : s ∈ hC.indexedDiff₀ J hJ n) : s ⊆ J.ordered n :=
  by
  refine'
    subset.trans _
      (hC.sUnion_diff₀_subset (ordered_mem' hJ n) (finset_lt J n) (finset_lt_subset' J hJ n))
  exact subset_sUnion_of_mem h

theorem iUnion_sUnion_indexedDiff₀ (hC : SetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C) :
    (⋃ i, ⋃₀ (hC.indexedDiff₀ J hJ i : Set (Set α))) = ⋃₀ J :=
  by
  rw [← Union_ordered]
  refine' subset_antisymm (fun a => _) fun a => _
  · simp_rw [mem_Union, mem_sUnion]
    rintro ⟨i, t, ht, hat⟩
    exact ⟨i, subset_ordered_of_mem_indexed_diff₀ hC J hJ ht hat⟩
  · simp_rw [mem_Union]
    intro h
    have h' : ∃ (i : ℕ) (hi : i < J.card), a ∈ J.ordered ⟨i, hi⟩ :=
      by
      obtain ⟨i, hai⟩ := h
      refine' ⟨i.1, i.2, _⟩
      convert hai
      ext
      norm_cast
    classical
    let i : ℕ := Nat.find h'
    have hi : i < J.card := (Nat.find_spec h').some
    have ha_mem_i : a ∈ J.ordered ⟨i, hi⟩ := (Nat.find_spec h').choose_spec
    refine' ⟨⟨i, hi⟩, _⟩
    rw [sUnion_indexed_diff₀, Set.mem_diff]
    refine' ⟨ha_mem_i, _⟩
    rw [sUnion_finset_lt_eq_bUnion]
    simp only [mem_Union, exists_prop, not_exists, not_and]
    intro j hj_lt hj
    have hj_lt' : ↑j < i := by rwa [← Fin.eta j j.2, Fin.mk_lt_mk] at hj_lt 
    refine' (Nat.lt_find_iff h' j).mp hj_lt' j le_rfl ⟨hj_lt'.trans hi, _⟩
    convert hj
    ext
    rfl

theorem disjoint_sUnion_finsetLt_of_mem_indexedDiff₀ (hC : SetSemiring C) (J : Finset (Set α))
    (hJ : ↑J ⊆ C) {n : Fin J.card} (h : s ∈ hC.indexedDiff₀ J hJ n) :
    Disjoint s (⋃₀ finsetLt J n) :=
  by
  refine' Disjoint.mono_left (subset_sUnion_of_mem h : s ⊆ ⋃₀ ↑(hC.indexed_diff₀ J hJ n)) _
  rw [set_semiring.sUnion_indexed_diff₀ hC J hJ n, Set.disjoint_iff_inter_eq_empty, Set.inter_comm,
    inter_diff_self]

theorem disjoint_ordered_of_mem_indexedDiff₀ (hC : SetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C)
    {n m : Fin J.card} (h : s ∈ hC.indexedDiff₀ J hJ n) (hnm : m < n) : Disjoint s (J.ordered m) :=
  by
  refine' Disjoint.mono_right _ (hC.disjoint_sUnion_finset_lt_of_mem_indexed_diff₀ J hJ h)
  exact subset_sUnion_of_mem (ordered_mem_finset_lt J hnm)

theorem disjoint_of_mem_indexedDiff₀_of_lt (hC : SetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C)
    {n m : Fin J.card} (hnm : n < m) (hs : s ∈ hC.indexedDiff₀ J hJ n)
    (ht : t ∈ hC.indexedDiff₀ J hJ m) : Disjoint s t :=
  by
  have hs_subset : s ⊆ J.ordered n := hC.subset_ordered_of_mem_indexed_diff₀ J hJ hs
  have hs_disj : Disjoint t (J.ordered n) := hC.disjoint_ordered_of_mem_indexed_diff₀ J hJ ht hnm
  exact Disjoint.mono_left hs_subset hs_disj.symm

theorem disjoint_of_mem_indexedDiff₀ (hC : SetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C)
    {n m : Fin J.card} (hnm : n ≠ m) (hs : s ∈ hC.indexedDiff₀ J hJ n)
    (ht : t ∈ hC.indexedDiff₀ J hJ m) : Disjoint s t :=
  by
  cases' lt_or_lt_iff_ne.mpr hnm with h h
  · exact hC.disjoint_of_mem_indexed_diff₀_of_lt J hJ h hs ht
  · exact (hC.disjoint_of_mem_indexed_diff₀_of_lt J hJ h ht hs).symm

theorem disjoint_indexedDiff₀ (hC : SetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C)
    {n m : Fin J.card} (hnm : n ≠ m) : Disjoint (hC.indexedDiff₀ J hJ n) (hC.indexedDiff₀ J hJ m) :=
  by
  rw [Finset.disjoint_iff_inter_eq_empty]
  ext1 s
  simp only [Finset.mem_inter, Finset.not_mem_empty, iff_false_iff, not_and]
  intro hsn hsm
  have : Disjoint s s := hC.disjoint_of_mem_indexed_diff₀ J hJ hnm hsn hsm
  rw [Set.disjoint_iff_inter_eq_empty, Set.inter_self] at this 
  rw [this] at hsn 
  exact hC.empty_not_mem_indexed_diff₀ _ _ _ hsn

theorem pairwiseDisjoint_indexedDiff₀ (hC : SetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C) :
    PairwiseDisjoint (↑(univ : Finset (Fin J.card))) (hC.indexedDiff₀ J hJ) := fun _ _ _ _ hnm =>
  hC.disjoint_indexedDiff₀ J hJ hnm

theorem pairwiseDisjoint_indexed_diff₀' (hC : SetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C)
    (n : Fin J.card) : PairwiseDisjoint ↑(hC.indexedDiff₀ J hJ n) (id : Set α → Set α) :=
  hC.pairwiseDisjoint_diff₀ _ _ _

end IndexedDiff₀

section AllDiff₀

variable [DecidableEq (Set α)]

/-- The union of all sets in `indexed_diff₀`, as a `finset`. -/
noncomputable def allDiff₀ (hC : SetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C) :
    Finset (Set α) :=
  Finset.disjUnion univ (hC.indexedDiff₀ J hJ) (hC.pairwiseDisjoint_indexedDiff₀ J hJ)

theorem pairwiseDisjoint_allDiff₀ (hC : SetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C) :
    PairwiseDisjoint ↑(hC.allDiff₀ J hJ) (id : Set α → Set α) :=
  by
  intro u hu v hv huv
  simp_rw [Function.onFun, id.def]
  simp_rw [set_semiring.all_diff₀, mem_coe, Finset.mem_disjiUnion] at hu hv 
  obtain ⟨n, hn, huBn⟩ := hu
  obtain ⟨m, hm, hvBm⟩ := hv
  by_cases hnm : n = m
  · rw [← hnm] at hvBm 
    exact hC.pairwise_disjoint_indexed_diff₀' _ _ n huBn hvBm huv
  · exact hC.disjoint_of_mem_indexed_diff₀ J hJ hnm huBn hvBm

theorem allDiff₀_subset (hC : SetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C) :
    ↑(hC.allDiff₀ J hJ) ⊆ C := by
  intro s
  rw [mem_coe, set_semiring.all_diff₀, mem_disj_Union]
  rintro ⟨n, hn, h_mem⟩
  exact hC.indexed_diff₀_subset J hJ n h_mem

theorem Finset.sUnion_disjUnion {α β : Type _} {f : α → Finset (Set β)} (I : Finset α)
    (hf : (I : Set α).PairwiseDisjoint f) :
    ⋃₀ (I.disjUnionₓ f hf : Set (Set β)) = ⋃ a ∈ I, ⋃₀ ↑(f a) :=
  by
  ext1 b
  simp_rw [mem_sUnion, mem_Union, mem_coe, mem_disj_Union, mem_sUnion, mem_coe]
  constructor
  · rintro ⟨t, ⟨a, haI, hatf⟩, hbt⟩
    exact ⟨a, haI, t, hatf, hbt⟩
  · rintro ⟨a, haI, t, hatf, hbt⟩
    exact ⟨t, ⟨a, haI, hatf⟩, hbt⟩

theorem sUnion_allDiff₀ (hC : SetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C) :
    ⋃₀ (hC.allDiff₀ J hJ : Set (Set α)) = ⋃₀ J := by
  simp only [all_diff₀, finset.sUnion_disj_Union, Finset.mem_univ, Union_true,
    Union_sUnion_indexed_diff₀]

end AllDiff₀

end SetSemiring

end Ordered

structure SetRing (C : Set (Set α)) : Prop where
  empty_mem : ∅ ∈ C
  union_mem : ∀ {s t}, s ∈ C → t ∈ C → s ∪ t ∈ C
  diff_mem : ∀ {s t}, s ∈ C → t ∈ C → s \ t ∈ C

namespace SetRing

theorem inter_mem (hC : SetRing C) (hs : s ∈ C) (ht : t ∈ C) : s ∩ t ∈ C := by
  rw [← diff_diff_right_self]; exact hC.diff_mem hs (hC.diff_mem hs ht)

theorem setSemiring (hC : SetRing C) : SetSemiring C :=
  { empty_mem := hC.empty_mem
    inter_mem := fun s hs t ht => hC.inter_mem hs ht
    diff_eq_Union' := by
      refine' fun s hs t ht => ⟨{t \ s}, _, _, _⟩
      · simp only [coe_singleton, Set.singleton_subset_iff]
        exact hC.diff_mem ht hs
      · simp only [coe_singleton, pairwise_disjoint_singleton]
      · simp only [coe_singleton, sUnion_singleton] }

theorem iUnion_le_mem (hC : SetRing C) {s : ℕ → Set α} (hs : ∀ n, s n ∈ C) (n : ℕ) :
    (⋃ i ≤ n, s i) ∈ C := by
  induction' n with n hn
  · simp only [Nat.zero_eq, le_zero_iff, Union_Union_eq_left, exists_prop]
    exact hs 0
  rw [Set.bUnion_le_succ]
  exact hC.union_mem hn (hs _)

theorem iInter_le_mem (hC : SetRing C) {s : ℕ → Set α} (hs : ∀ n, s n ∈ C) (n : ℕ) :
    (⋂ i ≤ n, s i) ∈ C := by
  induction' n with n hn
  · simp only [Nat.zero_eq, le_zero_iff, Inter_Inter_eq_left, exists_prop]
    exact hs 0
  rw [Set.bInter_le_succ]
  exact hC.inter_mem hn (hs _)

theorem partialSups_mem (hC : SetRing C) {s : ℕ → Set α} (hs : ∀ n, s n ∈ C) (n : ℕ) :
    partialSups s n ∈ C := by rw [partialSups_eq_biSup, supr_eq_Union]; exact hC.Union_le_mem hs n

theorem disjointed_mem (hC : SetRing C) {s : ℕ → Set α} (hs : ∀ n, s n ∈ C) (n : ℕ) :
    disjointed s n ∈ C := by
  cases n
  · rw [disjointed_zero]; exact hs 0
  · rw [disjointed_succ]; exact hC.diff_mem (hs n.succ) (hC.partial_sups_mem hs n)

theorem accumulate_mem (hC : SetRing C) {s : ℕ → Set α} (hs : ∀ i, s i ∈ C) (n : ℕ) :
    Set.Accumulate s n ∈ C := by
  induction' n with n hn
  · simp only [Set.Accumulate, le_zero_iff, Set.iUnion_iUnion_eq_left, hs 0]
  rw [Set.accumulate_succ]
  refine' hC.union_mem hn (hs _)

end SetRing

structure SetField (C : Set (Set α)) extends SetRing C : Prop where
  univ_mem : Set.univ ∈ C

namespace SetField

theorem union_mem (hC : SetField C) (hs : s ∈ C) (ht : t ∈ C) : s ∪ t ∈ C :=
  hC.to_setRing.union_mem hs ht

theorem inter_mem (hC : SetField C) (hs : s ∈ C) (ht : t ∈ C) : s ∩ t ∈ C :=
  hC.to_setRing.inter_mem hs ht

theorem diff_mem (hC : SetField C) (hs : s ∈ C) (ht : t ∈ C) : s \ t ∈ C :=
  hC.to_setRing.diff_mem hs ht

theorem compl_mem (hC : SetField C) (hs : s ∈ C) : sᶜ ∈ C := by rw [compl_eq_univ_diff];
  exact hC.diff_mem hC.univ_mem hs

theorem toSetSemiring (hC : SetField C) : SetSemiring C :=
  hC.to_setRing.SetSemiring

theorem iUnion_le_mem (hC : SetField C) {s : ℕ → Set α} (hs : ∀ n, s n ∈ C) (n : ℕ) :
    (⋃ i ≤ n, s i) ∈ C :=
  hC.to_setRing.iUnion_le_mem hs n

theorem iInter_le_mem (hC : SetField C) {s : ℕ → Set α} (hs : ∀ n, s n ∈ C) (n : ℕ) :
    (⋂ i ≤ n, s i) ∈ C :=
  hC.to_setRing.iInter_le_mem hs n

theorem partialSups_mem (hC : SetField C) {s : ℕ → Set α} (hs : ∀ n, s n ∈ C) (n : ℕ) :
    partialSups s n ∈ C :=
  hC.to_setRing.partialSups_mem hs n

theorem disjointed_mem (hC : SetField C) {s : ℕ → Set α} (hs : ∀ n, s n ∈ C) (n : ℕ) :
    disjointed s n ∈ C :=
  hC.to_setRing.disjointed_mem hs n

end SetField

end MeasureTheory

