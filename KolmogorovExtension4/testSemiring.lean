/-
  The goal is to avoid indexed things. We have shown: For J : Finset (Set α) and hJ : J ⊆ C, there is K : Finset (Set α) with K ⊆ C and (PairwiseDisjoint K id) such that ⋃₀ J = ⋃₀ K.

  However, we need a bit more (in Content.lean for additivity): For J : Finset (Set α) and hJ : J ⊆ C, there is K : J → Finset (Set α) with ⋃ j ∈ J, K j ⊆ C and (PairwiseDisjoint ⋃ j ∈ J, K j id) such that ⋃₀ K j ⊆ j and ⋃₀ J = ⋃ j ∈ J, ⋃₀ K j.
  Proof should be by Finset induction: If J = {}, the statement is clear.
  If it is proved for J, then we know s \ ⋃₀ J = ⋃₀ K' for some disjoint K'. We then set K j as before for j ∈ J and K s = K'. Then,
  ⋃₀ J ∪ {s} = s ∪ ⋃₀ J = (s \ ⋃₀ J) ⊎ ⋃₀ J = (⋃₀ K s) ⊎ ⋃ j ∈ J, ⋃₀ K j.
  In addition, ⋃₀ K s ⊆ s by construction and ⋃₀ K j ⊆ j by induction hypothesis.

  Using this result, additivity is as follows:
  First, if ⋃₀ J ⊆ s (for disjoint J), then ∑ u ∈ ⋃₀ J, m u ≤ m s since by additivity
  m s = ∑ u ∈ ⋃₀ J, m u + ∑ u ∈ ⋃₀ K, m u ∑ u ∈ ⋃₀ J, m u
  for s \ ⋃₀ J = ⋃₀ K.
  From this, directly,
  m ⋃ J = m ⋃ j ∈ J, ⋃ K j = ∑ j ∈ J, ∑ u in ⋃ K j, m u ≤ ∑ j ∈ J, m j.
-/



import KolmogorovExtension4.AuxLemmas
import Mathlib.MeasureTheory.SetSemiring

open Finset Set MeasureTheory Order

open scoped NNReal Topology ENNReal

namespace MeasureTheory

namespace IsSetSemiring

variable {α : Type*} {C : Set (Set α)} {s t : Set α}

lemma allDiffFinset₀_props (hC : IsSetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C)
  [DecidableEq (Set α)] : ∃ K : Finset (Set α), (↑K ⊆ C) ∧ (PairwiseDisjoint
  (K : Set (Set α)) id) ∧ (⋃₀ (J : Set (Set α))) = (⋃₀ (K : Set (Set α))) := by
  revert hJ
  apply @Finset.cons_induction (Set α) (fun (J : Finset (Set α)) => (↑J ⊆ C) → (∃ K : Finset (Set α), (↑K ⊆ C) ∧ (PairwiseDisjoint (K : Set (Set α)) id) ∧ (⋃₀ J) = (⋃₀ (K : Set (Set α))))) _ _ J
  · intro _
    use ∅
    simp only [coe_empty, Set.empty_subset, pairwiseDisjoint_empty, sUnion_empty, and_self]
  · intros j J hj hJ h
    simp only [coe_cons] at h
    obtain h' := (@Set.insert_subset_iff (Set α) j ↑J C).1 h
    specialize hJ h'.2
    rcases hJ with ⟨K, h1, h2, h3⟩
    let K' := hC.diffFinset₀ h'.1 h'.2
    simp [IsSetSemiring.diffFinset₀] at K'
    obtain hK'1 := hC.diffFinset₀_subset h'.1 h'.2
    obtain hK'2 := hC.pairwiseDisjoint_diffFinset₀ h'.1 h'.2
    obtain hK'3 := hC.diff_sUnion_eq_sUnion_diffFinset₀ h'.1 h'.2
    use K ∪ K'
    constructor
    · simp only [coe_union, Set.union_subset_iff]
      refine ⟨h1, hK'1⟩
    · constructor
      · simp only [coe_union]
        apply Set.PairwiseDisjoint.union h2 hK'2
        intros i hi i' hi' _
        simp only [id_eq]
        obtain h'i : i ⊆ ⋃₀ ↑J := by
          rw [h3]
          exact subset_sUnion_of_subset (↑K) i (fun ⦃a⦄ a => a) hi
        obtain h'i' : i' ⊆ (⋃₀ ↑J)ᶜ := by
          apply le_trans _ (diff_subset_compl j (⋃₀ ↑J))
          rw [hK'3]
          exact subset_sUnion_of_subset (↑K') i' (fun ⦃a⦄ a => a) hi'
        exact Disjoint.mono h'i h'i' (disjoint_compl_right_iff_subset.mpr fun ⦃a⦄ a => a)
      · simp only [cons_eq_insert, coe_insert, sUnion_insert, coe_union]
        rw [← diff_union_self, Set.union_comm, sUnion_union ↑K (K' : Set (Set α)), hK'3, h3]

noncomputable def allDiffFinset₀ (hC : IsSetSemiring C) [DecidableEq (Set α)] (J : Finset (Set α)) (hJ : ↑J ⊆ C) := (allDiffFinset₀_props hC J hJ).choose

lemma props_allDiffFinset₀ [DecidableEq (Set α)] (hC : IsSetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C) : (↑(allDiffFinset₀ hC J hJ) ⊆ C) ∧ (PairwiseDisjoint ((allDiffFinset₀ hC J hJ) : Set (Set α)) id) ∧ (⋃₀ (J : Set (Set α))) = (⋃₀ ((allDiffFinset₀ hC J hJ) : Set (Set α)))
 := by
  simp_rw [allDiffFinset₀]
  apply Exists.choose_spec (allDiffFinset₀_props hC J hJ)

lemma pairwiseDisjoint_allDiffFinset₀ (hC : IsSetSemiring C) [DecidableEq (Set α)] (J : Finset (Set α)) (hJ : ↑J ⊆ C) :
    PairwiseDisjoint ↑(allDiffFinset₀ hC J hJ) (id : Set α → Set α) := (props_allDiffFinset₀ hC J hJ).2.1

lemma allDiffFinset₀_subset (hC : IsSetSemiring C) [DecidableEq (Set α)] (J : Finset (Set α)) (hJ : ↑J ⊆ C) :
    ↑(allDiffFinset₀ hC J hJ) ⊆ C :=
    (props_allDiffFinset₀ hC J hJ).1

lemma sUnion_allDiffFinset₀ (hC : IsSetSemiring C) [DecidableEq (Set α)] (J : Finset (Set α)) (hJ : ↑J ⊆ C) :
    ⋃₀ (allDiffFinset₀ hC J hJ : Set (Set α)) = ⋃₀ J :=
    (props_allDiffFinset₀ hC J hJ).2.2.symm

lemma allDiffFinset₀₀_props (hC : IsSetSemiring C) (J : Finset (Set α)) (hJ : ↑J ⊆ C)
  [DecidableEq (Set α)] : ∃ K : Set α → Finset (Set α), (↑ (J.biUnion K) ⊆ C) ∧ (PairwiseDisjoint (J.biUnion K : Set (Set α)) id) ∧ (∀ j ∈ J, ⋃₀ K j ⊆ j ) ∧ (⋃₀ J = ⋃₀  (J.biUnion K : Set (Set α))) := by
  revert hJ
  apply @Finset.cons_induction (Set α) (fun (J : Finset (Set α)) => (↑J ⊆ C) → (∃ K : Set α → Finset (Set α), (↑ (J.biUnion K) ⊆ C) ∧ (PairwiseDisjoint (J.biUnion K : Set (Set α)) id)  ∧ (∀ j ∈ J, ⋃₀ K j ⊆ j ) ∧ (⋃₀ J = ⋃₀ (J.biUnion K : Set (Set α))))) _ _ J
  · simp only [coe_empty, Set.empty_subset, Finset.biUnion_empty, pairwiseDisjoint_empty,
    Finset.not_mem_empty, sUnion_subset_iff, mem_coe, IsEmpty.forall_iff, implies_true,
    sUnion_empty, and_self, exists_const, imp_self]
  · intro s J hJ hind h1
    rw [cons_eq_insert, coe_insert, Set.insert_subset_iff] at h1
    obtain hind2 := hind h1.2
    clear hind
    let ⟨K, hK⟩ := hind2
    clear hind2
    let K' := hC.diffFinset₀ h1.1 h1.2
    -- let K1 (t : Set α) : Finset (Set α) := match t with
    let K1 := fun (t : Set α) => ite (t == s) K' (K t)
    have ht1 : (if (s == s) = true then K' else K s) = K' := by
      simp only [beq_self_eq_true, ↓reduceIte]
    have ht2 : ∀ x ∈ J, ((if (x == s) = true then K' else K x) : Set (Set α)) = (K x : Set (Set α)) := by
      intro x hx
      simp only [beq_iff_eq, ite_eq_right_iff]
      intro g
      exfalso
      rw [g] at hx
      exact hJ hx
    have ht2' : ∀ x ∈ J, ((if (x == s) = true then K' else K x) ) = (K x) := by
      simp only [beq_iff_eq, ite_eq_right_iff]
      intros t b2 b3
      exfalso
      apply hJ
      rw [← b3]
      exact b2
    have ht3 : ⋃ x ∈ J, (((if (x == s) = true then K' else K x)) : Set (Set α)) = J.biUnion K := by
      simp only [beq_iff_eq, coe_biUnion, mem_coe]
      refine iUnion₂_congr ?_
      simp only [coe_biUnion, mem_coe, iUnion_subset_iff, sUnion_subset_iff, beq_self_eq_true,
        ↓reduceIte, beq_iff_eq, ite_eq_right_iff, coe_inj] at *
      exact ht2
    use K1
    rcases hK with ⟨hK1, hK2, hK3, hK4⟩
    constructor
    · simp only [cons_eq_insert, Finset.biUnion_insert, coe_union, coe_biUnion, mem_coe, Set.union_subset_iff, iUnion_subset_iff, K1, beq_self_eq_true, ↓reduceIte, beq_iff_eq, K1]
      constructor
      · exact hC.diffFinset₀_subset h1.1 h1.2
      · intros i hi
        split
        exact hC.diffFinset₀_subset h1.1 h1.2
        simp only [coe_biUnion, mem_coe, iUnion_subset_iff, K1] at hK1
        simp only [hi, hK1, K1]
    · constructor
      · simp only [cons_eq_insert, Finset.biUnion_insert, coe_union, coe_biUnion, mem_coe, K1, ht1, ht2]
        refine pairwiseDisjoint_union.mpr ?_
        constructor
        · exact hC.pairwiseDisjoint_diffFinset₀ h1.1 h1.2
        · constructor
          · simp_rw [apply_ite]
            rw [ht3]
            exact hK2
          · simp only [mem_coe, mem_iUnion, exists_prop, ne_eq, id_eq,
            forall_exists_index, and_imp, K1]
            intros i hi j x hx h3 h4
            rw [ht2' x hx]  at h3
            -- i ⊆ s \ ⋃₀ J
            -- j ∈ K x ⊆ x ∈ J
            have ki : i ⊆ s \ ⋃₀ J :=
              by
              rw [hC.diff_sUnion_eq_sUnion_diffFinset₀ h1.1 h1.2]
              exact
                subset_sUnion_of_subset (↑(hC.diffFinset₀ h1.1 h1.2)) i (fun ⦃a⦄ a => a) hi
            have hx2 : j ⊆ x := by
              apply le_trans _ (hK3 x hx)
              simp only [Set.le_eq_subset, K1]
              exact subset_sUnion_of_subset (↑(K x)) j (fun ⦃a⦄ a => a) h3
            have kj : j ⊆ ⋃₀ J := by
              apply le_trans hx2
              exact subset_sUnion_of_subset (↑J) x (fun ⦃a⦄ a => a) hx
            apply disjoint_of_subset ki kj
            exact disjoint_sdiff_left

      · constructor
        · simp only [cons_eq_insert, Finset.mem_insert, sUnion_subset_iff, mem_coe,
          forall_eq_or_imp, K1]
          constructor
          · simp only [beq_self_eq_true, ↓reduceIte, K1]
            change ∀ t' ∈ (K' : Set (Set α)), t' ⊆ s
            rw [← sUnion_subset_iff]
            exact hC.sUnion_diffFinset₀_subset h1.1 h1.2
          · intros a ha t ht
            rw [ht2' a ha] at ht
            revert t ht
            change ∀ t ∈ (K a : Set (Set α)), t ⊆ a
            rw [← sUnion_subset_iff]
            exact hK3 a ha
        · simp only [cons_eq_insert, coe_insert, sUnion_insert, Finset.biUnion_insert, coe_union, coe_biUnion, mem_coe, K1, ht1, ht2]
          simp_rw [apply_ite, ht3]
          rw [sUnion_union]
          rw [← hC.diff_sUnion_eq_sUnion_diffFinset₀ h1.1 h1.2, ← hK4]
          simp only [diff_union_self, K1]

example ( i j a b : Set α ) (hi : i ⊆ a) (hj : j ⊆ b) (hd : Disjoint a b) : (Disjoint i j) := by
  exact disjoint_of_subset hi hj hd

-- For J : Finset (Set α) and hJ : J ⊆ C, there is K : J → Finset (Set α) with ⋃ j ∈ J, K j ⊆ C and (PairwiseDisjoint ⋃ j ∈ J, K j id) such that ⋃₀ K j ⊆ j and ⋃₀ J = ⋃ j ∈ J, ⋃₀ K j.
--  If it is proved for J, then we know s \ ⋃₀ J = ⋃₀ K' for some disjoint K'. We then set K j as before for j ∈ J and K s = K'. Then,
--  ⋃₀ J ∪ {s} = s ∪ ⋃₀ J = (s \ ⋃₀ J) ⊎ ⋃₀ J = (⋃₀ K s) ⊎ ⋃ j ∈ J, ⋃₀ K j.
--  In addition, ⋃₀ K s ⊆ s by construction and ⋃₀ K j ⊆ j by induction hypothesis.

example : (if 1 < 2 then 1 else 2) ≤ 3 := by
  simp only [Nat.one_lt_ofNat, ↓reduceIte, Nat.one_le_ofNat]

end IsSetSemiring

namespace IsSetRing

variable {α : Type*} {C : Set (Set α)} {s t : Set α}

theorem iUnion_le_mem (hC : IsSetRing C) {s : ℕ → Set α} (hs : ∀ n, s n ∈ C) (n : ℕ) :
    (⋃ i ≤ n, s i) ∈ C := by
  induction' n with n hn
  · simp only [Nat.zero_eq, le_zero_iff, iUnion_iUnion_eq_left, exists_prop]
    exact hs 0
  rw [Set.biUnion_le_succ]
  exact hC.union_mem hn (hs _)

theorem iInter_le_mem (hC : IsSetRing C) {s : ℕ → Set α} (hs : ∀ n, s n ∈ C) (n : ℕ) :
    (⋂ i ≤ n, s i) ∈ C := by
  induction' n with n hn
  · simp only [Nat.zero_eq, le_zero_iff, iInter_iInter_eq_left, exists_prop]
    exact hs 0
  rw [Set.biInter_le_succ]
  exact hC.inter_mem hn (hs _)

theorem accumulate_mem (hC : IsSetRing C) {s : ℕ → Set α} (hs : ∀ i, s i ∈ C) (n : ℕ) :
    Set.Accumulate s n ∈ C := by
  induction' n with n hn
  · simp only [Set.Accumulate, le_zero_iff, Set.iUnion_iUnion_eq_left, hs 0, Nat.zero_eq,
      nonpos_iff_eq_zero, iUnion_iUnion_eq_left]
  · rw [Set.accumulate_succ]
    exact hC.union_mem hn (hs _)

end IsSetRing

end MeasureTheory
