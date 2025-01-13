revert hJ
  apply @Finset.cons_induction (Set α) (fun (J : Finset (Set α)) => (↑J ⊆ C) → ∃ (K : Set α → Finset (Set α)) (hK : (J.toSet).PairwiseDisjoint K), ((disjiUnion J K hK).toSet ⊆ C) ∧
    (PairwiseDisjoint (disjiUnion J K hK).toSet id) ∧ (∀ j ∈ J, ⋃₀ K j ⊆ j ) ∧
    ((⋃₀ J.toSet) = ⋃₀ (disjiUnion J K hK).toSet)) _ _ J
  · simp only [coe_empty, Set.empty_subset, disjiUnion_eq_biUnion, Finset.biUnion_empty,
    pairwiseDisjoint_empty, Finset.not_mem_empty, sUnion_subset_iff, mem_coe, IsEmpty.forall_iff,
    implies_true, sUnion_empty, and_self, exists_const, imp_self]
  · intro s J hJ hind h1
    rw [cons_eq_insert, coe_insert, Set.insert_subset_iff] at h1
    obtain ⟨K, hK0, ⟨hK1, hK2, hK3, hK4⟩⟩ := hind h1.2
    clear hind
    let K' := hC.diffFinset₀ h1.1 h1.2
    let K1 := fun (t : Set α) => ite (t = s) K' (K t)
    use K1
    simp only [cons_eq_insert, disjiUnion_eq_biUnion, Finset.biUnion_insert, coe_union, coe_biUnion,
      mem_coe, Set.union_subset_iff, iUnion_subset_iff, Finset.mem_insert, sUnion_subset_iff,
      forall_eq_or_imp, coe_insert, sUnion_insert, exists_and_left, exists_prop]
    -- two simplification rules for induction hypothesis
    have ht1 : ∀ x ∈ J, ((if x = s then K'.toSet else (K x).toSet) = (K x).toSet) := by
      simp only [beq_iff_eq, ite_eq_right_iff]
      exact fun x hx g => False.elim (hJ (g ▸ hx))
    have ht2 : (⋃ x ∈ J, if x = s then K'.toSet else (K x).toSet) = ⋃ x ∈ J, (K x).toSet := by
      apply iUnion₂_congr
      intros x hx
      exact if_neg (ne_of_mem_of_not_mem hx hJ)

    refine ⟨⟨?_,?_⟩, ?_, ?_, ?_, ?_⟩
    · simp only [↓reduceIte, K1, apply_ite]
      refine hC.diffFinset₀_subset h1.1 h1.2
    · intros i hi

      split
      · exact hC.diffFinset₀_subset h1.1 h1.2
      · exact hK1 i hi
    · refine pairwiseDisjoint_union.mpr ?_
      refine ⟨?_, ?_, ?_⟩
      · exact hC.pairwiseDisjoint_diffFinset₀ h1.1 h1.2
      · rw [ht2]
        exact hK2
      · simp only [↓reduceIte, mem_coe, mem_iUnion, exists_prop, ne_eq, id_eq, forall_exists_index,
        and_imp, K1]
        intros i hi j x hx h3 h4
        rw [ht1 x hx]  at h3
        -- We show i ⊆ s \ ⋃₀ J
        have ki : i ⊆ s \ ⋃₀ J :=
          by
          rw [hC.diff_sUnion_eq_sUnion_diffFinset₀ h1.1 h1.2]
          exact
            subset_sUnion_of_subset (↑(hC.diffFinset₀ h1.1 h1.2)) i (fun ⦃a⦄ a => a) hi
        -- We show j ∈ K x ⊆ x ∈ J
        have hx2 : j ⊆ x := by
          apply le_trans (by rfl) (hK3 x hx j h3)
        have kj : j ⊆ ⋃₀ J := by
          apply le_trans hx2
          exact subset_sUnion_of_subset (↑J) x (fun ⦃a⦄ a => a) hx

        apply disjoint_of_subset ki kj
        exact disjoint_sdiff_left

    · simp only [↓reduceIte, mem_coe, K1, K']
      constructor
      · exact hC.sUnion_diffFinset₀_subset h1.1 h1.2
      · intros a ha
        rw [if_neg (ne_of_mem_of_not_mem ha hJ), sUnion_subset_iff]
        exact hK3 a ha
    · simp only [↓reduceIte, K1, ht2, sUnion_union]
      rw [← hC.diff_sUnion_eq_sUnion_diffFinset₀ h1.1 h1.2, ← hK4]
      simp only [diff_union_self, K1]
example (s : Set (Set α)) (hs : s.PairwiseDisjoint id) (x y : Set α) (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) : Disjoint x y := by
  exact hs hx hy hxy

lemma l1 {J : Finset (Set α)} {K : Set α → Finset (Set α)} {x : Set α} {j : Set α} (hK : (J.toSet).PairwiseDisjoint K) (hj : j ∈ J) (hx : x ∈ K j) : x ∈ (disjiUnion J K hK).toSet := by
  simp only [disjiUnion_eq_biUnion, coe_biUnion, mem_coe, mem_iUnion, exists_prop]
  use j

example (J : Finset (Set α)) (K : Set α → Finset (Set α)) (hK : (J.toSet).PairwiseDisjoint K) (hs : PairwiseDisjoint (disjiUnion J K hK).toSet id) (x y : Set α) (hx : x ∈ (disjiUnion J K hK).toSet) (hy : y ∈ (disjiUnion J K hK).toSet) (hxy : x ≠ y) : Disjoint x y := by
  exact hs hx hy hxy

example (J : Finset (Set α)) (K : Set α → Finset (Set α)) (hK : PairwiseDisjoint J.toSet K) (hs : PairwiseDisjoint (disjiUnion J K hK).toSet id) (x y : Set α) (i j : Set α) (hi : i ∈ J.toSet) (hj : j ∈ J.toSet) (hij : i ≠ j) (hx : x ∈ K i) (hy : y ∈ K j) : Disjoint x y := by
  apply hs (l1 hK hi hx) (l1 hK hj hy)
  intro h
  apply hij
  rw [h] at hx
  exact PairwiseDisjoint.elim_finset hK hi hj y hx hy
