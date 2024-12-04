def boxIJ (I : Finset ι) (J : Finset ι) (t : (i : I) → Set (α i)) : Set ((i : I) → α i) := box t (Finset_Subtype_of_subset I J)



-- boxes

lemma embedding_inj {ι : Type} (I : Finset ι) : Function.Injective (fun (i : I) => (i.val : ι)) := by
  intros i j hij
  simp only at hij
  exact SetCoe.ext hij
  
lemma embedding_injOn {ι : Type} (I J : Finset ι) (hIJ : J ⊆ I) : Set.InjOn (fun (i : I) => (i.val : ι)) ((fun (i : I) => (i.val : ι))⁻¹' J) := Function.Injective.injOn (embedding_inj I) ((fun (i : I) => (i.val : ι))⁻¹' J)

noncomputable def Finset_Subtype_of_subset (I J : Finset ι) : Finset I := Finset.preimage J (fun (i : I) => (i.val : ι)) (Function.Injective.injOn (embedding_inj I) ((fun (i : I) => (i.val : ι))⁻¹' J))

@[simp]
lemma Finset_Subtype_of_univ (I : Finset ι) : (Finset_Subtype_of_subset I I : Set I) = univ := by
  ext x
  constructor
  · intro _
    simp only [mem_univ]
  · intro _
    simp only [Finset_Subtype_of_subset, Finset.coe_preimage, mem_preimage, Finset.mem_coe, Finset.coe_mem]



def J_as_Subtype (I J : Set ι) (hJI : J ⊆ I) : Set I := {x : I | x.val ∈ J}
lemma mem_boxI' {I : Set ι} (t : (i : ι) → Set (α i)) (y : (i : I) → α i) : y ∈ (boxI I t) ↔ (∀ i : I, (y i  ∈ t i)) := by
  obtain h := Classical.choose_spec (exists_sub_pi I y)
  rw [← h]
  simp [mem_boxI]
  sorry





-- noch zu verwenden:



theorem generateFrom_boxesI (I : Finset ι) [∀ (i : I), MeasurableSpace (α i)] : MeasurableSpace.pi = MeasurableSpace.generateFrom (boxesI I : Set (Set ((i : I) → α i))) := by  
  exact Eq.symm generateFrom_pi

lemma box_measurable (I : Finset ι) [∀ (i : I), MeasurableSpace (α i)] {s : Set ((i : I) → α i)} (hs : s ∈ boxesI I) : MeasurableSet s := by
   sorry


lemma l1 {I J : Finset ι} (hJI : J ⊆ I) [∀ (i : I), MeasurableSpace (α i)] (s : Set ((i : J) → α i)) (hs : s ∈ (boxesI J)) : (∃ (t : (i : J) → Set (α i)), s = boxIJ J J t) := by
  apply (mem_boxesI s).1 hs


theorem proj' (P : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (P i)] (J I : Finset ι) (hJI : J ⊆ I) : Measure.subset_pi P J = Measure.map (Function.proj hJI) (Measure.subset_pi P I) := by
  apply MeasureTheory.ext_of_generate_finite (boxesI J) (generateFrom_boxesI J) (isPiSystem_boxesI J)
  · intros s hs
    simp only [Function.proj_eval]
    --have hmea : Measurable pro := by
    --  exact measurable_proj₂' I J hJI
    --have h3 : MeasurableSet s := by 
    --  apply box_measurable J hs
    --have h2 : (Measure.map (fun (f : (i : I) → α i) (i : J) => f ⟨i, hJI i.prop⟩) (Measure.subset_pi P I)) s = (Measure.subset_pi P I) ((fun (f : (i : I) → α i) (i : J) => f ⟨i, hJI i.prop⟩)⁻¹' s) := by
    --  refine Measure.map_apply hmea h3
    rw [Measure.map_apply (measurable_proj₂' I J hJI) (box_measurable J hs)]
    obtain hs'' := l1 hJI s 

--    have hs'' : (∃ (t : (i : J) → Set (α i)), s = boxIJ J t) := by 
--      apply (mem_boxesI s).1 hs
      
    have hs' : (∃ (t : (i : I) → Set (α i)), s = (boxIJ I I)) := by sorry


    -- rw [MeasureTheory.Measure.mapₗ_apply_of_measurable pro hmea (Measure.subset_pi P I) s]
    
    sorry
  · sorry

theorem product_isProjective (P : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (P i)] :
    IsProjectiveMeasureFamily (fun J : Finset ι => Measure.subset_pi P J) := by
  simp [IsProjectiveMeasureFamily, IsProjective]
  intros I J hJI
  exact proj' P J I hJI 

noncomputable def independentFamily [∀ i, PseudoEMetricSpace (α i)]
    [∀ i, BorelSpace (α i)] [∀ i, TopologicalSpace.SecondCountableTopology (α i)]
    [∀ i, CompleteSpace (α i)] [Nonempty (∀ i, α i)] (P : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (P i)] : Measure (∀ i, α i) := projectiveLimitWithWeakestHypotheses (fun J : Finset ι => Measure.subset_pi P J) (product_isProjective P)

end MeasureTheory


-- def boxIJ' {I J : Finset ι} (hJI : J ⊆ I) (t : (i : I) → Set (α i)) : Set ((i : I) → α i) := box t (Finset.preimage J (Set.inclusion hJI) (Function.Injective.injOn (Set.inclusion_injective hJI) J))

-- lemma proj (P : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (P i)] (J I : Finset ι) (hJI : J ⊆ I) (t : (i : I) → Set (α i)) : (Measure.subset_pi P J) (univ.pi (fun (i : J) => t ⟨i.val, hJI i.prop⟩)) = (Measure.subset_pi P I) (boxIJ J t) := by
--   sorry

-- (Measure.subset_pi P J) (univ.pi (fun (i : J) => t ⟨i.val, hJI i.prop⟩)) = (Measure.subset_pi P J) (boxIJ J t)

/- 
lemma proj_box (J I : Finset ι) (hJI : J ⊆ I) (t : (i : I) → Set (α i)) : (Function.proj I J hJI) '' (boxIJ J t) = boxIJ J (fun (i : J) => t ⟨i.val, hJI i.prop⟩) := by
  simp only [Function.proj, boxIJ, box, Finset_Subtype_of_subset, Finset.coe_preimage]
  ext pi
  constructor
  · intro h
    simp only [mem_pi, mem_preimage, Finset.mem_coe, Finset.coe_mem, forall_true_left, Subtype.forall]
    intros a ha
    simp only [mem_image, mem_pi, mem_preimage, Finset.mem_coe, Subtype.forall] at h 
    rcases h with ⟨x1, ⟨h1, h2⟩⟩
    rw [← h2]
    simp only
    specialize h1 a (hJI ha) ha
    simp only [h1]
  · intro h
    simp only [mem_image, mem_pi, mem_preimage, Finset.mem_coe, Subtype.forall]
    simp only [mem_pi, mem_preimage, Finset.mem_coe, Finset.coe_mem, forall_true_left, Subtype.forall] at h 
    sorry
-/


-- s ∈ boxesI J ↔ ∃ (t : (i : J) → Set (α i))), s = bixIJ J t




  







  -- simp_rw [apply_dite, Finset.prod_dite]
  simp only [Finset.univ_eq_attach, measure_univ, Finset.prod_const_one, mul_one]
  
--  simp_rw [← Finset.univ_eq_attach]
  let f := (fun i => (P i) (t i)) 
  let JsI := { x : I // x ∈ Finset.filter (fun x => ↑x ∈ J) Finset.univ }
  have h1 : (∏ i in Finset.attach J, (P (i : ι)) (t (i : ι))) = (∏ i in Finset.attach J, (f i)) := by
    rfl
  have h3 : (∏ i in Finset.attach J, (f i)) = (∏ i in J, (f i)) := by
    exact l6 J f
  have h2 : ∏ i in Finset.attach (Finset.filter (fun x => ↑x ∈ J) (Finset.attach I)), (P (i : ι)) (t (i : ι)) = ∏ i in Finset.attach (Finset.filter (fun x => ↑x ∈ J) (Finset.attach I)), (f i) := by
    rfl
  have h3 : (∏ i in Finset.attach J, (f i)) = (∏ i in J, (f i)) := by
    exact l6 J f
  have h4 : ∏ i in Finset.attach (Finset.filter (fun x => ↑x ∈ J) (Finset.attach I)), (f i) = ∏ i in (Finset.filter (fun x => ↑x ∈ J) (Finset.attach I)), (f i) := by
    apply l7
  rw [h1, h2, h4, Finset.prod_filter]
  



  
  -- refine Finset.prod_subtype


  have h : { x // x ∈ Finset.filter (fun x => ↑x ∈ J) (Finset.univ : Finset I)} = { x : I // x.val ∈ J } := by
    simp only [Finset.univ_eq_attach, Finset.mem_attach, forall_true_left, Subtype.forall, Finset.mem_filter, true_and]
  simp
  rw [← Finset.univ_eq_attach]  
  
  -- have h1 : Finset.attach (Finset.filter (fun x => ↑x ∈ J) (Finset.attach I)) = Finset.attach J := by
  -- simp [Fintype.prod_equiv]
  -- simp_rw [h]


  
  -- refine Finset.prod_congr h
  

  sorry
set_option maxHeartbeats 0



example  (f : ι → ι) (c : Prop) [Decidable c] (y z : ι) : (f (ite c y z )) = (ite c (f y) (f z)) := by
  exact apply_ite f c y z

set_option maxHeartbeats 0
example (J : Finset ι) (f : ι → ℝ) : ∏ x : J, f x = ∏ x in J, f x := by
  simp only [Finset.univ_eq_attach]
  exact Finset.prod_attach

lemma l5  [DecidableEq ι] (J I : Finset ι) : (Finset.filter (fun (x : I) => x.val ∈ J) Finset.univ : Set I) = (fun (x : I) => x.val ∈ J) := by
  simp only [Finset.univ_eq_attach, Finset.mem_attach, forall_true_left, Subtype.forall, Finset.coe_filter, true_and]
  rfl
#check Finset.attach
#check Finset.filter


example (I : Finset ι) (f : ι → ℝ≥0∞) : ∏ i : { x // x ∈ I }, f i = ∏ i in I, f i:= by
  exact Finset.prod_coe_sort I f

lemma l6 (J : Finset ι) (f : ι → ℝ≥0∞) : ∏ i  in Finset.attach J, f i = ∏ i in J, f i:= by
  exact Finset.prod_attach

lemma l7 (I J : Finset ι) [DecidableEq ι] (f : ι → ℝ≥0∞) : ∏ i in Finset.attach (Finset.filter (fun x => ↑x ∈ J) (Finset.attach I)), (f i)  = ∏ i in (Finset.filter (fun x => ↑x ∈ J) (Finset.attach I)), (f i) := by
  let J' := (Finset.filter (fun x => ↑x ∈ J) (Finset.attach I))
  change ∏ i in Finset.attach J', (f i)  = ∏ i in J', (f i)
  apply l6 J' (fun (i : I) => f i)
  
lemma l8 (I J : Finset ι) (hJI : J ⊆ I) [DecidableEq ι] (f : ι → ℝ) : ∏ i in (Finset.filter (fun x => ↑x ∈ J) (Finset.attach I)), (f i) = ∏ i in Finset.attach (Finset.filter (fun x => x ∈ J) I), (f i):= by
  rw [Finset.prod_filter]
  set s := (Finset.filter (fun x => x ∈ J) I)
  have hs : s = (Finset.filter (fun x => x ∈ J) (univ : Set ι)) := by
    sorry  

  let p := (fun (i : ι) => (i ∈ J))
  have h : Finset.attach (Finset.filter (fun x => ↑x ∈ J) (Finset.attach I)) = Finset.attach J := by
    sorry
  

  refine @Finset.prod_subtype_of_mem ℝ ι s _ f (fun (i : ι) => (i ∈ J)) _ ()


  apply?
  sorry


example (I : Finset ι) (f : ι → ℝ) : (∏ x : I, f x) = (∏ x in I, f x) := by
  exact Finset.prod_coe_sort I f 
