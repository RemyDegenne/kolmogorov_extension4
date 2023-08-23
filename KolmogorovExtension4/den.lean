import Mathlib.Logic.Denumerable


open Set Function

variable {α β : Type*} 

namespace Set


lemma rangeFactorization_bijective_of_injective {f : α → β} (hf : Function.Injective f) : Function.Bijective (rangeFactorization f) := by
  refine' ⟨_, surjective_onto_range⟩
  intros x y h1
  have h2 : (rangeFactorization f x : β) = (rangeFactorization f y : β) := by rw [h1]
  simp only [rangeFactorization_coe] at h2 
  apply hf h2

end Set

namespace Equiv

lemma of_range_injective {f : α → β} (hf : Function.Injective f) : α ≃ (range f) := by
  exact ofBijective (rangeFactorization f) (rangeFactorization_bijective_of_injective hf)

end Equiv


namespace Denumerable

lemma l1 (s : Set α) (hs : Denumerable s) : (s ≃ (range (fun i => (Denumerable.ofNat s i)))) := by
  let f := fun (i : ℕ) => (Denumerable.ofNat s i)
  change s ≃ range f
  haveI hr : ℕ ≃ (range f)  :=  by
    have hf : Injective f :=  by
      refine HasLeftInverse.injective ?_
      use Encodable.encode
      simp only [Denumerable.decode_eq_ofNat, Option.some.injEq]
      exact Denumerable.encode_ofNat
    refine' Equiv.of_range_injective hf
  obtain hD : Denumerable (range f) := Denumerable.mk' (id hr.symm)
  apply Denumerable.equiv₂

lemma l2 (hs : Denumerable α) : (range (fun i => (Denumerable.ofNat α i))) = univ := by
  let f := fun (i : ℕ) => (Denumerable.ofNat α i)
  change (range f) = univ
  have hfS : Surjective f := by
    intro x
    use Encodable.encode x
    simp only [decode_eq_ofNat, Option.some.injEq, ofNat_encode]
  rw [← Set.image_univ_of_surjective hfS]
  simp only [decode_eq_ofNat, Option.some.injEq, image_univ]
  

lemma l3 (s : Set α) (hs : Denumerable s) : ((range (fun i => (Denumerable.ofNat s i)))) = univ := by
  apply l2

lemma l3a (s : Set β) (f : α → s) : ((range (fun x => f x)) : Set β) = Subtype.val '' (range f) := by
  ext y
  refine' ⟨fun h => _, fun h => _⟩
  · simp only [mem_image, mem_range, exists_exists_eq_and]
    simp only [mem_range] at h 
    cases' h with z hz
    use z
  · simp only [mem_range]
    simp only [mem_image, mem_range, exists_exists_eq_and] at h 
    cases' h with z hz
    use z

lemma l4 (s : Set α) (hs : Denumerable s) : ((range (fun i => (Denumerable.ofNat s i))) : Set α) = s := by
  conv_rhs
  => conv => {rw [← Subtype.coe_image_univ s]}
  have h : ((range (fun i => (Denumerable.ofNat s i))) : Set α) = Subtype.val '' (range (fun i => (Denumerable.ofNat s i))) := by
    refine' l3a s (fun i => (Denumerable.ofNat s i))
  rw [h]
  apply congrArg (image Subtype.val)
  exact l3 s hs

end Denumerable





