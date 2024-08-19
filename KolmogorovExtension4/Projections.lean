/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import KolmogorovExtension4.Annexe

open MeasureTheory

variable {ι : Type*} {X : ι → Type*}

/-- Given a dependent function, restrict it to a function of variables in `s`. -/
def proj (s : Set ι) (x : (i : ι) → X i) (i : s) : X i := x i

@[simp]
lemma proj_def (s : Set ι) : @proj ι X s = fun x i ↦ x i := rfl

/-- Given a dependent function of variables in `t`, restrict it to a function of variables in `s`
when `s ⊆ t`. -/
def projSubset {s t : Set ι} (hst : s ⊆ t) (x : (i : t) → X i) (i : s) : X i := x ⟨i.1, hst i.2⟩

@[simp]
lemma projSubset_def {s t : Set ι} (hst : s ⊆ t) :
    projSubset (X := X) hst = fun x i ↦ x ⟨i.1, hst i.2⟩ := rfl

theorem projSubset_comp_proj {s t : Set ι} (hst : s ⊆ t) :
    (projSubset (X := X) hst) ∘ (proj t) = proj s := rfl

theorem projSubset_comp_projSubset {s t u : Set ι} (hst : s ⊆ t) (htu : t ⊆ u) :
    (projSubset (X := X) hst) ∘ (projSubset htu) = projSubset (hst.trans htu) := rfl

/-- Given a dependent function, restrict it to a function of variables in `s`, `Finset` version. -/
def fproj (s : Finset ι) (x : (i : ι) → X i) (i : s) : X i := x i

@[simp]
lemma fproj_def (s : Finset ι) : @fproj ι X s = fun x i ↦ x i := rfl

/-- Given a dependent function of variables in `t`, restrict it to a function of variables in `s`
when `s ⊆ t`, `Finset` version. -/
def fprojSubset {s t : Finset ι} (hst : s ⊆ t) (x : (i : t) → X i) (i : s) : X i :=
  x ⟨i.1, hst i.2⟩

@[simp]
lemma fprojSubset_def {s t : Finset ι} (hst : s ⊆ t) :
    fprojSubset (X := X) hst = fun x i ↦ x ⟨i.1, hst i.2⟩ := rfl

theorem fprojSubset_comp_fproj {s t : Finset ι} (hst : s ⊆ t) :
    (fprojSubset (X := X) hst) ∘ (fproj t) = fproj s := rfl

theorem fprojSubset_comp_fprojSubset {s t u : Finset ι} (hst : s ⊆ t) (htu : t ⊆ u) :
    (fprojSubset (X := X) hst) ∘ (fprojSubset htu) = fprojSubset (hst.trans htu) := rfl

variable [∀ i, MeasurableSpace (X i)]

theorem measurable_proj (s : Set ι) : Measurable (@proj ι X s) :=
  measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

theorem measurable_projSubset {s t : Set ι} (hst : s ⊆ t) :
    Measurable (projSubset (X := X) hst) :=
  measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

theorem measurable_fproj (s : Finset ι) : Measurable (@fproj ι X s) :=
  measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

theorem measurable_fprojSubset {s t : Finset ι} (hst : s ⊆ t) :
    Measurable (fprojSubset (X := X) hst) :=
  measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

variable [∀ i, TopologicalSpace (X i)]

theorem continuous_proj (s : Set ι) : Continuous (@proj ι X s) :=
  continuous_pi fun _ ↦ continuous_apply _

theorem continuous_projSubset {s t : Set ι} (hst : s ⊆ t) :
    Continuous (projSubset (X := X) hst) :=
  continuous_pi fun _ ↦ continuous_apply _

theorem continuous_fproj (s : Finset ι) : Continuous (@fproj ι X s) :=
  continuous_pi fun _ ↦ continuous_apply _

theorem continuous_fprojSubset {s t : Finset ι} (hst : s ⊆ t) :
    Continuous (fprojSubset (X := X) hst) :=
  continuous_pi fun _ ↦ continuous_apply _

variable {X : ℕ → Type*}

/-- Given a dependent function indexed by `ℕ`, specialize it as a function on `Iic n`. -/
abbrev projNat (n : ℕ) := @proj ℕ X (Set.Iic n)

/-- Given a dependent function indexed by `Iic n`, specialize it as a function on `Iic m` when
`m ≤ n`. -/
abbrev projNat_le {m n : ℕ} (hmn : m ≤ n) := projSubset (X := X) (Set.Iic_subset_Iic.2 hmn)

/-- Given a dependent function indexed by `ℕ`, specialize it as a function on `Iic n`,
`Finset` version. -/
abbrev fprojNat (n : ℕ) := @fproj ℕ X (Finset.Iic n)

/-- Given a dependent function indexed by `Iic n`, specialize it as a function on `Iic m` when
`m ≤ n`, `Finset` version. -/
abbrev fprojNat_le {m n : ℕ} (hmn : m ≤ n) := fprojSubset (X := X) (Finset.Iic_subset_Iic.2 hmn)

variable [∀ n, MeasurableSpace (X n)]

theorem measurable_projNat (n : ℕ) : Measurable (@projNat X n) := measurable_proj _

theorem measurable_projNat_le {m n : ℕ} (hmn : m ≤ n) : Measurable (projNat_le (X := X) hmn) :=
  measurable_projSubset _

theorem measurable_fprojNat (n : ℕ) : Measurable (@fprojNat X n) := measurable_fproj _

theorem measurable_fprojNat_le {m n : ℕ} (hmn : m ≤ n) : Measurable (fprojNat_le (X := X) hmn) :=
  measurable_fprojSubset _

variable [∀ n, TopologicalSpace (X n)]

theorem continuous_projNat (n : ℕ) : Continuous (@projNat X n) := continuous_proj _

theorem continuous_projNat_le {m n : ℕ} (hmn : m ≤ n) : Continuous (projNat_le (X := X) hmn) :=
  continuous_projSubset _

theorem continuous_fprojNat (n : ℕ) : Continuous (@fprojNat X n) := continuous_fproj _

theorem continuous_fprojNat_le {m n : ℕ} (hmn : m ≤ n) : Continuous (fprojNat_le (X := X) hmn) :=
  continuous_fprojSubset _
