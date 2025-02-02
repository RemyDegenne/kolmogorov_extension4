/-
Copyright (c) 2025 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
import KolmogorovExtension4.AuxLemmas
import Mathlib.MeasureTheory.SetSemiring
/-
  ## Main results

  * `allDiffFinset₀'_props`: In a semiring, write a union of elements of the semiring as a disjoint union of elements of the semiring.
-/

open Finset Set MeasureTheory Order

open scoped NNReal Topology ENNReal

namespace MeasureTheory

namespace IsSetSemiring

-- Goes in SetSemiring.lean

variable {α : Type*} {C : Set (Set α)} {s t : Set α}
    {J : Finset (Set α)}

end IsSetSemiring

end MeasureTheory

-- goes to Mathlib.Order.CompleteLattice, line 1652

variable [CompleteLattice α]

namespace MeasureTheory

namespace IsSetSemiring

variable {α : Type*} {C : Set (Set α)} {s t : Set α}
    {J : Finset (Set α)}

/- In a `hC : IsSetSemiring C`, for a `J : Finset (Set α)` with `J ⊆ C`, there is for every `x in J` some `K x ⊆ C` finite, such that
    * `⋃ x ∈ J, K x` are pairwise disjoint and do not contan ∅,
    * `⋃ s ∈ K x, s ⊆ x`,
    * `⋃ x ∈ J, x = ⋃ x ∈ J, ⋃ s ∈ K x, s`.
-/
set_option trace.split.failure true


variable [DecidableEq (Set α)]

end IsSetSemiring



namespace IsSetRing

variable {α : Type*} {C : Set (Set α)} {s t : Set α}

end IsSetRing

end MeasureTheory
