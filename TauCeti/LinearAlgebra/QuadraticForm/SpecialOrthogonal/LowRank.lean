/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Special orthogonal groups in dimension at most one

A determinant-one automorphism of a space of dimension at most one is the identity. Thus its
special orthogonal group is trivial, even for a degenerate quadratic form and in characteristic
two. This supplies the low-dimensional boundary of spinor-norm image calculations.
-/

public section

namespace QuadraticMap

open TauCeti.QuadraticMap

variable {K V N : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [AddCommMonoid N] [Module K N]

/-- The special orthogonal group of a quadratic map in dimension at most one is trivial.
No nondegeneracy or characteristic assumption is needed. -/
theorem specialOrthogonalGroup_eq_bot_of_finrank_le_one (Q : QuadraticMap K V N)
    (hV : Module.finrank K V ≤ 1) : specialOrthogonalGroup Q = ⊥ := by
  apply eq_bot_iff.mpr
  intro g hg
  rw [Subgroup.mem_bot]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hV with hV | hV
  · let := Module.finrank_zero_iff.mp hV
    exact Subsingleton.elim _ _
  · obtain ⟨c, hc, _⟩ := g.toLinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hV
    have hd : c = 1 := by
      simpa [LinearEquiv.coe_det, hc, LinearMap.det_smul, hV] using
        congrArg Units.val (mem_specialOrthogonalGroup_iff.mp hg).2
    apply LinearEquiv.toLinearMap_injective
    simpa [hd] using hc

end QuadraticMap
