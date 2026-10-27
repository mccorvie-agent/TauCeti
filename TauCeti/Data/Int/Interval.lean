/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Algebra.Order.Interval.Finset.Basic
public import Mathlib.Data.Int.Interval
import TauCeti.Data.Finset.Basic

/-!
# Translation boundaries of integer intervals

Translating a finite integer interval by `k` changes at most `2 * k.natAbs` points,
independently of the endpoints. This uniform boundary bound is useful for averaging
on intervals whose lengths tend to infinity. Empty intervals are allowed.
-/

public section

open Finset
open scoped Pointwise symmDiff

namespace Int

/-- Translating an integer interval by `k` changes at most `2 * k.natAbs` points. -/
theorem card_vadd_Icc_symmDiff_le (a b k : ℤ) :
    #((k +ᵥ Icc a b) ∆ Icc a b) ≤ 2 * k.natAbs := by
  have hi : Icc (k + a) (k + b) ∩ Icc a b = Icc (max (k + a) a) (min (k + b) b) := by
    ext x
    simp only [mem_inter, mem_Icc, max_le_iff, le_min_iff]
    tauto
  have h := card_symmDiff_add_two_mul_card_inter (Icc (k + a) (k + b)) (Icc a b)
  simp only [vadd_finset_def, vadd_eq_add, image_add_left_Icc]
  rw [hi, card_Icc, card_Icc, card_Icc] at h
  have hk := natCast_natAbs k
  omega

end Int
