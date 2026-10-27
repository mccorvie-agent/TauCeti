/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Int.Interval
public import TauCeti.GroupTheory.Amenable.Average

/-!
# Integer intervals are Følner

The intervals `{0, …, n}` have cardinality `n + 1`, while translation by `k` changes
at most `2 * |k|` points. Consequently their boundary-to-volume ratios tend to zero.
We express this both as a real cardinality limit and using Mathlib's `IsAddFoelner`
for counting measure. Transporting these intervals to `Multiplicative ℤ` and applying
the finite-average criterion gives an invariant mean, hence amenability of the integers.

## References

* A. Garrido, *An introduction to amenable groups*, Example 3.5.
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Example G.5.4.
-/

public section

open Filter Finset MeasureTheory
open scoped Pointwise symmDiff Topology

namespace Int

/-- For each fixed integer translation, the boundary-to-volume ratio of `{0, …, n}`
tends to zero. -/
theorem tendsto_card_vadd_Icc_symmDiff_div_card (k : ℤ) :
    Tendsto (fun n : ℕ =>
      (#((k +ᵥ Icc (0 : ℤ) n) ∆ Icc (0 : ℤ) n) : ℝ) / #(Icc (0 : ℤ) n))
      atTop (𝓝 0) := by
  have hb : Tendsto (fun n : ℕ => (2 * k.natAbs : ℝ) / (n + 1)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 * k.natAbs : ℝ)
  refine squeeze_zero (fun n => by positivity) (fun n => ?_) hb
  have h := card_vadd_Icc_symmDiff_le 0 n k
  have hc : #(Icc (0 : ℤ) n) = n + 1 := by simp [card_Icc]
  simp only [hc, Nat.cast_add, Nat.cast_one]
  exact div_le_div_of_nonneg_right (by exact_mod_cast h) (by positivity)

end Int

namespace TauCeti

/-- The intervals `{0, …, n}` form an additive Følner sequence for counting measure on `ℤ`. -/
theorem isAddFoelner_int_Icc :
    IsAddFoelner ℤ Measure.count atTop (fun n : ℕ => (Icc (0 : ℤ) n : Set ℤ)) where
  eventually_measurableSet := Eventually.of_forall fun n => (Icc (0 : ℤ) n).measurableSet
  eventually_meas_ne_zero := Eventually.of_forall fun n => by
    rw [Measure.count_apply_finset, Int.card_Icc]
    simp
  eventually_meas_ne_top := Eventually.of_forall fun n => by
    rw [Measure.count_apply_finset]
    simp
  tendsto_meas_vadd_symmDiff k := by
    have hp (n : ℕ) : (0 : ℝ) < #(Icc (0 : ℤ) n) := by
      exact_mod_cast card_pos.2 (nonempty_Icc.2 (Int.natCast_nonneg n))
    have h := ENNReal.tendsto_ofReal (Int.tendsto_card_vadd_Icc_symmDiff_div_card k)
    simp_rw [ENNReal.ofReal_div_of_pos (hp _), ENNReal.ofReal_natCast] at h
    simpa only [Function.comp_def, ENNReal.ofReal_zero, ← coe_vadd_finset,
      ← coe_symmDiff, Measure.count_apply_finset] using h

/-- The integers, written multiplicatively, are amenable for any group topology. -/
instance Amenable.multiplicative_int [TopologicalSpace (Multiplicative ℤ)]
    [IsTopologicalGroup (Multiplicative ℤ)] : Amenable (Multiplicative ℤ) := by
  let F : ℕ → Finset (Multiplicative ℤ) := fun n =>
    (Icc (0 : ℤ) n).image Multiplicative.ofAdd
  refine Amenable.of_tendsto_card_smul_symmDiff_div_card (F := F) (l := atTop)
    (fun n => (nonempty_Icc.2 (Int.natCast_nonneg n)).image _) fun k => ?_
  have hF (n : ℕ) : (k • F n) ∆ F n =
      (((k.toAdd +ᵥ Icc (0 : ℤ) n) ∆ Icc (0 : ℤ) n).image Multiplicative.ofAdd) := by
    rw [image_symmDiff _ _ Multiplicative.ofAdd.injective]
    congr 1
    simp only [F, smul_finset_def, vadd_finset_def, image_image, Function.comp_def,
      smul_eq_mul, vadd_eq_add]
    simp [ofAdd_add]
  simpa only [hF, F, card_image_of_injective _ Multiplicative.ofAdd.injective] using
    Int.tendsto_card_vadd_Icc_symmDiff_div_card k.toAdd

end TauCeti
