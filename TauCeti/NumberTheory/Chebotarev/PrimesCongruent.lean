/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.Crossing.CompositumFrobenius
public import TauCeti.NumberTheory.NumberField.Cyclotomic.Galois
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal

/-!
# Cyclotomic Frobenius fibres and arithmetic progressions

Away from the cyclotomic level, the fibre of an automorphism is the set of primes whose norm
reduces to its cyclotomic character. This identifies the arithmetic Frobenius convention with
arithmetic progressions: the residue is the character itself, not its inverse.

For a cyclotomic extension of `ℚ` of nonzero level `n` with `n % 4 ≠ 2`, the identification
holds at every prime: primes dividing the level ramify and their residues are not units.
The restriction excludes levels twice an odd number, where `2` is unramified. In particular,
the four Frobenius fibres of `ℚ(ζ₅)` are precisely the four invertible residue classes modulo five.

## References

* L. Washington, *Introduction to Cyclotomic Fields*, Chapter 2.
* The Frobenius computation is the existing
  `mem_frobeniusPrimeSet_mk_iff_restrictNormal_autToPow`, specialized to a trivial lower extension.
-/

public section

open NumberField IsDedekindDomain
open IsCyclotomicExtension

namespace NumberField.Chebotarev

variable (F : Type*) [Field F] [NumberField F] (n : ℕ) [NeZero n]
  [IsCyclotomicExtension {n} ℚ F]

/-- Every prime dividing a cyclotomic level not congruent to two modulo four ramifies. -/
theorem mem_ramifiedPrimes_of_natCast_mem (hn : n % 4 ≠ 2)
    {𝔭 : HeightOneSpectrum (𝓞 ℚ)} (hm : (n : 𝓞 ℚ) ∈ 𝔭.asIdeal) :
    𝔭 ∈ ramifiedPrimes ℚ F := by
  let p := Ideal.absNorm 𝔭.asIdeal
  have hp : p.Prime := by
    simpa [p, Rat.HeightOneSpectrum.absNorm_asIdeal] using
      Rat.HeightOneSpectrum.prime_natGenerator 𝔭
  have : Fact p.Prime := ⟨hp⟩
  have hpn : p ∣ n := (Rat.HeightOneSpectrum.absNorm_asIdeal_dvd_iff_natCast_mem 𝔭).mpr hm
  obtain ⟨e, m, hpm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (NeZero.ne n) p hp.ne_one
  cases e with
  | zero => simp_all
  | succ e =>
    rw [mem_ramifiedPrimes_iff]
    intro hur
    let Q : 𝔭.asIdeal.primesOver (𝓞 F) := Classical.choice inferInstance
    have : Q.1.IsPrime := Q.2.1
    have : Q.1.LiesOver 𝔭.asIdeal := Q.2.2
    have hpQ : (p : 𝓞 F) ∈ Q.1 := by
      have hp𝔭 : (p : 𝓞 ℚ) ∈ 𝔭.asIdeal :=
        (Rat.HeightOneSpectrum.absNorm_asIdeal_dvd_iff_natCast_mem 𝔭).mp dvd_rfl
      simpa using (Ideal.mem_of_liesOver Q.1 𝔭.asIdeal (p : 𝓞 ℚ)).mp hp𝔭
    have : Q.1.LiesOver (Ideal.span {(p : ℤ)}) := by
      rw [Ideal.liesOver_iff]
      refine Ideal.IsMaximal.eq_of_le (Int.ideal_span_isMaximal_of_prime p)
        Ideal.IsPrime.ne_top' ?_
      simpa [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap] using hpQ
    have := hur Q.1
    have he := Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := 𝓞 ℚ) (p := Q.1)
    rw [Ideal.ramificationIdx_ringOfIntegers_rat_eq_int Q.1
      (Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q.1),
      Rat.ramificationIdx_eq n F Q.1 hnm hpm] at he
    have hp2 : p = 2 := by
      have := Nat.eq_one_of_mul_eq_one_left he
      have := hp.two_le
      omega
    rw [hp2] at he hnm hpm
    have he0 : e = 0 := by
      have := Nat.eq_one_of_mul_eq_one_right he
      simpa using this
    subst e
    simp only [zero_add, pow_one] at hnm
    omega

variable [IsGalois ℚ F]

/-- At a nonzero level not congruent to two modulo four, a cyclotomic Frobenius fibre over
`ℚ` is exactly an invertible arithmetic progression. Primes dividing the level belong to neither
side. -/
theorem frobeniusPrimeSet_galEquivZMod_symm_eq_setOf_absNorm_natCast_eq (hn : n % 4 ≠ 2)
    (a : (ZMod n)ˣ) :
    frobeniusPrimeSet ℚ F (ConjClasses.mk ((Rat.galEquivZMod n F).symm a)) =
      {𝔭 : HeightOneSpectrum (𝓞 ℚ) | (Ideal.absNorm 𝔭.asIdeal : ZMod n) = a} := by
  ext 𝔭
  by_cases hm : (n : 𝓞 ℚ) ∈ 𝔭.asIdeal
  · have hram : 𝔭 ∉ frobeniusPrimeSet ℚ F
        (ConjClasses.mk ((Rat.galEquivZMod n F).symm a)) := fun h ↦
      frobeniusPrimeSet_subset_compl_ramifiedPrimes _ h
        (mem_ramifiedPrimes_of_natCast_mem F n hn hm)
    refine iff_of_false hram fun ha ↦ ?_
    have hcop := (ZMod.isUnit_iff_coprime (Ideal.absNorm 𝔭.asIdeal) n).mp
      (ha.symm ▸ a.isUnit)
    have hdvd := (Rat.HeightOneSpectrum.absNorm_asIdeal_dvd_iff_natCast_mem 𝔭).mpr hm
    have hp := Rat.HeightOneSpectrum.prime_natGenerator 𝔭
    rw [Rat.HeightOneSpectrum.absNorm_asIdeal] at hcop hdvd
    exact (hp.coprime_iff_not_dvd.mp hcop) hdvd
  · rw [mem_frobeniusPrimeSet_mk_iff_autToPow_eq_absNorm (zeta_spec n ℚ F) _ hm,
      (zeta_spec n ℚ F).autToPow_eq_unitsMap_galEquivZMod dvd_rfl,
      ZMod.unitsMap_self, MonoidHom.id_apply, MulEquiv.apply_symm_apply]
    simp only [Set.mem_ofPred_eq, eq_comm]

end NumberField.Chebotarev
