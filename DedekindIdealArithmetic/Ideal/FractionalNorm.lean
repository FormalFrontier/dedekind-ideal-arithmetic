/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.FractionalIdeal.Extended
public import Mathlib.RingTheory.FractionalIdeal.Norm
public import Mathlib.RingTheory.Ideal.Norm.RelNorm

/-!
# Absolute norms under extension of fractional ideals

For a torsion-free extension of Dedekind domains that are finite free over `ℤ`,
extending a fractional ideal raises its absolute norm to the relative rank.
The formula holds for zero as well as nonzero fractional ideals.

The proof clears a denominator using `FractionalIdeal.den_mul_self_eq_num'`,
applies the integral-ideal norm formula, and cancels the norm of a nonzero
integral principal ideal. No freeness over the smaller Dedekind domain is needed.
-/

public section

open scoped nonZeroDivisors

namespace FractionalIdeal

variable {R S K L : Type*} [CommRing R] [IsDedekindDomain R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S] [Module.IsTorsionFree R S]
  [Module.Free ℤ R] [Module.Finite ℤ R] [Module.Free ℤ S] [Module.Finite ℤ S]
  [Field K] [Field L] [Algebra R K] [Algebra S L]
  [IsFractionRing R K] [IsFractionRing S L]

/-- Extending a fractional ideal along a torsion-free extension of Dedekind domains
that are finite free over `ℤ` raises its absolute norm to the relative rank. -/
theorem absNorm_extendedHom (I : FractionalIdeal R⁰ K) :
    absNorm (extendedHom (A := R) (K := K) L S I) =
      absNorm I ^ Module.finrank R S := by
  have : Module.Finite R S := Module.Finite.of_restrictScalars_finite ℤ R S
  have hcoe (J : Ideal R) :
      absNorm (extendedHom (A := R) (K := K) L S (J : FractionalIdeal R⁰ K)) =
        absNorm (J : FractionalIdeal R⁰ K) ^ Module.finrank R S := by
    rw [extendedHom_coeIdeal_eq_map, coeIdeal_absNorm, coeIdeal_absNorm,
      Ideal.absNorm_algebraMap, Nat.cast_pow]
  let P : Ideal R := Ideal.span {(I.den : R)}
  have hden : (P : FractionalIdeal R⁰ K) * I = (I.num : FractionalIdeal R⁰ K) := by
    simpa only [P, coeIdeal_span_singleton] using I.den_mul_self_eq_num'
  have hP : absNorm (P : FractionalIdeal R⁰ K) ≠ 0 := by
    dsimp only [P]
    rw [ne_eq, absNorm_eq_zero_iff, coeIdeal_span_singleton,
      spanSingleton_eq_zero_iff, IsFractionRing.to_map_eq_zero_iff]
    exact nonZeroDivisors.coe_ne_zero I.den
  apply mul_left_cancel₀ (pow_ne_zero (Module.finrank R S) hP)
  calc
    absNorm (P : FractionalIdeal R⁰ K) ^ Module.finrank R S *
        absNorm (extendedHom (A := R) (K := K) L S I) =
        absNorm (extendedHom (A := R) (K := K) L S
          ((P : FractionalIdeal R⁰ K) * I)) := by
      rw [map_mul, map_mul, hcoe P]
    _ = absNorm (extendedHom (A := R) (K := K) L S
        (I.num : FractionalIdeal R⁰ K)) := by rw [hden]
    _ = absNorm (I.num : FractionalIdeal R⁰ K) ^ Module.finrank R S := hcoe I.num
    _ = (absNorm (P : FractionalIdeal R⁰ K) * absNorm I) ^ Module.finrank R S := by
      rw [← hden, map_mul]
    _ = absNorm (P : FractionalIdeal R⁰ K) ^ Module.finrank R S *
        absNorm I ^ Module.finrank R S := mul_pow _ _ _

end FractionalIdeal
