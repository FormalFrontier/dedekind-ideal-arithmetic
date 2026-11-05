/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# Attainment of fractional-ideal exponents

At a fixed height-one prime of a Dedekind domain, a nonzero fractional ideal
contains a nonzero element whose principal fractional ideal has the same
factorization exponent. Together with `FractionalIdeal.count_mono`, this says
that the exponent of the ideal is the minimum of the principal-ideal exponents
of its nonzero elements.

The element is chosen separately for each prime; the fractional ideal need not
be principal. Clearing a denominator subtracts the same exponent on both sides,
so the result also applies to negative fractional-ideal exponents.

The proof uses Mathlib's fractional-ideal factor counts and the power-membership
criterion for adic valuations.
-/

@[expose] public section

open scoped nonZeroDivisors

universe u v

namespace FractionalIdeal

variable {R : Type u} [CommRing R] [IsDedekindDomain R]

private theorem exists_mem_factors_count_span_singleton_eq
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (p : IsDedekindDomain.HeightOneSpectrum R) {J : Ideal R} (hJ : J ≠ 0) :
    ∃ b ∈ J, b ≠ 0 ∧
      (Associates.mk p.asIdeal).count (Associates.mk (Ideal.span {b} : Ideal R)).factors =
        (Associates.mk p.asIdeal).count (Associates.mk J).factors := by
  classical
  let m := (Associates.mk p.asIdeal).count (Associates.mk J).factors
  have hJ' : (J : FractionalIdeal R⁰ K) ≠ 0 := coeIdeal_ne_zero.mpr hJ
  have hnot : ¬J ≤ p.asIdeal ^ (m + 1) := by
    intro h
    have hle : ((m + 1 : ℕ) : ℤ) ≤ (m : ℤ) := by
      simpa only [coeIdeal_pow, count_pow_self, count_coe K p hJ, m] using
        (count_mono K p hJ' ((coeIdeal_le_coeIdeal K).mpr h))
    exact (Nat.not_succ_le_self m) (Int.ofNat_le.mp hle)
  obtain ⟨b, hbJ, hbnot⟩ := SetLike.not_le_iff_exists.mp hnot
  have hb : b ≠ 0 := by
    intro h
    apply hbnot
    rw [h]
    exact Ideal.zero_mem _
  have hbK : algebraMap R K b ≠ 0 :=
    (map_ne_zero_iff (algebraMap R K) (IsFractionRing.injective R K)).mpr hb
  have hbspan : (Ideal.span {b} : Ideal R) ≠ 0 := by
    exact fun h => hb (Ideal.span_singleton_eq_bot.mp (h.trans Ideal.zero_eq_bot))
  let k := (Associates.mk p.asIdeal).count
    (Associates.mk (Ideal.span {b} : Ideal R)).factors
  have hmk : m ≤ k := by
    have h := count_mono K p (spanSingleton_ne_zero_iff.mpr hbK)
      (spanSingleton_le_iff_mem.mpr (mem_coeIdeal_of_mem R⁰ hbJ))
    rw [← coeIdeal_span_singleton, count_coe K p hbspan, count_coe K p hJ] at h
    exact Int.ofNat_le.mp h
  have hkm : k < m + 1 := by
    apply lt_of_not_ge
    intro h
    apply hbnot
    apply (p.intValuation_le_pow_iff_mem b (m + 1)).mp
    rw [p.intValuation_if_neg hb, WithZero.exp_le_exp, neg_le_neg_iff]
    exact Int.ofNat_le.mpr h
  exact ⟨b, hbJ, hb, Nat.eq_of_le_of_lt_succ hmk hkm⟩

variable {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
  (p : IsDedekindDomain.HeightOneSpectrum R)

/-- At a fixed height-one prime, the exponent of a nonzero fractional ideal is
attained by the principal fractional ideal of a nonzero element of the ideal.
The element may depend on the prime; no principal-ideal hypothesis is needed. -/
theorem exists_mem_count_spanSingleton_eq
    {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) :
    ∃ a ∈ I, a ≠ 0 ∧ count K p (spanSingleton R⁰ a) = count K p I := by
  obtain ⟨d, J, hd, hIJ⟩ := exists_eq_spanSingleton_mul I
  obtain ⟨b, hbJ, hb, hcount⟩ :=
    exists_mem_factors_count_span_singleton_eq K p (ideal_factor_ne_zero hI hIJ)
  have hdK : algebraMap R K d ≠ 0 :=
    (map_ne_zero_iff (algebraMap R K) (IsFractionRing.injective R K)).mpr hd
  have hbK : algebraMap R K b ≠ 0 :=
    (map_ne_zero_iff (algebraMap R K) (IsFractionRing.injective R K)).mpr hb
  let a : K := (algebraMap R K d)⁻¹ * algebraMap R K b
  have ha : a ≠ 0 := mul_ne_zero (inv_ne_zero hdK) hbK
  refine ⟨a, ?_, ha, ?_⟩
  · rw [hIJ]
    exact mem_singleton_mul.mpr
      ⟨algebraMap R K b, mem_coeIdeal_of_mem R⁰ hbJ, rfl⟩
  · have hspan : spanSingleton R⁰ a =
        spanSingleton R⁰ (algebraMap R K d)⁻¹ *
          (Ideal.span {b} : FractionalIdeal R⁰ K) := by
      simp only [a, coeIdeal_span_singleton, spanSingleton_mul_spanSingleton]
    rw [count_well_defined K p (spanSingleton_ne_zero_iff.mpr ha) hspan,
      count_well_defined K p hI hIJ, hcount]

end FractionalIdeal
