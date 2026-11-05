/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# Principal fractional ideals and adic norms

The adic valuation of a nonzero scalar is the exponential of the negative
exponent of its principal fractional ideal. This algebraic identity holds over
any Dedekind domain with the given fraction field, without finiteness assumptions
on the residue fields.

For an infinite Dedekind domain with finite quotients, the norm on the adic
completion restricts to the residue cardinality raised to that negative
exponent. The resulting cancellation identity compares a principal-ideal weight
with the norm of the scalar. Zero is excluded from the exponent formulas:
`FractionalIdeal.count` of the zero ideal is zero, whereas the norm of zero is zero.

The proofs combine Mathlib's fractional-ideal exponent API, adic valuations,
and residue-cardinality normalization of completion norms. The embedding and
algebra-map comparison also gives the restriction formula for finite places of
number fields. No norm on the fraction field is chosen.
-/

@[expose] public section

open scoped nonZeroDivisors

universe u v

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type u} {K : Type v} [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] (p : IsDedekindDomain.HeightOneSpectrum R)

/-- The adic valuation of a nonzero scalar is the exponential of the negative
exponent of its principal fractional ideal. No residue-field finiteness is needed. -/
theorem valuation_eq_exp_neg_count_spanSingleton (a : K) (ha : a ≠ 0) :
    p.valuation K a = WithZero.exp
      (-FractionalIdeal.count K p (FractionalIdeal.spanSingleton R⁰ a)) := by
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq R⁰ a
  have hr : r ≠ 0 := by
    intro h
    apply ha
    simp [IsFractionRing.mk'_eq_div, h]
  have hprincipal :
      FractionalIdeal.spanSingleton R⁰ (IsLocalization.mk' K r s) =
        FractionalIdeal.spanSingleton R⁰ ((algebraMap R K (s : R))⁻¹) *
          (Ideal.span {r} : FractionalIdeal R⁰ K) := by
    rw [FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton, IsFractionRing.mk'_eq_div,
      div_eq_mul_inv, mul_comm]
  rw [FractionalIdeal.count_well_defined K p
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr ha) hprincipal,
    p.valuation_of_mk', p.intValuation_if_neg hr,
    p.intValuation_if_neg (nonZeroDivisors.coe_ne_zero s), ← WithZero.exp_sub]
  congr 1
  ring

end IsDedekindDomain.HeightOneSpectrum

namespace NumberField.FinitePlace

variable {R : Type u} {K : Type v} [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- The embedding into an adic completion is its canonical algebra map. -/
theorem embedding_eq_algebraMap (p : IsDedekindDomain.HeightOneSpectrum R) :
    embedding (K := K) p = algebraMap K (p.adicCompletion K) := by
  ext a
  simp only [embedding_apply, IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion,
    Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply]

end NumberField.FinitePlace

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type u} {K : Type v} [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [Infinite R] [Ring.HasFiniteQuotients R]
  (p : IsDedekindDomain.HeightOneSpectrum R)

/-- The completion norm of a scalar equals its residue-cardinality adic absolute value.
This holds also for the zero scalar. -/
theorem norm_algebraMap_eq_adicAbv (a : K) :
    ‖algebraMap K (p.adicCompletion K) a‖ =
      NumberField.HeightOneSpectrum.adicAbv K p a := by
  rw [← NumberField.FinitePlace.embedding_eq_algebraMap]
  exact NumberField.FinitePlace.norm_embedding p a

/-- The completion norm of a nonzero scalar is the residue cardinality raised
to the negative exponent of its principal fractional ideal. -/
theorem norm_algebraMap_eq_zpow_neg_count_spanSingleton (a : K) (ha : a ≠ 0) :
    ‖algebraMap K (p.adicCompletion K) a‖ = (Ideal.absNorm p.asIdeal : ℝ) ^
      (-FractionalIdeal.count K p (FractionalIdeal.spanSingleton R⁰ a)) := by
  rw [p.norm_algebraMap_eq_adicAbv, NumberField.HeightOneSpectrum.adicAbv_def,
    p.valuation_eq_exp_neg_count_spanSingleton a ha,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero,
    WithZero.toAdd_unzero_eq_log, WithZero.log_exp]
  norm_cast

/-- A principal-ideal weight cancels the completion norm of its nonzero generator. -/
theorem zpow_count_spanSingleton_mul_norm_algebraMap_eq_one (a : K) (ha : a ≠ 0) :
    (Ideal.absNorm p.asIdeal : ℝ) ^
        FractionalIdeal.count K p (FractionalIdeal.spanSingleton R⁰ a) *
      ‖algebraMap K (p.adicCompletion K) a‖ = 1 := by
  have hq : (Ideal.absNorm p.asIdeal : ℝ) ≠ 0 := by
    exact_mod_cast NumberField.HeightOneSpectrum.absNorm_ne_zero p
  rw [p.norm_algebraMap_eq_zpow_neg_count_spanSingleton a ha, ← zpow_add₀ hq,
    add_neg_cancel, zpow_zero]

end IsDedekindDomain.HeightOneSpectrum

namespace NumberField.FinitePlace

variable {K : Type v} [Field K] [NumberField K]

/-- The norm on the completion associated to a finite place restricts to that place. -/
theorem norm_algebraMap (w : FinitePlace K) (a : K) :
    ‖algebraMap K (w.maximalIdeal.adicCompletion K) a‖ = w a := by
  rw [← embedding_eq_algebraMap]
  exact norm_embedding_eq w a

end NumberField.FinitePlace
