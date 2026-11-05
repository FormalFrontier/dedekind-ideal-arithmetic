/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import DedekindIdealArithmetic.NumberField.RationalFrameHeight
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# Fractional-ideal norms and finite-place height factors

The absolute norm of a nonzero fractional ideal of a number field is the
finite-support product of residue cardinalities raised to its signed ideal
exponents. This is the fractional-ideal norm factorization, cast to `ℝ` and
reindexed by the equivalence between finite places and height-one primes.
The nonzero hypothesis is essential: the zero ideal has all exponents zero
but absolute norm zero.

Substitution in the rational-frame formula evaluates the intrinsic height
of an invertible module. Its finite-place factors have the negative of the
coefficient-ideal exponents, while its denominator is the weighted
archimedean norm product of the rational unit vector. No nonzeroness
hypothesis on the coefficient ideal is needed: the rational frame implies it.

These formulas introduce neither a second height nor norms on finite
completion fibres. No integral basis or degree root is used.
-/

@[expose] public section

open scoped NumberField TensorProduct nonZeroDivisors

universe u w

namespace NumberField

variable {K : Type u} [Field K] [NumberField K]

namespace FinitePlace

/-- The real absolute norm of a nonzero fractional ideal is the finite-support
product of residue cardinalities raised to its signed finite-place exponents. -/
theorem absNorm_eq_finprod_count (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) :
    (FractionalIdeal.absNorm I : ℝ) = ∏ᶠ w : FinitePlace K,
      (Ideal.absNorm w.maximalIdeal.asIdeal : ℝ) ^
        FractionalIdeal.count K w.maximalIdeal I := by
  have hs : (fun p : IsDedekindDomain.HeightOneSpectrum (𝓞 K) ↦
      (Ideal.absNorm p.asIdeal : ℚ) ^ FractionalIdeal.count K p I).HasFiniteMulSupport := by
    refine (Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors I)).subset ?_
    intro p hp hcount
    exact hp (by simp only [hcount, zpow_zero])
  rw [FractionalIdeal.absNorm_eq_finprod_count I hI]
  have hcast := map_finprod (Rat.castHom ℝ) hs
  simp only [Rat.coe_castHom] at hcast
  rw [hcast]
  simpa only [Rat.cast_zpow, Rat.cast_natCast, equivHeightOneSpectrum_apply] using
    (finprod_comp_equiv (equivHeightOneSpectrum (K := K))
      (f := fun p : IsDedekindDomain.HeightOneSpectrum (𝓞 K) ↦
        (Ideal.absNorm p.asIdeal : ℝ) ^ FractionalIdeal.count K p I)).symm

end FinitePlace

namespace ArchimedeanNorms

variable {M : Type w} [AddCommGroup M] [Module (𝓞 K) M]
variable [Module.Invertible (𝓞 K) M]

/-- A rational frame evaluates the intrinsic height as the finite-place product
with negative coefficient-ideal exponents, divided by the weighted archimedean
norm product of the rational unit vector. -/
theorem height_eq_finitePlace (P : ArchimedeanNorms K M)
    (e : K ⊗[𝓞 K] M ≃ₗ[K] K) :
    P.height = (∏ᶠ w : FinitePlace K,
      (Ideal.absNorm w.maximalIdeal.asIdeal : ℝ) ^
        (-FractionalIdeal.count K w.maximalIdeal e.coefficientIdeal)) /
      (∏ v : InfinitePlace K, P.rationalEval v (e.symm 1) ^ v.mult) := by
  rw [P.height_eq_rationalFrame e,
    FinitePlace.absNorm_eq_finprod_count e.coefficientIdeal e.coefficientIdeal_ne_zero,
    mul_inv, div_eq_mul_inv, ← finprod_inv_distrib]
  simp only [zpow_neg]

end ArchimedeanNorms

end NumberField
