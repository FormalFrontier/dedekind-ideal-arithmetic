/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import DedekindIdealArithmetic.Module.CoefficientIdealNorm
public import DedekindIdealArithmetic.NumberField.ModuleHeight
public import DedekindIdealArithmetic.NumberField.RationalFibre

/-!
# Heights in a rational frame

A rational frame `e : K ⊗[𝓞 K] M ≃ₗ[K] K` expresses the weighted archimedean
norm product of an integral section as the absolute field norm of its
coefficient times the weighted product at `e.symm 1`. This identity needs no
finiteness, torsion-freeness or invertibility assumption on the integral module.

For an invertible module, the same frame evaluates its intrinsic height as the
reciprocal of the coefficient-ideal norm times that weighted product. The proof
compares quotient indices with fractional-ideal norms and cancels the index of
a nonzero integral section. It does not choose an integral basis or define a
second height.

The norms are the given definite seminorms on the completion fibres, evaluated
on the rational fibre by scalar extension. They use ordinary, unsquared
completion norms, with multiplicity one at real places and two at complex
places. There is no degree root in the multiplicative height; only the
logarithmic height is divided by the degree of the number field.

Explicit finite-place local norms and finite-extension height transport are
not provided by these formulas.
-/

@[expose] public section

open scoped NumberField TensorProduct

universe u w

namespace NumberField.ArchimedeanNorms

variable {K : Type u} [Field K] [NumberField K]
variable {M : Type w} [AddCommGroup M] [Module (𝓞 K) M]

/-- In a rational frame, the weighted norm product of any integral section is
the absolute field norm of its coefficient times the weighted norm product
of the rational unit vector. This also holds for the zero section. -/
theorem normProduct_eq_rationalFrame (P : ArchimedeanNorms K M)
    (e : K ⊗[𝓞 K] M ≃ₗ[K] K) (m : M) :
    P.normProduct m = |(Algebra.norm ℚ (e.coefficientMap m) : ℝ)| *
      ∏ v : InfinitePlace K, P.rationalEval v (e.symm 1) ^ v.mult := by
  classical
  have hframe : (1 : K) ⊗ₜ[𝓞 K] m = e.coefficientMap m • e.symm 1 := by
    apply e.injective
    simp only [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one,
      LinearEquiv.coefficientMap_apply]
  have heval (v : InfinitePlace K) :
      P.apply v ((1 : v.Completion) ⊗ₜ[𝓞 K] m) =
        v (e.coefficientMap m) * P.rationalEval v (e.symm 1) := by
    calc
      P.apply v ((1 : v.Completion) ⊗ₜ[𝓞 K] m) =
          P.rationalEval v ((1 : K) ⊗ₜ[𝓞 K] m) := by
        rw [P.rationalEval_tmul, map_one]
      _ = _ := by
        rw [hframe, P.rationalEval_smul, InfinitePlace.Completion.norm_algebraMap]
  simp_rw [P.normProduct_apply, heval, mul_pow]
  rw [Finset.prod_mul_distrib, InfinitePlace.prod_eq_abs_norm, Rat.cast_abs]

variable [Module.Invertible (𝓞 K) M]

/-- A rational frame evaluates the intrinsic height using the norm of its
coefficient ideal and the weighted norm product of its rational unit vector. -/
theorem height_eq_rationalFrame (P : ArchimedeanNorms K M)
    (e : K ⊗[𝓞 K] M ≃ₗ[K] K) :
    P.height = ((FractionalIdeal.absNorm e.coefficientIdeal : ℝ) *
      ∏ v : InfinitePlace K, P.rationalEval v (e.symm 1) ^ v.mult)⁻¹ := by
  classical
  let : Nontrivial (M → M) :=
    (smul_left_injective' (M := 𝓞 K) (α := M)).nontrivial
  let : Nontrivial M := Function.nontrivial_of_nontrivial M M
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  let : Finite (M ⧸ Submodule.span (𝓞 K) {m}) :=
    NumberField.finite_quotient_span_singleton (K := K) hm
  have hindex_pos : 0 < ((Submodule.span (𝓞 K) {m}).cardQuot : ℝ) := by
    rw [Submodule.cardQuot_apply, Nat.cast_pos]
    exact Nat.card_pos
  have hindexQ := e.cardQuot_span_singleton_mul_absNorm_coefficientIdeal m
  rw [FractionalIdeal.absNorm_span_singleton] at hindexQ
  have hindex : ((Submodule.span (𝓞 K) {m}).cardQuot : ℝ) *
      (FractionalIdeal.absNorm e.coefficientIdeal : ℝ) =
      |(Algebra.norm ℚ (e.coefficientMap m) : ℝ)| := by
    exact_mod_cast hindexQ
  rw [P.height_eq hm, ← P.normProduct_apply m, P.normProduct_eq_rationalFrame e m,
    ← hindex, mul_assoc, div_mul_eq_div_div, div_self hindex_pos.ne', one_div]

/-- In a rational frame, normalized logarithmic height is minus the logarithmic
coefficient-ideal norm and the weighted archimedean logarithmic sum, divided
by the degree of the number field. -/
theorem normalizedLogHeight_eq_rationalFrame (P : ArchimedeanNorms K M)
    (e : K ⊗[𝓞 K] M ≃ₗ[K] K) :
    P.normalizedLogHeight =
      (-Real.log (FractionalIdeal.absNorm e.coefficientIdeal : ℝ) -
        ∑ v : InfinitePlace K, (v.mult : ℝ) * Real.log (P.rationalEval v (e.symm 1))) /
          (Module.finrank ℚ K : ℝ) := by
  classical
  have hnonzero : (FractionalIdeal.absNorm e.coefficientIdeal : ℝ) *
      (∏ v : InfinitePlace K, P.rationalEval v (e.symm 1) ^ v.mult) ≠ 0 := by
    intro hz
    have hheight : P.height = 0 := by
      rw [P.height_eq_rationalFrame e, hz, inv_zero]
    exact P.height_pos.ne' hheight
  have hnorm := (mul_ne_zero_iff.mp hnonzero).1
  have hprod := (mul_ne_zero_iff.mp hnonzero).2
  have hfactor (v : InfinitePlace K) : P.rationalEval v (e.symm 1) ^ v.mult ≠ 0 :=
    Finset.prod_ne_zero_iff.mp hprod v (Finset.mem_univ v)
  rw [P.normalizedLogHeight_def, P.height_eq_rationalFrame e, Real.log_inv,
    Real.log_mul hnorm hprod, Real.log_prod (fun v _ ↦ hfactor v)]
  simp only [Real.log_pow, neg_add, sub_eq_add_neg]

end NumberField.ArchimedeanNorms
