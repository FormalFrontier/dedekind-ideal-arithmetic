/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import DedekindIdealArithmetic.Module.Index
public import DedekindIdealArithmetic.NumberField.ArchimedeanNorms
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.NumberField.Norm
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.PicardGroup

/-!
# Heights of normed invertible modules

For an invertible module over the ring of integers of a number field, the
multiplicative height is the index of a nonzero integral section divided by
its weighted archimedean norm product. The normalized logarithmic height is
`Real.log H / Module.finrank ℚ K`. It need not be nonnegative.

The definition evaluates the index quotient at a chosen nonzero integral
section. The nonzero section exists by faithful scalar action, independently
of the height evaluation theorem. Finiteness of the quotient and independence
of the section are conclusions, not fields of the norm data.

## Limitations

This module defines height through integral sections over a fixed number field.
The companion modules `MetricTensorProduct`, `MetricRescaling` and
`MetricTransport` supply tensor metrics, positive placewise rescaling and
pullback along module equivalences, together with their height formulas.
`RationalFrameHeight` evaluates this same height in a supplied rational frame.
Explicit finite-place local norms and compatible archimedean metrics and height
transport through finite extensions are not provided here.

## References

* J. S. Milne, *Abelian Varieties*, IV §6, 6.2–6.3.
-/

@[expose] public section

open scoped NumberField TensorProduct

universe u w

namespace NumberField

variable {K : Type u} [Field K] [hK : NumberField K]
variable {M : Type w} [AddCommGroup M] [Module (𝓞 K) M]

namespace ArchimedeanNorms

/-- The index divided by the weighted norm product at an integral section. -/
noncomputable def integralEvalHeight (P : ArchimedeanNorms K M) (m : M) : ℝ :=
  (Submodule.cardQuot (Submodule.span (𝓞 K) {m}) : ℝ) / P.normProduct m

/-- Evaluation height uses the cardinality of the quotient by the section's span. -/
theorem integralEvalHeight_apply (P : ArchimedeanNorms K M) (m : M) :
    P.integralEvalHeight m =
      (Submodule.cardQuot (Submodule.span (𝓞 K) {m}) : ℝ) /
        ∏ v : InfinitePlace K, P.apply v ((1 : v.Completion) ⊗ₜ[𝓞 K] m) ^ v.mult :=
  rfl

/-- The index/product expression of the standard unit metric is one at the integral unit. -/
@[simp]
theorem unit_integralEvalHeight_one : (unit K).integralEvalHeight (1 : 𝓞 K) = 1 := by
  simp only [integralEvalHeight, Ideal.span_singleton_one, Submodule.cardQuot_top,
    unit_normProduct_one, Nat.cast_one, div_one]

/-- A nonzero integral scalar does not change the index/product evaluation. -/
theorem integralEvalHeight_smul [Module.IsTorsionFree (𝓞 K) M]
    (P : ArchimedeanNorms K M) {r : 𝓞 K}
    (hr : r ≠ 0) (m : M) : P.integralEvalHeight (r • m) = P.integralEvalHeight m := by
  classical
  by_cases hm : m = 0
  · simp only [hm, smul_zero]
  have hrK : (r : K) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hr
  have hnormQ : Algebra.norm ℚ (r : K) ≠ 0 :=
    (hrK.isUnit.map (Algebra.norm ℚ)).ne_zero
  have hnorm : |(Algebra.norm ℚ (r : K) : ℝ)| ≠ 0 :=
    abs_ne_zero.mpr (Rat.cast_ne_zero.mpr hnormQ)
  have hprincipal : (Ideal.absNorm (Ideal.span {r}) : ℝ) =
      |(Algebra.norm ℚ (r : K) : ℝ)| := by
    have hQ : (Ideal.absNorm (Ideal.span {r}) : ℚ) =
        |Algebra.norm ℚ (r : K)| := by
      rw [Ideal.absNorm_span_singleton, Nat.cast_natAbs, Int.cast_abs, Algebra.coe_norm_int]
    exact_mod_cast hQ
  have hprincipal_ne : (Ideal.absNorm (Ideal.span {r}) : ℝ) ≠ 0 := by
    rwa [hprincipal]
  unfold integralEvalHeight
  rw [Submodule.cardQuot_span_singleton_smul_eq_absNorm_mul hm r,
    P.normProduct_smul, ← hprincipal, Nat.cast_mul]
  exact mul_div_mul_left _ _ hprincipal_ne

end ArchimedeanNorms

variable [hM : Module.Invertible (𝓞 K) M]

include hM in
omit hK in
private theorem exists_nonzero_integral_section : ∃ m : M, m ≠ 0 := by
  let : Nontrivial (M → M) :=
    (smul_left_injective' (M := 𝓞 K) (α := M)).nontrivial
  let : Nontrivial M := Function.nontrivial_of_nontrivial M M
  exact exists_ne (0 : M)

namespace ArchimedeanNorms

/-- The multiplicative height of an invertible module with archimedean norms. -/
noncomputable def height (P : ArchimedeanNorms K M) : ℝ :=
  -- Inline the existence proof so the exposed definition uses only public declarations.
  letI : Nontrivial (M → M) :=
    (smul_left_injective' (M := 𝓞 K) (α := M)).nontrivial
  letI : Nontrivial M := Function.nontrivial_of_nontrivial M M
  P.integralEvalHeight (Classical.choose (exists_ne (0 : M)))

/-- The logarithmic height, normalized by the degree of the number field. -/
noncomputable def normalizedLogHeight (P : ArchimedeanNorms K M) : ℝ :=
  Real.log P.height / (Module.finrank ℚ K : ℝ)

/-- Normalized logarithmic height is the logarithm of multiplicative height divided by degree. -/
theorem normalizedLogHeight_def (P : ArchimedeanNorms K M) :
    P.normalizedLogHeight = Real.log P.height / (Module.finrank ℚ K : ℝ) :=
  rfl

end ArchimedeanNorms

include hM hK

/-- A nonzero section of an invertible integral module has a finite quotient by its span. -/
theorem finite_quotient_span_singleton {m : M} (hm : m ≠ 0) :
    Finite (M ⧸ Submodule.span (𝓞 K) {m}) := by
  exact Module.Invertible.finite_quotient_span_singleton hm

namespace ArchimedeanNorms

/-- The integral-section height formula of Milne, *Abelian Varieties*, IV §6:
the same index/product quotient evaluates the height at every nonzero section. -/
theorem height_eq (P : ArchimedeanNorms K M) {m : M} (hm : m ≠ 0) :
    P.height =
      (Submodule.cardQuot (Submodule.span (𝓞 K) {m}) : ℝ) /
        ∏ v : InfinitePlace K, P.apply v ((1 : v.Completion) ⊗ₜ[𝓞 K] m) ^ v.mult := by
  classical
  let n : M := Classical.choose (exists_nonzero_integral_section (K := K) (M := M))
  have hn : n ≠ 0 := Classical.choose_spec (exists_nonzero_integral_section (K := K) (M := M))
  change P.integralEvalHeight n = P.integralEvalHeight m
  obtain ⟨r, s, hr, hs, hrs⟩ :=
    Module.Invertible.exists_nonzero_smul_eq (R := 𝓞 K) hn hm
  calc
    P.integralEvalHeight n = P.integralEvalHeight (r • n) :=
      (P.integralEvalHeight_smul hr n).symm
    _ = P.integralEvalHeight (s • m) := congrArg P.integralEvalHeight hrs
    _ = P.integralEvalHeight m := P.integralEvalHeight_smul hs m

/-- The multiplicative height of a normed invertible module is strictly positive. -/
theorem height_pos (P : ArchimedeanNorms K M) : 0 < P.height := by
  obtain ⟨m, hm⟩ := exists_nonzero_integral_section (K := K) (M := M)
  let : Finite (M ⧸ Submodule.span (𝓞 K) {m}) :=
    finite_quotient_span_singleton (K := K) hm
  have hindex : 0 < (Submodule.cardQuot (Submodule.span (𝓞 K) {m}) : ℝ) := by
    rw [Submodule.cardQuot_apply, Nat.cast_pos]
    exact Nat.card_pos
  rw [P.height_eq hm, ← P.normProduct_apply m]
  exact div_pos hindex (P.normProduct_pos hm)

/-- The normalized logarithmic formula of Milne, *Abelian Varieties*, IV §6,
with the weighted logarithmic norm sum subtracted from the logarithmic index. -/
theorem normalizedLogHeight_eq (P : ArchimedeanNorms K M) {m : M} (hm : m ≠ 0) :
    P.normalizedLogHeight =
      (Real.log (Submodule.cardQuot (Submodule.span (𝓞 K) {m}) : ℝ) -
        ∑ v : InfinitePlace K, (v.mult : ℝ) *
          Real.log (P.apply v ((1 : v.Completion) ⊗ₜ[𝓞 K] m))) /
        (Module.finrank ℚ K : ℝ) := by
  classical
  let : Finite (M ⧸ Submodule.span (𝓞 K) {m}) :=
    finite_quotient_span_singleton (K := K) hm
  have hindex : 0 < (Submodule.cardQuot (Submodule.span (𝓞 K) {m}) : ℝ) := by
    rw [Submodule.cardQuot_apply, Nat.cast_pos]
    exact Nat.card_pos
  have hprod :
      (∏ v : InfinitePlace K, P.apply v ((1 : v.Completion) ⊗ₜ[𝓞 K] m) ^ v.mult) ≠ 0 :=
    (P.normProduct_pos hm).ne'
  have hfactor (v : InfinitePlace K) :
      P.apply v ((1 : v.Completion) ⊗ₜ[𝓞 K] m) ^ v.mult ≠ 0 :=
    Finset.prod_ne_zero_iff.mp hprod v (Finset.mem_univ v)
  rw [P.normalizedLogHeight_def, P.height_eq hm, Real.log_div hindex.ne' hprod,
    Real.log_prod (fun v _ ↦ hfactor v)]
  simp only [Real.log_pow]

omit hM

/-- The ring of integers with its standard archimedean norms has height one. -/
@[simp]
theorem unit_height : (unit K).height = 1 := by
  calc
    (unit K).height = (unit K).integralEvalHeight 1 :=
      (unit K).height_eq one_ne_zero
    _ = 1 := unit_integralEvalHeight_one

/-- The standard unit metric has normalized logarithmic height zero. -/
@[simp]
theorem unit_normalizedLogHeight : (unit K).normalizedLogHeight = 0 := by
  rw [normalizedLogHeight_def, unit_height, Real.log_one, zero_div]

end ArchimedeanNorms

end NumberField
