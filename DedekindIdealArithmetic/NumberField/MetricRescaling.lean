/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import DedekindIdealArithmetic.NumberField.ModuleHeight

/-!
# Positive rescaling of archimedean metrics

A family `c : InfinitePlace K → ℝ≥0ˣ` represents a strictly positive real
factor at each infinite place. `ArchimedeanNorms.rescale` multiplies the
ordinary, unsquared norm on the whole fibre at `v` by the value of `c v`.
The multiplicities remain one at real places and two at complex places.

Rescaling divides the multiplicative height by the weighted product of the
factors and subtracts their weighted logarithmic sum divided by the field
degree from the normalized logarithmic height. Neither a lower bound of one
for the multiplicative height nor nonnegativity of the logarithmic height
is imposed.

## References

* J. S. Milne, *Abelian Varieties*, IV §6, normed-module heights.
-/

@[expose] public section

open scoped NNReal NumberField TensorProduct

universe u w

namespace NumberField
namespace ArchimedeanNorms

variable {K : Type u} [Field K] {M : Type w} [AddCommGroup M] [Module (𝓞 K) M]

/-- Multiply each archimedean fibre norm by an intrinsically positive real factor. -/
noncomputable def rescale (P : ArchimedeanNorms K M) (c : InfinitePlace K → ℝ≥0ˣ) :
    ArchimedeanNorms K M where
  seminorm v := (c v : ℝ≥0) • P.seminorm v
  eq_zero_of_map_eq_zero v x h := by
    apply P.eq_zero_of_map_eq_zero v x
    change ((c v : ℝ≥0) : ℝ) * P.seminorm v x = 0 at h
    exact (mul_eq_zero.mp h).resolve_left (NNReal.coe_ne_zero.mpr (c v).ne_zero)

/-- The underlying seminorm is the nonnegative-real scalar multiple. -/
@[simp]
theorem rescale_seminorm (P : ArchimedeanNorms K M) (c : InfinitePlace K → ℝ≥0ˣ)
    (v : InfinitePlace K) :
    (P.rescale c).seminorm v = (c v : ℝ≥0) • P.seminorm v :=
  rfl

/-- Rescaling multiplies the norm of every fibre vector by the corresponding factor. -/
@[simp]
theorem rescale_apply (P : ArchimedeanNorms K M) (c : InfinitePlace K → ℝ≥0ˣ)
    (v : InfinitePlace K) (x : v.Completion ⊗[𝓞 K] M) :
    (P.rescale c).apply v x = ((c v : ℝ≥0) : ℝ) * P.apply v x :=
  rfl

/-- Rescaling by the constant factor one preserves the metrics. -/
@[simp]
theorem rescale_one (P : ArchimedeanNorms K M) : P.rescale 1 = P := by
  apply ext
  intro v x
  simp only [rescale_apply, Pi.one_apply, Units.val_one, NNReal.coe_one, one_mul]

/-- Successive positive rescalings multiply their factors pointwise. -/
@[simp]
theorem rescale_rescale (P : ArchimedeanNorms K M) (c d : InfinitePlace K → ℝ≥0ˣ) :
    (P.rescale c).rescale d = P.rescale (c * d) := by
  apply ext
  intro v x
  simp only [rescale_apply, Pi.mul_apply, Units.val_mul, NNReal.coe_mul]
  exact (mul_left_comm _ _ _).trans (mul_assoc _ _ _).symm

/-- The integral unit has norm equal to the rescaling factor in the rescaled unit metric. -/
theorem unit_rescale_apply_one_tmul (c : InfinitePlace K → ℝ≥0ˣ) (v : InfinitePlace K) :
    ((unit K).rescale c).apply v ((1 : v.Completion) ⊗ₜ[𝓞 K] (1 : 𝓞 K)) =
      ((c v : ℝ≥0) : ℝ) := by
  rw [rescale_apply, unit_apply_one_tmul, mul_one]

/-- A factor different from one at a specified place changes the standard unit metric. -/
theorem unit_rescale_ne (c : InfinitePlace K → ℝ≥0ˣ) {v : InfinitePlace K}
    (hc : c v ≠ 1) : (unit K).rescale c ≠ unit K := by
  intro h
  have hval := congrArg
    (fun Q : ArchimedeanNorms K (𝓞 K) ↦
      Q.apply v ((1 : v.Completion) ⊗ₜ[𝓞 K] (1 : 𝓞 K))) h
  rw [unit_rescale_apply_one_tmul, unit_apply_one_tmul] at hval
  exact hc (Units.val_eq_one.mp (NNReal.coe_eq_one.mp hval))

/-- Doubling the ordinary norms changes the unit metric. -/
theorem unit_rescale_two_ne (v : InfinitePlace K) :
    (unit K).rescale (fun _ ↦ Units.mk0 (2 : ℝ≥0) (OfNat.ofNat_ne_zero 2)) ≠ unit K := by
  apply unit_rescale_ne (v := v)
  intro h
  have htwo : (2 : ℝ≥0) = 1 := congrArg (fun a : ℝ≥0ˣ ↦ (a : ℝ≥0)) h
  exact (OfNat.ofNat_ne_one 2) htwo

variable [NumberField K]

/-- The norm product of any integral section acquires the weighted product of the factors. -/
theorem normProduct_rescale (P : ArchimedeanNorms K M) (c : InfinitePlace K → ℝ≥0ˣ)
    (m : M) :
    (P.rescale c).normProduct m =
      (∏ v : InfinitePlace K, ((c v : ℝ≥0) : ℝ) ^ v.mult) * P.normProduct m := by
  simp_rw [normProduct_apply, rescale_apply, mul_pow]
  rw [Finset.prod_mul_distrib]

/-- Positive metric rescaling divides the index/product evaluation by the weighted product
of the factors, for every integral section. -/
theorem integralEvalHeight_rescale (P : ArchimedeanNorms K M)
    (c : InfinitePlace K → ℝ≥0ˣ) (m : M) :
    (P.rescale c).integralEvalHeight m =
      P.integralEvalHeight m /
        (∏ v : InfinitePlace K, ((c v : ℝ≥0) : ℝ) ^ v.mult) := by
  rw [integralEvalHeight_apply, ← normProduct_apply, normProduct_rescale,
    integralEvalHeight_apply, ← normProduct_apply, div_div, mul_comm (P.normProduct m)]

variable [Module.Invertible (𝓞 K) M]

/-- Positive metric rescaling divides the normed-module height of Milne, *Abelian Varieties*,
IV §6, by the weighted product of the factors. -/
theorem height_rescale (P : ArchimedeanNorms K M) (c : InfinitePlace K → ℝ≥0ˣ) :
    (P.rescale c).height =
      P.height / (∏ v : InfinitePlace K, ((c v : ℝ≥0) : ℝ) ^ v.mult) := by
  let : Nontrivial (M → M) :=
    (smul_left_injective' (M := 𝓞 K) (α := M)).nontrivial
  let : Nontrivial M := Function.nontrivial_of_nontrivial M M
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  have hP : P.height = P.integralEvalHeight m := P.height_eq hm
  have hrescale : (P.rescale c).height = (P.rescale c).integralEvalHeight m :=
    (P.rescale c).height_eq hm
  rw [hrescale, integralEvalHeight_rescale, hP]

/-- Positive metric rescaling subtracts the degree-normalized weighted logarithmic sum
from the normalized logarithmic normed-module height of Milne, *Abelian Varieties*, IV §6. -/
theorem normalizedLogHeight_rescale (P : ArchimedeanNorms K M)
    (c : InfinitePlace K → ℝ≥0ˣ) :
    (P.rescale c).normalizedLogHeight = P.normalizedLogHeight -
      (∑ v : InfinitePlace K, (v.mult : ℝ) * Real.log ((c v : ℝ≥0) : ℝ)) /
        (Module.finrank ℚ K : ℝ) := by
  classical
  have hfactor (v : InfinitePlace K) : ((c v : ℝ≥0) : ℝ) ^ v.mult ≠ 0 :=
    pow_ne_zero _ (NNReal.coe_ne_zero.mpr (c v).ne_zero)
  have hprod : (∏ v : InfinitePlace K, ((c v : ℝ≥0) : ℝ) ^ v.mult) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun v _ ↦ hfactor v
  simp only [normalizedLogHeight_def]
  rw [height_rescale, Real.log_div P.height_pos.ne' hprod,
    Real.log_prod (fun v _ ↦ hfactor v)]
  simp only [Real.log_pow, sub_div]

end ArchimedeanNorms
end NumberField
