/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import DedekindIdealArithmetic.NumberField.ArchimedeanNorms
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Archimedean evaluation on the rational fibre

The scalar-extension map from `K ⊗[𝓞 K] M` to `v.Completion ⊗[𝓞 K] M` is the
existing `TensorProduct.AlgebraTensorModule.map`, applied to
`Algebra.linearMap K v.Completion` and the identity of `M`. It is `K`-linear and
injective for every integral module, without a flatness assumption on `M`.

`NumberField.ArchimedeanNorms.rationalEval` evaluates the given completion-fibre
norm after this map. The norm data remain explicit and place-dependent; no norm
on `K`, `M`, or the rational fibre is installed. The canonical unit metric is
identified on the whole rational fibre with the completion norm through the
right-unit equivalence.

## Limitations

This interface concerns one infinite place at a time. It makes no assertion
about finite places, products of norms, heights, or finite field extensions.
-/

@[expose] public section

open scoped NumberField TensorProduct

universe u w

namespace NumberField

namespace InfinitePlace

variable {K : Type u} [Field K]

/-- Scalar extension from the rational fibre to a completion fibre is injective.
The map is the tensor product of the field embedding and the identity of the
integral module. -/
theorem rationalFibre_injective {M : Type w} [AddCommMonoid M] [Module (𝓞 K) M]
    (v : InfinitePlace K) :
    Function.Injective
      (TensorProduct.AlgebraTensorModule.map (Algebra.linearMap K v.Completion)
        (LinearMap.id : M →ₗ[𝓞 K] M)) := by
  let : FaithfulSMul K v.Completion :=
    (faithfulSMul_iff_algebraMap_injective K v.Completion).mpr
      (algebraMap K v.Completion).injective
  have h :
      TensorProduct.AlgebraTensorModule.map (Algebra.linearMap K v.Completion)
          (LinearMap.id : M →ₗ[𝓞 K] M) =
        (TensorProduct.AlgebraTensorModule.cancelBaseChange
          (𝓞 K) K K v.Completion M).toLinearMap.comp
          (TensorProduct.mk K v.Completion (K ⊗[𝓞 K] M) 1) := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a m
    change algebraMap K v.Completion a ⊗ₜ[𝓞 K] m =
      TensorProduct.AlgebraTensorModule.cancelBaseChange (𝓞 K) K K v.Completion M
        ((1 : v.Completion) ⊗ₜ[K] (a ⊗ₜ[𝓞 K] m))
    rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, Algebra.smul_def, mul_one]
  rw [h]
  exact (TensorProduct.AlgebraTensorModule.cancelBaseChange
    (𝓞 K) K K v.Completion M).injective.comp
      (Module.Flat.tensorProduct_mk_injective K (K ⊗[𝓞 K] M) v.Completion)

/-- The right-unit equivalences commute with scalar extension from the rational
fibre to a completion fibre, on every vector. -/
theorem rid_rationalFibre (v : InfinitePlace K) (x : K ⊗[𝓞 K] 𝓞 K) :
    TensorProduct.AlgebraTensorModule.rid (𝓞 K) v.Completion v.Completion
        (TensorProduct.AlgebraTensorModule.map (Algebra.linearMap K v.Completion)
          (LinearMap.id : 𝓞 K →ₗ[𝓞 K] 𝓞 K) x) =
      algebraMap K v.Completion (TensorProduct.AlgebraTensorModule.rid (𝓞 K) K K x) := by
  have h :
      (LinearMap.restrictScalars K
        (TensorProduct.AlgebraTensorModule.rid (𝓞 K) v.Completion v.Completion).toLinearMap).comp
          (TensorProduct.AlgebraTensorModule.map (Algebra.linearMap K v.Completion)
            (LinearMap.id : 𝓞 K →ₗ[𝓞 K] 𝓞 K)) =
        (Algebra.linearMap K v.Completion).comp
          (TensorProduct.AlgebraTensorModule.rid (𝓞 K) K K).toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a r
    change r • algebraMap K v.Completion a = algebraMap K v.Completion (r • a)
    simp only [Algebra.smul_def, map_mul,
      ← IsScalarTower.algebraMap_apply (𝓞 K) K v.Completion]
  exact DFunLike.congr_fun h x

end InfinitePlace

namespace ArchimedeanNorms

variable {K : Type u} [Field K] {M : Type w} [AddCommGroup M] [Module (𝓞 K) M]

/-- Evaluation on the rational fibre using its canonical map to a completion fibre. -/
noncomputable def rationalEval (P : ArchimedeanNorms K M) (v : InfinitePlace K)
    (x : K ⊗[𝓞 K] M) : ℝ :=
  P.apply v (TensorProduct.AlgebraTensorModule.map (Algebra.linearMap K v.Completion)
    (LinearMap.id : M →ₗ[𝓞 K] M) x)

/-- Rational evaluation is completion-fibre evaluation after scalar extension. -/
theorem rationalEval_eq (P : ArchimedeanNorms K M) (v : InfinitePlace K)
    (x : K ⊗[𝓞 K] M) :
    P.rationalEval v x =
      P.apply v (TensorProduct.AlgebraTensorModule.map (Algebra.linearMap K v.Completion)
        (LinearMap.id : M →ₗ[𝓞 K] M) x) :=
  rfl

/-- An arbitrary rational pure tensor specializes by the field embedding. -/
@[simp]
theorem rationalEval_tmul (P : ArchimedeanNorms K M) (v : InfinitePlace K)
    (a : K) (m : M) :
    P.rationalEval v (a ⊗ₜ[𝓞 K] m) =
      P.apply v (algebraMap K v.Completion a ⊗ₜ[𝓞 K] m) :=
  rfl

/-- Rational evaluation is nonnegative. -/
theorem rationalEval_nonneg (P : ArchimedeanNorms K M) (v : InfinitePlace K)
    (x : K ⊗[𝓞 K] M) : 0 ≤ P.rationalEval v x :=
  P.apply_nonneg v _

/-- Rational evaluation vanishes at zero. -/
@[simp]
theorem rationalEval_zero (P : ArchimedeanNorms K M) (v : InfinitePlace K) :
    P.rationalEval v 0 = 0 := by
  simp only [rationalEval_eq, map_zero, apply_zero]

/-- Rational evaluation vanishes exactly at zero, without a flatness assumption
on the integral module. -/
@[simp]
theorem rationalEval_eq_zero_iff (P : ArchimedeanNorms K M) (v : InfinitePlace K)
    (x : K ⊗[𝓞 K] M) : P.rationalEval v x = 0 ↔ x = 0 := by
  constructor
  · intro h
    apply InfinitePlace.rationalFibre_injective v
    rw [map_zero]
    exact (P.apply_eq_zero_iff v _).mp h
  · rintro rfl
    exact P.rationalEval_zero v

/-- Rational evaluation satisfies the triangle inequality. -/
theorem rationalEval_add_le (P : ArchimedeanNorms K M) (v : InfinitePlace K)
    (x y : K ⊗[𝓞 K] M) :
    P.rationalEval v (x + y) ≤ P.rationalEval v x + P.rationalEval v y := by
  simp only [rationalEval_eq, map_add]
  exact P.apply_add_le v _ _

/-- Homogeneity on the rational fibre uses the norm of the scalar in the chosen
completion, not a norm on the original field. -/
theorem rationalEval_smul (P : ArchimedeanNorms K M) (v : InfinitePlace K)
    (a : K) (x : K ⊗[𝓞 K] M) :
    P.rationalEval v (a • x) =
      ‖algebraMap K v.Completion a‖ * P.rationalEval v x := by
  simp only [rationalEval_eq, map_smul]
  rw [← IsScalarTower.algebraMap_smul v.Completion a]
  exact P.apply_smul v _ _

/-- On the whole rational unit fibre, the canonical metric is the completion norm
of the field element obtained by the right-unit equivalence. -/
theorem unit_rationalEval (v : InfinitePlace K) (x : K ⊗[𝓞 K] 𝓞 K) :
    (unit K).rationalEval v x =
      ‖algebraMap K v.Completion (TensorProduct.AlgebraTensorModule.rid (𝓞 K) K K x)‖ := by
  rw [rationalEval_eq, unit_apply, InfinitePlace.rid_rationalFibre]

/-- The right-unit parametrization realizes every field element in the rational
unit fibre, with its chosen infinite-place value. -/
theorem unit_rationalEval_rid_symm (v : InfinitePlace K) (a : K) :
    (unit K).rationalEval v ((TensorProduct.AlgebraTensorModule.rid (𝓞 K) K K).symm a) =
      v a := by
  rw [unit_rationalEval, LinearEquiv.apply_symm_apply,
    InfinitePlace.Completion.norm_algebraMap]

/-- The canonical rational unit vector has norm one. -/
theorem unit_rationalEval_one (v : InfinitePlace K) :
    (unit K).rationalEval v ((1 : K) ⊗ₜ[𝓞 K] (1 : 𝓞 K)) = 1 := by
  rw [unit_rationalEval, TensorProduct.AlgebraTensorModule.rid_tmul]
  simp only [one_smul, map_one, norm_one]

end ArchimedeanNorms

end NumberField
