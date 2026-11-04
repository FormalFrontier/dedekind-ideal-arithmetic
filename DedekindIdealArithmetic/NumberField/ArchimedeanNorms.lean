/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.Normed.Module.Seminorm.Norm
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.RingTheory.Flat.Basic

/-!
# Norms on archimedean module fibres

`NumberField.ArchimedeanNorms K M` consists of a definite seminorm on each
`v.Completion ⊗[𝓞 K] M`. The completion is the first tensor factor so that its
scalar action is the canonical one. Norms are explicit data: no norm or metric
instances are installed on `M` or on the tensor fibres.

The completion norm is the ordinary, unsquared absolute value. Products over
infinite places use `InfinitePlace.mult`, with weight one at real places and
two at complex places.
-/

@[expose] public section

open scoped NumberField TensorProduct

universe u w

namespace NumberField

namespace InfinitePlace

/-- A flat integral module embeds into each archimedean fibre by scalar extension. -/
theorem one_tmul_injective {K : Type u} [Field K] {M : Type w}
    [AddCommMonoid M] [Module (𝓞 K) M] [Module.Flat (𝓞 K) M]
    (v : InfinitePlace K) :
    Function.Injective (fun m : M ↦ (1 : v.Completion) ⊗ₜ[𝓞 K] m) := by
  let : FaithfulSMul (𝓞 K) v.Completion :=
    (faithfulSMul_iff_algebraMap_injective (𝓞 K) v.Completion).mpr <| by
      rw [IsScalarTower.algebraMap_eq (𝓞 K) K v.Completion]
      exact (algebraMap K v.Completion).injective.comp RingOfIntegers.coe_injective
  exact Module.Flat.tensorProduct_mk_injective (𝓞 K) M v.Completion

end InfinitePlace

/-- The completion norm restricts to the infinite place on the original field. -/
theorem InfinitePlace.Completion.norm_algebraMap {K : Type u} [Field K]
    (v : InfinitePlace K) (a : K) : ‖algebraMap K v.Completion a‖ = v a := by
  change ‖(((WithAbs.equiv v.1).symm a : WithAbs v.1) : v.Completion)‖ = v a
  rw [InfinitePlace.Completion.norm_coe, (WithAbs.equiv v.1).apply_symm_apply]

/-- A family of definite seminorms on the archimedean fibres of an integral module. -/
structure ArchimedeanNorms (K : Type u) [Field K] (M : Type w)
    [AddCommGroup M] [Module (𝓞 K) M] where
  /-- The seminorm on the fibre at an infinite place. -/
  seminorm (v : InfinitePlace K) : Seminorm v.Completion (v.Completion ⊗[𝓞 K] M)
  /-- Each seminorm detects zero on the whole fibre. -/
  eq_zero_of_map_eq_zero (v : InfinitePlace K) (x : v.Completion ⊗[𝓞 K] M) :
    seminorm v x = 0 → x = 0

namespace ArchimedeanNorms

variable {K : Type u} [Field K] {M : Type w} [AddCommGroup M] [Module (𝓞 K) M]

/-- Evaluation of an archimedean norm on a fibre vector. -/
noncomputable def apply (P : ArchimedeanNorms K M) (v : InfinitePlace K)
    (x : v.Completion ⊗[𝓞 K] M) : ℝ :=
  P.seminorm v x

/-- Norm evaluation agrees with the underlying seminorm. -/
theorem apply_eq (P : ArchimedeanNorms K M) (v : InfinitePlace K)
    (x : v.Completion ⊗[𝓞 K] M) : P.apply v x = P.seminorm v x :=
  rfl

/-- Archimedean norms are determined by their values on all fibre vectors. -/
@[ext]
theorem ext {P Q : ArchimedeanNorms K M}
    (h : ∀ (v : InfinitePlace K) (x : v.Completion ⊗[𝓞 K] M),
      P.apply v x = Q.apply v x) : P = Q := by
  rcases P with ⟨p, _⟩
  rcases Q with ⟨q, _⟩
  have hpq : p = q := funext fun v ↦ Seminorm.ext (h v)
  cases hpq
  rfl

/-- A fibre norm is nonnegative. -/
theorem apply_nonneg (P : ArchimedeanNorms K M) (v : InfinitePlace K)
    (x : v.Completion ⊗[𝓞 K] M) : 0 ≤ P.apply v x :=
  NonnegHomClass.apply_nonneg (P.seminorm v) x

/-- A fibre norm vanishes at zero. -/
@[simp]
theorem apply_zero (P : ArchimedeanNorms K M) (v : InfinitePlace K) :
    P.apply v 0 = 0 :=
  map_zero (P.seminorm v)

/-- A fibre norm vanishes exactly at zero. -/
@[simp]
theorem apply_eq_zero_iff (P : ArchimedeanNorms K M) (v : InfinitePlace K)
    (x : v.Completion ⊗[𝓞 K] M) : P.apply v x = 0 ↔ x = 0 := by
  constructor
  · exact P.eq_zero_of_map_eq_zero v x
  · rintro rfl
    exact P.apply_zero v

/-- Homogeneity uses the ordinary completion absolute value. -/
theorem apply_smul (P : ArchimedeanNorms K M) (v : InfinitePlace K)
    (a : v.Completion) (x : v.Completion ⊗[𝓞 K] M) :
    P.apply v (a • x) = ‖a‖ * P.apply v x :=
  map_smul_eq_mul (P.seminorm v) a x

/-- Homogeneity for a scalar from the original field uses its infinite-place value. -/
theorem apply_algebraMap_smul (P : ArchimedeanNorms K M) (v : InfinitePlace K)
    (a : K) (x : v.Completion ⊗[𝓞 K] M) :
    P.apply v ((algebraMap K v.Completion a) • x) = v a * P.apply v x := by
  rw [P.apply_smul, InfinitePlace.Completion.norm_algebraMap]

/-- Integral scalars act on a fibre with their ordinary infinite-place absolute value. -/
theorem apply_integral_smul (P : ArchimedeanNorms K M) (v : InfinitePlace K)
    (r : 𝓞 K) (x : v.Completion ⊗[𝓞 K] M) :
    P.apply v (r • x) = v (r : K) * P.apply v x := by
  rw [← IsScalarTower.algebraMap_smul v.Completion r,
    IsScalarTower.algebraMap_apply (𝓞 K) K v.Completion, P.apply_algebraMap_smul]

/-- Specializing an integral scalar multiple to a fibre respects norm homogeneity. -/
theorem apply_one_tmul_smul (P : ArchimedeanNorms K M) (v : InfinitePlace K)
    (r : 𝓞 K) (m : M) :
    P.apply v ((1 : v.Completion) ⊗ₜ[𝓞 K] (r • m)) =
      v (r : K) * P.apply v ((1 : v.Completion) ⊗ₜ[𝓞 K] m) := by
  rw [TensorProduct.tmul_smul, P.apply_integral_smul]

/-- A fibre norm satisfies the triangle inequality. -/
theorem apply_add_le (P : ArchimedeanNorms K M) (v : InfinitePlace K)
    (x y : v.Completion ⊗[𝓞 K] M) :
    P.apply v (x + y) ≤ P.apply v x + P.apply v y :=
  map_add_le_add (P.seminorm v) x y

/-- The ring of integers with the norms induced by the completions. -/
noncomputable def unit (K : Type u) [Field K] : ArchimedeanNorms K (𝓞 K) where
  seminorm v := (normSeminorm v.Completion v.Completion).comp
    (TensorProduct.AlgebraTensorModule.rid (𝓞 K) v.Completion v.Completion).toLinearMap
  eq_zero_of_map_eq_zero v x h := by
    apply (TensorProduct.AlgebraTensorModule.rid (𝓞 K) v.Completion v.Completion).injective
    change ‖TensorProduct.AlgebraTensorModule.rid (𝓞 K) v.Completion v.Completion x‖ = 0 at h
    simpa only [map_zero] using (norm_eq_zero.mp h)

/-- The unit metric is the completion norm transported along the tensor unit equivalence. -/
@[simp]
theorem unit_apply (v : InfinitePlace K) (x : v.Completion ⊗[𝓞 K] 𝓞 K) :
    (unit K).apply v x =
      ‖TensorProduct.AlgebraTensorModule.rid (𝓞 K) v.Completion v.Completion x‖ :=
  rfl

/-- The integral unit has norm one in every archimedean fibre. -/
theorem unit_apply_one_tmul (v : InfinitePlace K) :
    (unit K).apply v ((1 : v.Completion) ⊗ₜ[𝓞 K] (1 : 𝓞 K)) = 1 := by
  rw [unit_apply]
  simp only [TensorProduct.AlgebraTensorModule.rid_tmul, one_smul, norm_one]

variable [NumberField K]

/-- The weighted product of the norms of an integral section at the infinite places. -/
noncomputable def normProduct (P : ArchimedeanNorms K M) (m : M) : ℝ :=
  ∏ v : InfinitePlace K, P.apply v ((1 : v.Completion) ⊗ₜ[𝓞 K] m) ^ v.mult

/-- The norm product uses multiplicity one at real places and two at complex places. -/
theorem normProduct_apply (P : ArchimedeanNorms K M) (m : M) :
    P.normProduct m =
      ∏ v : InfinitePlace K, P.apply v ((1 : v.Completion) ⊗ₜ[𝓞 K] m) ^ v.mult :=
  rfl

/-- A nonzero section of a flat integral module has positive weighted norm product. -/
theorem normProduct_pos [Module.Flat (𝓞 K) M]
    (P : ArchimedeanNorms K M) {m : M} (hm : m ≠ 0) :
    0 < P.normProduct m := by
  classical
  rw [normProduct_apply]
  refine Finset.prod_pos fun v _ ↦ pow_pos ?_ _
  refine lt_of_le_of_ne (P.apply_nonneg v _) ?_
  intro h
  apply hm
  apply v.one_tmul_injective (M := M)
  simpa only [TensorProduct.tmul_zero] using
    (P.apply_eq_zero_iff v _).mp h.symm

/-- Integral scalar multiplication scales the weighted product by the absolute field norm. -/
theorem normProduct_smul (P : ArchimedeanNorms K M) (r : 𝓞 K) (m : M) :
    P.normProduct (r • m) = |(Algebra.norm ℚ (r : K) : ℝ)| * P.normProduct m := by
  simp_rw [normProduct_apply, P.apply_one_tmul_smul, mul_pow]
  rw [Finset.prod_mul_distrib, InfinitePlace.prod_eq_abs_norm, Rat.cast_abs]

/-- The standard unit metric has weighted norm product one at the integral unit. -/
@[simp]
theorem unit_normProduct_one : (unit K).normProduct (1 : 𝓞 K) = 1 := by
  rw [normProduct_apply]
  simp only [unit_apply_one_tmul, one_pow, Finset.prod_const_one]

end ArchimedeanNorms

end NumberField
