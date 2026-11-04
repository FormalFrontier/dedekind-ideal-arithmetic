/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.Normed.Module.Seminorm.Norm
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.PicardGroup
import Mathlib.Tactic.Ring

/-!
# Scalar extension of a seminorm on a line

`Seminorm.extendScalarsRankOne` extends a possibly degenerate seminorm on an
invertible module over a normed field `k` to `l ⊗[k] V`, for a normed field
extension `l` of `k`. Its characteristic formula is
`p.extendScalarsRankOne l (a ⊗ₜ[k] x) = ‖a‖ * p x`.

A linear coordinate on `V` identifies its scalar extension with `l`. The
construction pulls back the field norm and scales it by the seminorm of the
coordinate's unit vector. The characteristic formula determines the result
uniquely, so the result does not depend on the chosen coordinate. The unit
model recovers the field norm through the canonical tensor comparison.

No norm or metric instances are installed on the module or its tensor product.
There are no completeness or finite-extension hypotheses.
-/

@[expose] public section

open scoped NNReal TensorProduct

universe u v w

namespace Seminorm

section Coordinates

variable {k : Type u} [Field k] {V : Type w} [AddCommGroup V] [Module k V]

private noncomputable def rankOneCoordinate [Module.Invertible k V] : V ≃ₗ[k] k :=
  (Module.Invertible.free_iff_linearEquiv.mp (inferInstance : Module.Free k V)).some

variable (l : Type v) [Field l] [Algebra k l]

private def scalarExtensionCoordinate (e : V ≃ₗ[k] k) : l ⊗[k] V ≃ₗ[l] l :=
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl l l) e ≪≫ₗ
    TensorProduct.AlgebraTensorModule.rid k l l

@[simp]
private theorem scalarExtensionCoordinate_tmul (e : V ≃ₗ[k] k) (a : l) (x : V) :
    scalarExtensionCoordinate l e (a ⊗ₜ[k] x) = e x • a := by
  simp [scalarExtensionCoordinate]

private theorem eq_coordinate_smul (e : V ≃ₗ[k] k) (x : V) :
    x = e x • e.symm 1 := by
  apply e.injective
  simp

private theorem eq_coordinate_tmul (e : V ≃ₗ[k] k) (z : l ⊗[k] V) :
    z = scalarExtensionCoordinate l e z ⊗ₜ[k] e.symm 1 := by
  apply (scalarExtensionCoordinate l e).injective
  simp

end Coordinates

variable {k : Type u} [NormedField k] (l : Type v) [NormedField l]
  [NormedAlgebra k l] {V : Type w} [AddCommGroup V] [Module k V]

private theorem apply_eq_coordinate (p : Seminorm k V) (e : V ≃ₗ[k] k) (x : V) :
    p x = ‖e x‖ * p (e.symm 1) := by
  calc
    p x = p (e x • e.symm 1) := congrArg p (eq_coordinate_smul e x)
    _ = ‖e x‖ * p (e.symm 1) := map_smul_eq_mul p _ _

variable [Module.Invertible k V]

/-- Extension of a seminorm on a one-dimensional vector space to a normed field
extension. The seminorm may be zero; no norm instance is chosen on either module. -/
noncomputable def extendScalarsRankOne (p : Seminorm k V) : Seminorm l (l ⊗[k] V) :=
  let e : V ≃ₗ[k] k :=
    (Module.Invertible.free_iff_linearEquiv.mp (inferInstance : Module.Free k V)).some
  let c : ℝ≥0 := ⟨p (e.symm 1), apply_nonneg p _⟩
  c • (normSeminorm l l).comp
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl l l) e ≪≫ₗ
        TensorProduct.AlgebraTensorModule.rid k l l).toLinearMap

/-- The extended seminorm is multiplicative on pure tensors, including when the
original seminorm is degenerate. -/
@[simp]
theorem extendScalarsRankOne_apply_tmul (p : Seminorm k V) (a : l) (x : V) :
    p.extendScalarsRankOne l (a ⊗ₜ[k] x) = ‖a‖ * p x := by
  let e : V ≃ₗ[k] k := rankOneCoordinate
  change p (e.symm 1) * ‖scalarExtensionCoordinate l e (a ⊗ₜ[k] x)‖ = ‖a‖ * p x
  rw [scalarExtensionCoordinate_tmul, norm_smul, apply_eq_coordinate p e x]
  ring

/-- Restriction along the canonical map into the scalar extension recovers the
original seminorm. -/
theorem extendScalarsRankOne_apply_one_tmul (p : Seminorm k V) (x : V) :
    p.extendScalarsRankOne l ((1 : l) ⊗ₜ[k] x) = p x := by
  simp

/-- Evaluation in any linear coordinate, not just the coordinate used to define
`extendScalarsRankOne`. -/
theorem extendScalarsRankOne_apply (p : Seminorm k V) (e : V ≃ₗ[k] k)
    (z : l ⊗[k] V) :
    p.extendScalarsRankOne l z = p (e.symm 1) *
      ‖(TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl l l) e ≪≫ₗ
        TensorProduct.AlgebraTensorModule.rid k l l) z‖ := by
  calc
    p.extendScalarsRankOne l z = p.extendScalarsRankOne l
        (scalarExtensionCoordinate l e z ⊗ₜ[k] e.symm 1) :=
      congrArg (p.extendScalarsRankOne l) (eq_coordinate_tmul l e z)
    _ = ‖scalarExtensionCoordinate l e z‖ * p (e.symm 1) :=
      extendScalarsRankOne_apply_tmul l p _ _
    _ = _ := mul_comm _ _

/-- The pure-tensor formula uniquely characterizes the scalar extension of a
seminorm on a line. -/
theorem extendScalarsRankOne_unique (p : Seminorm k V) (q : Seminorm l (l ⊗[k] V))
    (h : ∀ (a : l) (x : V), q (a ⊗ₜ[k] x) = ‖a‖ * p x) :
    q = p.extendScalarsRankOne l := by
  let e : V ≃ₗ[k] k := rankOneCoordinate
  apply Seminorm.ext
  intro z
  calc
    q z = q (scalarExtensionCoordinate l e z ⊗ₜ[k] e.symm 1) :=
      congrArg q (eq_coordinate_tmul l e z)
    _ = ‖scalarExtensionCoordinate l e z‖ * p (e.symm 1) := h _ _
    _ = p.extendScalarsRankOne l
        (scalarExtensionCoordinate l e z ⊗ₜ[k] e.symm 1) :=
      (extendScalarsRankOne_apply_tmul l p _ _).symm
    _ = p.extendScalarsRankOne l z :=
      congrArg (p.extendScalarsRankOne l) (eq_coordinate_tmul l e z).symm

/-- A definite seminorm remains definite after scalar extension. -/
theorem extendScalarsRankOne_eq_zero_iff (p : Seminorm k V)
    (hp : ∀ x : V, p x = 0 → x = 0) (z : l ⊗[k] V) :
    p.extendScalarsRankOne l z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    let e : V ≃ₗ[k] k := rankOneCoordinate
    have he : e.symm (1 : k) ≠ 0 := by
      intro h
      have h' := congrArg e h
      simp at h'
    have hp_unit : p (e.symm 1) ≠ 0 := fun h ↦ he (hp _ h)
    have hprod : p (e.symm 1) * ‖scalarExtensionCoordinate l e z‖ = 0 :=
      (extendScalarsRankOne_apply l p e z).symm.trans hz
    have hcoord : scalarExtensionCoordinate l e z = 0 :=
      norm_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hp_unit)
    apply (scalarExtensionCoordinate l e).injective
    simpa only [map_zero] using hcoord
  · rintro rfl
    exact map_zero _

/-- For the unit line with its field norm, scalar extension recovers the norm of
`l` through the canonical equivalence `l ⊗[k] k ≃ₗ[l] l`. -/
theorem extendScalarsRankOne_normSeminorm :
    (normSeminorm k k).extendScalarsRankOne l =
      (normSeminorm l l).comp (TensorProduct.AlgebraTensorModule.rid k l l).toLinearMap := by
  symm
  apply extendScalarsRankOne_unique l
  intro a x
  simp [norm_smul, mul_comm]

end Seminorm
