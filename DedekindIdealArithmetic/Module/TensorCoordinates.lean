/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Scalar extension of linear coordinates

`LinearEquiv.scalarExtensionCoordinate` extends a coordinate `M ≃ₗ[R] R` to
an `F`-linear coordinate on `F ⊗[R] M`, by base change and the tensor
right-unit equivalence. It applies to modules over commutative semirings
and arbitrary algebra semirings, without freeness or finiteness hypotheses
beyond the supplied coordinate.
-/

@[expose] public section

open scoped TensorProduct

namespace LinearEquiv

universe u v w

variable {R : Type u} {M : Type v}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable (e : M ≃ₗ[R] R) (F : Type w) [Semiring F] [Algebra R F]

/-- The scalar extension of a linear coordinate, followed by the tensor
right-unit equivalence. -/
def scalarExtensionCoordinate : F ⊗[R] M ≃ₗ[F] F :=
  e.baseChange R F ≪≫ₗ TensorProduct.AlgebraTensorModule.rid R F F

@[simp]
theorem scalarExtensionCoordinate_tmul (a : F) (x : M) :
    e.scalarExtensionCoordinate F (a ⊗ₜ[R] x) = e x • a := by
  simp [scalarExtensionCoordinate]

/-- The inverse coordinate sends a scalar to its tensor with the unit vector
of the original coordinate. -/
@[simp]
theorem scalarExtensionCoordinate_symm_apply (a : F) :
    (e.scalarExtensionCoordinate F).symm a = a ⊗ₜ[R] e.symm 1 := by
  simp [scalarExtensionCoordinate]

end LinearEquiv
