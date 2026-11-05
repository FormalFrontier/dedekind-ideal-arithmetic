/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import DedekindIdealArithmetic.Ideal.AdicNorm
public import DedekindIdealArithmetic.Module.CoefficientIdeal
public import DedekindIdealArithmetic.Module.RankOneSeminorm
public import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.Tactic.Ring

/-!
# Lattice-normalized seminorms on adic fibres

A rational frame of a finite module defines a definite seminorm on its adic
fibre. Its value is the norm of the fibre coordinate multiplied by the residue
cardinality to the exponent of the coefficient ideal. The plus sign on the exponent
makes the change in the ideal cancel the change in the coordinate.

`LinearEquiv.adicSeminorm` constructs this seminorm from a supplied frame.
`Module.adicSeminorm` is the frame-independent construction for an invertible
module. Its characteristic formula holds in every rational frame. The scalar
module recovers the selected norm on the adic completion on the whole fibre.

The construction first pulls back a weighted norm to the fibre over the fraction
field tagged with its adic absolute value. It then uses
`Seminorm.extendScalarsRankOne` and cancels the intermediate base change. No norm
or metric instance is installed on the fraction field or on a module fibre.
-/

@[expose] public section

open scoped NNReal TensorProduct nonZeroDivisors

universe u v w

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type u} {K : Type v} [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [Infinite R] [Ring.HasFiniteQuotients R]
  (p : IsDedekindDomain.HeightOneSpectrum R)

/-- The algebra map from the fraction field tagged with its adic absolute value
into the adic completion preserves the selected norm. -/
theorem norm_algebraMap_withAbs (a : WithAbs (NumberField.HeightOneSpectrum.adicAbv K p)) :
    ‖algebraMap (WithAbs (NumberField.HeightOneSpectrum.adicAbv K p))
      (p.adicCompletion K) a‖ = ‖a‖ := by
  rw [WithAbs.algebraMap_left_apply, p.norm_algebraMap_eq_adicAbv,
    WithAbs.norm_eq_apply_ofAbs]

/-- The adic completion is a normed algebra over the fraction field tagged with
the same residue-cardinality absolute value. -/
noncomputable instance normedAlgebraAdicCompletion :
    NormedAlgebra (WithAbs (NumberField.HeightOneSpectrum.adicAbv K p))
      (p.adicCompletion K) where
  norm_smul_le a x := by
    rw [Algebra.smul_def, norm_mul, p.norm_algebraMap_withAbs]

end IsDedekindDomain.HeightOneSpectrum

namespace LinearEquiv

variable {R : Type u} {K : Type v} {M : Type w}
variable [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
variable [Infinite R] [Ring.HasFiniteQuotients R]
variable [AddCommGroup M] [Module R M] [Module.Finite R M]
variable (e : K ⊗[R] M ≃ₗ[K] K) (p : IsDedekindDomain.HeightOneSpectrum R)

/-- The coefficient-weighted adic seminorm in a supplied rational frame.
It is obtained by scalar extension from the fibre over the fraction field tagged
with its adic absolute value. -/
noncomputable def adicSeminorm :
    Seminorm (p.adicCompletion K) (p.adicCompletion K ⊗[R] M) :=
  let A := WithAbs (NumberField.HeightOneSpectrum.adicAbv K p)
  let F := p.adicCompletion K
  letI : Module.Invertible A (A ⊗[R] M) :=
    Module.Invertible.congr (e.fibreCoordinate A).symm
  let c : ℝ≥0 := NNReal.mk ((Ideal.absNorm p.asIdeal : ℝ) ^
    FractionalIdeal.count K p e.coefficientIdeal)
    (zpow_nonneg (Nat.cast_nonneg _) _)
  let s : Seminorm A (A ⊗[R] M) :=
    c • (normSeminorm A A).comp (e.fibreCoordinate A).toLinearMap
  (s.extendScalarsRankOne F).comp
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R A F F M).symm.toLinearMap

/-- Evaluation of the adic seminorm is the coordinate norm times the positive
coefficient-ideal weight. This formula holds on the whole adic fibre. -/
theorem adicSeminorm_apply (x : p.adicCompletion K ⊗[R] M) :
    e.adicSeminorm p x = (Ideal.absNorm p.asIdeal : ℝ) ^
      FractionalIdeal.count K p e.coefficientIdeal *
        ‖e.fibreCoordinate (p.adicCompletion K) x‖ := by
  let A := WithAbs (NumberField.HeightOneSpectrum.adicAbv K p)
  let F := p.adicCompletion K
  let : Module.Invertible A (A ⊗[R] M) :=
    Module.Invertible.congr (e.fibreCoordinate A).symm
  let c : ℝ≥0 := NNReal.mk ((Ideal.absNorm p.asIdeal : ℝ) ^
    FractionalIdeal.count K p e.coefficientIdeal)
    (zpow_nonneg (Nat.cast_nonneg _) _)
  let s : Seminorm A (A ⊗[R] M) :=
    c • (normSeminorm A A).comp (e.fibreCoordinate A).toLinearMap
  have hs (y : A ⊗[R] M) :
      s y = (c : ℝ) * ‖e.fibreCoordinate A y‖ := rfl
  change s.extendScalarsRankOne F
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange R A F F M).symm x) = _
  -- The algebraic and normed-field instance paths on `WithAbs` agree definitionally.
  erw [Seminorm.extendScalarsRankOne_apply F s (e.fibreCoordinate A)]
  change s ((e.fibreCoordinate A).symm 1) *
    ‖(e.fibreCoordinate A).scalarExtensionCoordinate F
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange R A F F M).symm x)‖ = _
  rw [fibreCoordinate_scalarExtensionCoordinate_apply, apply_symm_apply]
  -- Evaluate across the definitionally equal `WithAbs` instance paths.
  erw [hs, apply_symm_apply, norm_one, mul_one]
  simp only [c, NNReal.coe_mk]
  -- Normalize the completion-field superclass paths exposed by the coordinate API.
  with_unfolding_all rfl

/-- Changing the rational frame does not change the adic seminorm. -/
theorem adicSeminorm_eq (e' : K ⊗[R] M ≃ₗ[K] K) :
    e'.adicSeminorm p = e.adicSeminorm p := by
  have ha : e' (e.symm (1 : K)) ≠ 0 := by
    intro h
    have hunit : e.symm (1 : K) = 0 := e'.injective (by simpa only [map_zero] using h)
    exact one_ne_zero (by simpa only [apply_symm_apply, map_zero] using congrArg e hunit)
  have hq : (Ideal.absNorm p.asIdeal : ℝ) ≠ 0 := by
    exact_mod_cast NumberField.HeightOneSpectrum.absNorm_ne_zero p
  apply Seminorm.ext
  intro x
  rw [adicSeminorm_apply, adicSeminorm_apply,
    e.coefficientIdeal_eq_spanSingleton_mul e',
    FractionalIdeal.count_mul K p (FractionalIdeal.spanSingleton_ne_zero_iff.mpr ha)
      e.coefficientIdeal_ne_zero,
    zpow_add₀ hq, e.fibreCoordinate_change (p.adicCompletion K) e', norm_mul]
  calc
    _ = ((Ideal.absNorm p.asIdeal : ℝ) ^
        FractionalIdeal.count K p (FractionalIdeal.spanSingleton R⁰ (e' (e.symm 1))) *
        ‖algebraMap K (p.adicCompletion K) (e' (e.symm 1))‖) *
      ((Ideal.absNorm p.asIdeal : ℝ) ^ FractionalIdeal.count K p e.coefficientIdeal *
        ‖e.fibreCoordinate (p.adicCompletion K) x‖) := by ring
    _ = _ := by
      rw [p.zpow_count_spanSingleton_mul_norm_algebraMap_eq_one _ ha, one_mul]

/-- The adic seminorm in a rational frame is definite. -/
@[simp]
theorem adicSeminorm_eq_zero_iff (x : p.adicCompletion K ⊗[R] M) :
    e.adicSeminorm p x = 0 ↔ x = 0 := by
  have hq : (Ideal.absNorm p.asIdeal : ℝ) ≠ 0 := by
    exact_mod_cast NumberField.HeightOneSpectrum.absNorm_ne_zero p
  rw [adicSeminorm_apply, mul_eq_zero, norm_eq_zero]
  simp only [zpow_ne_zero _ hq, false_or, map_eq_zero_iff]

/-- The adic seminorm satisfies the ultrametric triangle inequality. -/
theorem adicSeminorm_add_le_max (x y : p.adicCompletion K ⊗[R] M) :
    e.adicSeminorm p (x + y) ≤ max (e.adicSeminorm p x) (e.adicSeminorm p y) := by
  rw [adicSeminorm_apply, adicSeminorm_apply, adicSeminorm_apply, map_add]
  calc
    _ ≤ (Ideal.absNorm p.asIdeal : ℝ) ^ FractionalIdeal.count K p e.coefficientIdeal *
        max ‖e.fibreCoordinate (p.adicCompletion K) x‖
          ‖e.fibreCoordinate (p.adicCompletion K) y‖ :=
      mul_le_mul_of_nonneg_left (IsUltrametricDist.norm_add_le_max _ _)
        (zpow_nonneg (Nat.cast_nonneg _) _)
    _ = _ := mul_max_of_nonneg _ _ (zpow_nonneg (Nat.cast_nonneg _) _)

/-- The weight at the rational unit vector characterizes the entire seminorm. -/
theorem adicSeminorm_unique
    (N : Seminorm (p.adicCompletion K) (p.adicCompletion K ⊗[R] M))
    (h : N (TensorProduct.AlgebraTensorModule.map (Algebra.linearMap K (p.adicCompletion K))
      (LinearMap.id : M →ₗ[R] M) (e.symm 1)) =
        (Ideal.absNorm p.asIdeal : ℝ) ^ FractionalIdeal.count K p e.coefficientIdeal) :
    N = e.adicSeminorm p := by
  apply Seminorm.ext
  intro x
  rw [adicSeminorm_apply]
  conv_lhs => rw [e.eq_fibreCoordinate_smul (p.adicCompletion K) x]
  rw [map_smul_eq_mul, h, mul_comm]

/-- On the scalar module, the adic seminorm is the selected completion norm
pulled back along the tensor right-unit equivalence. -/
@[simp]
theorem adicSeminorm_rid :
    (TensorProduct.AlgebraTensorModule.rid R K K).adicSeminorm p =
      (normSeminorm (p.adicCompletion K) (p.adicCompletion K)).comp
        (TensorProduct.AlgebraTensorModule.rid R (p.adicCompletion K)
          (p.adicCompletion K)).toLinearMap := by
  apply Seminorm.ext
  intro x
  rw [adicSeminorm_apply]
  simp only [coefficientIdeal_rid, FractionalIdeal.count_one, zpow_zero,
    fibreCoordinate_rid, one_mul]
  rfl

end LinearEquiv

namespace Module

variable {R : Type u} {K : Type v} (M : Type w)
variable [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
variable [Infinite R] [Ring.HasFiniteQuotients R]
variable [AddCommGroup M] [Module R M] [Module.Invertible R M]
variable (p : IsDedekindDomain.HeightOneSpectrum R)

/-- The lattice-normalized adic seminorm of an invertible module. Base change
preserves invertibility, and the resulting line over the fraction field is free;
any rational frame therefore supplies this frame-independent seminorm. -/
noncomputable def adicSeminorm :
    Seminorm (p.adicCompletion K) (p.adicCompletion K ⊗[R] M) :=
  let e : K ⊗[R] M ≃ₗ[K] K :=
    (Module.Invertible.free_iff_linearEquiv.mp
      (inferInstance : Module.Free K (K ⊗[R] M))).some
  e.adicSeminorm p

variable {M}

/-- The canonical seminorm agrees with the construction in every supplied frame. -/
theorem adicSeminorm_eq (e : K ⊗[R] M ≃ₗ[K] K) :
    adicSeminorm (K := K) M p = e.adicSeminorm p := by
  unfold adicSeminorm
  exact e.adicSeminorm_eq p _

/-- Evaluation of the canonical seminorm in any rational frame. -/
theorem adicSeminorm_apply (e : K ⊗[R] M ≃ₗ[K] K)
    (x : p.adicCompletion K ⊗[R] M) :
    adicSeminorm (K := K) M p x = (Ideal.absNorm p.asIdeal : ℝ) ^
      FractionalIdeal.count K p e.coefficientIdeal *
        ‖e.fibreCoordinate (p.adicCompletion K) x‖ := by
  rw [adicSeminorm_eq p e, e.adicSeminorm_apply]

/-- On the rational fibre, evaluation uses the residue-cardinality absolute value. -/
theorem adicSeminorm_apply_rationalFibre (e : K ⊗[R] M ≃ₗ[K] K) (x : K ⊗[R] M) :
    adicSeminorm (K := K) M p
      (TensorProduct.AlgebraTensorModule.map (Algebra.linearMap K (p.adicCompletion K))
        (LinearMap.id : M →ₗ[R] M) x) =
      (Ideal.absNorm p.asIdeal : ℝ) ^ FractionalIdeal.count K p e.coefficientIdeal *
        NumberField.HeightOneSpectrum.adicAbv K p (e x) := by
  rw [adicSeminorm_apply p e, e.fibreCoordinate_rationalFibre,
    p.norm_algebraMap_eq_adicAbv]

/-- Evaluation on a pure tensor in a rational frame. -/
theorem adicSeminorm_apply_tmul (e : K ⊗[R] M ≃ₗ[K] K)
    (a : p.adicCompletion K) (m : M) :
    adicSeminorm (K := K) M p (a ⊗ₜ[R] m) =
      (Ideal.absNorm p.asIdeal : ℝ) ^ FractionalIdeal.count K p e.coefficientIdeal *
        (‖a‖ * NumberField.HeightOneSpectrum.adicAbv K p (e.coefficientMap m)) := by
  rw [adicSeminorm_apply p e, e.fibreCoordinate_tmul, norm_mul,
    p.norm_algebraMap_eq_adicAbv]

/-- Evaluation at an integral section. -/
theorem adicSeminorm_apply_one_tmul (e : K ⊗[R] M ≃ₗ[K] K) (m : M) :
    adicSeminorm (K := K) M p ((1 : p.adicCompletion K) ⊗ₜ[R] m) =
      (Ideal.absNorm p.asIdeal : ℝ) ^ FractionalIdeal.count K p e.coefficientIdeal *
        NumberField.HeightOneSpectrum.adicAbv K p (e.coefficientMap m) := by
  rw [adicSeminorm_apply_tmul p e, norm_one, one_mul]

/-- The rational unit vector has seminorm equal to the coefficient-ideal weight. -/
@[simp]
theorem adicSeminorm_apply_unitVector (e : K ⊗[R] M ≃ₗ[K] K) :
    adicSeminorm (K := K) M p
      (TensorProduct.AlgebraTensorModule.map (Algebra.linearMap K (p.adicCompletion K))
        (LinearMap.id : M →ₗ[R] M) (e.symm 1)) =
      (Ideal.absNorm p.asIdeal : ℝ) ^ FractionalIdeal.count K p e.coefficientIdeal := by
  rw [adicSeminorm_apply_rationalFibre p e, e.apply_symm_apply, map_one, mul_one]

/-- Normalization at a rational unit vector characterizes the canonical seminorm. -/
theorem adicSeminorm_unique (e : K ⊗[R] M ≃ₗ[K] K)
    (N : Seminorm (p.adicCompletion K) (p.adicCompletion K ⊗[R] M))
    (h : N (TensorProduct.AlgebraTensorModule.map (Algebra.linearMap K (p.adicCompletion K))
      (LinearMap.id : M →ₗ[R] M) (e.symm 1)) =
        (Ideal.absNorm p.asIdeal : ℝ) ^ FractionalIdeal.count K p e.coefficientIdeal) :
    N = adicSeminorm (K := K) M p := by
  rw [adicSeminorm_eq p e]
  exact e.adicSeminorm_unique p N h

/-- The canonical adic seminorm is definite. -/
@[simp]
theorem adicSeminorm_eq_zero_iff (x : p.adicCompletion K ⊗[R] M) :
    adicSeminorm (K := K) M p x = 0 ↔ x = 0 := by
  obtain ⟨e⟩ := Module.Invertible.free_iff_linearEquiv.mp
    (inferInstance : Module.Free K (K ⊗[R] M))
  rw [adicSeminorm_eq p e, e.adicSeminorm_eq_zero_iff]

/-- The canonical adic seminorm satisfies the ultrametric triangle inequality. -/
theorem adicSeminorm_add_le_max (x y : p.adicCompletion K ⊗[R] M) :
    adicSeminorm (K := K) M p (x + y) ≤
      max (adicSeminorm (K := K) M p x) (adicSeminorm (K := K) M p y) := by
  obtain ⟨e⟩ := Module.Invertible.free_iff_linearEquiv.mp
    (inferInstance : Module.Free K (K ⊗[R] M))
  rw [adicSeminorm_eq p e]
  exact e.adicSeminorm_add_le_max p x y

/-- The canonical adic seminorm is nonnegative. -/
theorem adicSeminorm_nonneg (x : p.adicCompletion K ⊗[R] M) :
    0 ≤ adicSeminorm (K := K) M p x :=
  apply_nonneg _ _

/-- Homogeneity for scalars in the adic completion. -/
@[simp]
theorem adicSeminorm_smul (a : p.adicCompletion K) (x : p.adicCompletion K ⊗[R] M) :
    adicSeminorm (K := K) M p (a • x) = ‖a‖ * adicSeminorm (K := K) M p x :=
  map_smul_eq_mul _ _ _

/-- On the scalar module, the entire canonical seminorm is the selected completion
norm pulled back along the tensor right-unit equivalence. -/
@[simp]
theorem adicSeminorm_self :
    adicSeminorm (K := K) R p =
      (normSeminorm (p.adicCompletion K) (p.adicCompletion K)).comp
        (TensorProduct.AlgebraTensorModule.rid R (p.adicCompletion K)
          (p.adicCompletion K)).toLinearMap := by
  rw [adicSeminorm_eq p (TensorProduct.AlgebraTensorModule.rid R K K),
    LinearEquiv.adicSeminorm_rid]

/-- The integral unit in the scalar module has seminorm one. -/
theorem adicSeminorm_one_tmul_one :
    adicSeminorm (K := K) R p ((1 : p.adicCompletion K) ⊗ₜ[R] (1 : R)) = 1 := by
  rw [adicSeminorm_self]
  simp

/-- In every rational frame of the scalar module, the coefficient-ideal weight
cancels the coordinate norm at the same integral unit vector. -/
theorem adicSeminorm_fixed_unit (e : K ⊗[R] R ≃ₗ[K] K) :
    (Ideal.absNorm p.asIdeal : ℝ) ^ FractionalIdeal.count K p e.coefficientIdeal *
      ‖algebraMap K (p.adicCompletion K) (e.coefficientMap 1)‖ = 1 := by
  have h := adicSeminorm_apply p e
    ((1 : p.adicCompletion K) ⊗ₜ[R] (1 : R))
  rw [adicSeminorm_one_tmul_one] at h
  simpa only [LinearEquiv.fibreCoordinate_tmul, one_mul] using h.symm

end Module
