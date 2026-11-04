/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import DedekindIdealArithmetic.NumberField.ModuleHeight
import Mathlib.Tactic.Ring

/-!
# Tensor products of archimedean norms

The tensor metric is defined on the integral tensor product. At each
infinite place, field-linear coordinates on the two rank-one fibres give a
coordinate on the tensor fibre through the base-change equivalence.
The ordinary completion norm is scaled by the product of the norms of the two
coordinate generators.

Only the field fibres are trivialized: the integral modules need not be free.
Norms remain explicit seminorm data, with no norm instances on the modules or
their fibres. The construction uses Mathlib's invertible-module, tensor-product
and seminorm APIs.

## References

* J. S. Milne, *Abelian Varieties*, IV §6.
-/

@[expose] public section

open scoped NNReal NumberField TensorProduct

universe u w z

namespace NumberField

variable {K : Type u} [Field K]
variable (M : Type w) [AddCommGroup M] [Module (𝓞 K) M]
variable (N : Type z) [AddCommGroup N] [Module (𝓞 K) N]

namespace InfinitePlace

/-- The canonical comparison from the tensor of the fibres to the fibre of the tensor. -/
noncomputable def tensorFibreEquiv (v : InfinitePlace K) :
    (v.Completion ⊗[𝓞 K] M) ⊗[v.Completion] (v.Completion ⊗[𝓞 K] N) ≃ₗ[v.Completion]
      v.Completion ⊗[𝓞 K] (M ⊗[𝓞 K] N) :=
  (TensorProduct.AlgebraTensorModule.distribBaseChange (𝓞 K) v.Completion M N).symm

/-- The fibre comparison multiplies the completion scalars of two elementary tensors. -/
@[simp]
theorem tensorFibreEquiv_tmul (v : InfinitePlace K) (m : M) (n : N)
    (a b : v.Completion) :
    tensorFibreEquiv M N v ((a ⊗ₜ[𝓞 K] m) ⊗ₜ[v.Completion] (b ⊗ₜ[𝓞 K] n)) =
      (a * b) ⊗ₜ[𝓞 K] (m ⊗ₜ[𝓞 K] n) := by
  simp only [tensorFibreEquiv, TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul]

end InfinitePlace

namespace ArchimedeanNorms

variable {M N}

private theorem generator_norm_pos (P : ArchimedeanNorms K M) (v : InfinitePlace K)
    (e : (v.Completion ⊗[𝓞 K] M) ≃ₗ[v.Completion] v.Completion) :
    0 < P.apply v (e.symm 1) := by
  have he : e.symm 1 ≠ 0 := by
    intro h
    apply (one_ne_zero : (1 : v.Completion) ≠ 0)
    simpa only [LinearEquiv.apply_symm_apply, map_zero] using congrArg e h
  have hne : P.apply v (e.symm 1) ≠ 0 := by
    intro h
    exact he (P.eq_zero_of_map_eq_zero v _ h)
  exact lt_of_le_of_ne (P.apply_nonneg v _) hne.symm

variable [Module.Invertible (𝓞 K) M] [Module.Invertible (𝓞 K) N]

/-- The induced archimedean norms on the tensor product of two invertible integral modules. -/
noncomputable def tensor (P : ArchimedeanNorms K M) (Q : ArchimedeanNorms K N) :
    ArchimedeanNorms K (M ⊗[𝓞 K] N) :=
  let eM (v : InfinitePlace K) :
      (v.Completion ⊗[𝓞 K] M) ≃ₗ[v.Completion] v.Completion :=
    (Module.Invertible.free_iff_linearEquiv.mp
      (inferInstance : Module.Free v.Completion (v.Completion ⊗[𝓞 K] M))).some
  let eN (v : InfinitePlace K) :
      (v.Completion ⊗[𝓞 K] N) ≃ₗ[v.Completion] v.Completion :=
    (Module.Invertible.free_iff_linearEquiv.mp
      (inferInstance : Module.Free v.Completion (v.Completion ⊗[𝓞 K] N))).some
  let e (v : InfinitePlace K) :
      (v.Completion ⊗[𝓞 K] (M ⊗[𝓞 K] N)) ≃ₗ[v.Completion] v.Completion :=
    (InfinitePlace.tensorFibreEquiv M N v).symm ≪≫ₗ
      TensorProduct.congr (eM v) (eN v) ≪≫ₗ TensorProduct.lid v.Completion v.Completion
  { seminorm v :=
      let c : ℝ≥0 :=
        ⟨P.apply v ((eM v).symm 1) * Q.apply v ((eN v).symm 1),
          mul_nonneg (P.apply_nonneg v _) (Q.apply_nonneg v _)⟩
      c • (normSeminorm v.Completion v.Completion).comp (e v).toLinearMap
    eq_zero_of_map_eq_zero v x h := by
      change (P.apply v ((eM v).symm 1) * Q.apply v ((eN v).symm 1)) * ‖e v x‖ = 0 at h
      have hs : P.apply v ((eM v).symm 1) * Q.apply v ((eN v).symm 1) ≠ 0 :=
        (mul_pos (generator_norm_pos P v (eM v)) (generator_norm_pos Q v (eN v))).ne'
      have hx : e v x = 0 := norm_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hs)
      apply (e v).injective
      simpa only [map_zero] using hx }

/-- Evaluation of the tensor metric in the chosen field-fibre coordinates. -/
theorem tensor_apply (P : ArchimedeanNorms K M) (Q : ArchimedeanNorms K N)
    (v : InfinitePlace K) (x : v.Completion ⊗[𝓞 K] (M ⊗[𝓞 K] N)) :
    let eM : (v.Completion ⊗[𝓞 K] M) ≃ₗ[v.Completion] v.Completion :=
      (Module.Invertible.free_iff_linearEquiv.mp
        (inferInstance : Module.Free v.Completion (v.Completion ⊗[𝓞 K] M))).some
    let eN : (v.Completion ⊗[𝓞 K] N) ≃ₗ[v.Completion] v.Completion :=
      (Module.Invertible.free_iff_linearEquiv.mp
        (inferInstance : Module.Free v.Completion (v.Completion ⊗[𝓞 K] N))).some
    (P.tensor Q).apply v x =
      (P.apply v (eM.symm 1) * Q.apply v (eN.symm 1)) *
        ‖((InfinitePlace.tensorFibreEquiv M N v).symm ≪≫ₗ
          TensorProduct.congr eM eN ≪≫ₗ TensorProduct.lid v.Completion v.Completion) x‖ :=
  rfl

/-- The tensor metric has a nonzero vector of strictly positive norm in every fibre. -/
theorem tensor_exists_nonzero (P : ArchimedeanNorms K M) (Q : ArchimedeanNorms K N)
    (v : InfinitePlace K) :
    ∃ x : v.Completion ⊗[𝓞 K] (M ⊗[𝓞 K] N), x ≠ 0 ∧ 0 < (P.tensor Q).apply v x := by
  let eM : (v.Completion ⊗[𝓞 K] M) ≃ₗ[v.Completion] v.Completion :=
    (Module.Invertible.free_iff_linearEquiv.mp
      (inferInstance : Module.Free v.Completion (v.Completion ⊗[𝓞 K] M))).some
  let eN : (v.Completion ⊗[𝓞 K] N) ≃ₗ[v.Completion] v.Completion :=
    (Module.Invertible.free_iff_linearEquiv.mp
      (inferInstance : Module.Free v.Completion (v.Completion ⊗[𝓞 K] N))).some
  let x := InfinitePlace.tensorFibreEquiv M N v (eM.symm 1 ⊗ₜ[v.Completion] eN.symm 1)
  have heval : (P.tensor Q).apply v x = P.apply v (eM.symm 1) * Q.apply v (eN.symm 1) := by
    rw [tensor_apply]
    change (P.apply v (eM.symm 1) * Q.apply v (eN.symm 1)) *
      ‖((InfinitePlace.tensorFibreEquiv M N v).symm ≪≫ₗ
        TensorProduct.congr eM eN ≪≫ₗ TensorProduct.lid v.Completion v.Completion) x‖ = _
    simp only [x, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
      TensorProduct.congr_tmul, LinearEquiv.apply_symm_apply, TensorProduct.lid_tmul,
      one_smul, norm_one, mul_one]
  have hpos : 0 < (P.tensor Q).apply v x := by
    rw [heval]
    exact mul_pos (generator_norm_pos P v eM) (generator_norm_pos Q v eN)
  refine ⟨x, ?_, hpos⟩
  intro hx
  rw [hx, apply_zero] at hpos
  exact (lt_irrefl 0) hpos

/-- The tensor metric on arbitrary pure tensors of completion-fibre vectors. -/
theorem tensor_apply_tmul (P : ArchimedeanNorms K M) (Q : ArchimedeanNorms K N)
    (v : InfinitePlace K) (x : v.Completion ⊗[𝓞 K] M) (y : v.Completion ⊗[𝓞 K] N) :
    (P.tensor Q).apply v (InfinitePlace.tensorFibreEquiv M N v (x ⊗ₜ[v.Completion] y)) =
      P.apply v x * Q.apply v y := by
  let eM : (v.Completion ⊗[𝓞 K] M) ≃ₗ[v.Completion] v.Completion :=
    (Module.Invertible.free_iff_linearEquiv.mp
      (inferInstance : Module.Free v.Completion (v.Completion ⊗[𝓞 K] M))).some
  let eN : (v.Completion ⊗[𝓞 K] N) ≃ₗ[v.Completion] v.Completion :=
    (Module.Invertible.free_iff_linearEquiv.mp
      (inferInstance : Module.Free v.Completion (v.Completion ⊗[𝓞 K] N))).some
  have hx : x = eM x • eM.symm 1 := by
    apply eM.injective
    simp only [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  have hy : y = eN y • eN.symm 1 := by
    apply eN.injective
    simp only [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  have hP : P.apply v x = ‖eM x‖ * P.apply v (eM.symm 1) := by
    calc
      P.apply v x = P.apply v (eM x • eM.symm 1) := congrArg (P.apply v) hx
      _ = _ := P.apply_smul v _ _
  have hQ : Q.apply v y = ‖eN y‖ * Q.apply v (eN.symm 1) := by
    calc
      Q.apply v y = Q.apply v (eN y • eN.symm 1) := congrArg (Q.apply v) hy
      _ = _ := Q.apply_smul v _ _
  rw [tensor_apply]
  change (P.apply v (eM.symm 1) * Q.apply v (eN.symm 1)) *
    ‖((InfinitePlace.tensorFibreEquiv M N v).symm ≪≫ₗ
      TensorProduct.congr eM eN ≪≫ₗ TensorProduct.lid v.Completion v.Completion)
        (InfinitePlace.tensorFibreEquiv M N v (x ⊗ₜ[v.Completion] y))‖ = _
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    TensorProduct.congr_tmul, TensorProduct.lid_tmul, smul_eq_mul, norm_mul]
  rw [hP, hQ]
  ring

/-- The tensor metric is multiplicative on the images of integral pure tensors in a fibre. -/
theorem tensor_apply_one_tmul (P : ArchimedeanNorms K M) (Q : ArchimedeanNorms K N)
    (v : InfinitePlace K) (m : M) (n : N) :
    (P.tensor Q).apply v ((1 : v.Completion) ⊗ₜ[𝓞 K] (m ⊗ₜ[𝓞 K] n)) =
      P.apply v ((1 : v.Completion) ⊗ₜ[𝓞 K] m) *
        Q.apply v ((1 : v.Completion) ⊗ₜ[𝓞 K] n) := by
  simpa only [InfinitePlace.tensorFibreEquiv_tmul, one_mul] using
    P.tensor_apply_tmul Q v ((1 : v.Completion) ⊗ₜ[𝓞 K] m)
      ((1 : v.Completion) ⊗ₜ[𝓞 K] n)

variable [NumberField K]

/-- The weighted norm product is multiplicative on integral pure tensors. -/
theorem normProduct_tensor_tmul (P : ArchimedeanNorms K M) (Q : ArchimedeanNorms K N)
    (m : M) (n : N) :
    (P.tensor Q).normProduct (m ⊗ₜ[𝓞 K] n) = P.normProduct m * Q.normProduct n := by
  simp_rw [normProduct_apply, tensor_apply_one_tmul, mul_pow]
  rw [Finset.prod_mul_distrib]

/-- The normed-module height of Milne, *Abelian Varieties*, IV §6,
is multiplicative for the tensor metric. -/
theorem height_tensor (P : ArchimedeanNorms K M) (Q : ArchimedeanNorms K N) :
    (P.tensor Q).height = P.height * Q.height := by
  let : Nontrivial (M → M) :=
    (smul_left_injective' (M := 𝓞 K) (α := M)).nontrivial
  let : Nontrivial M := Function.nontrivial_of_nontrivial M M
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  let : Nontrivial (N → N) :=
    (smul_left_injective' (M := 𝓞 K) (α := N)).nontrivial
  let : Nontrivial N := Function.nontrivial_of_nontrivial N N
  obtain ⟨n, hn⟩ := exists_ne (0 : N)
  have hmn : m ⊗ₜ[𝓞 K] n ≠ 0 := by
    let f : 𝓞 K →ₗ[𝓞 K] M := LinearMap.toSpanSingleton (𝓞 K) M m
    have hf : Function.Injective f := smul_left_injective (𝓞 K) hm
    have htf := Module.Flat.rTensor_preserves_injective_linearMap (M := N) f hf
    intro hz
    have hunit : (1 : 𝓞 K) ⊗ₜ[𝓞 K] n = 0 := htf (by
      simpa only [LinearMap.rTensor_tmul, f, LinearMap.toSpanSingleton_apply,
        one_smul, map_zero] using hz)
    apply hn
    simpa only [TensorProduct.lid_tmul, one_smul, map_zero] using
      congrArg (TensorProduct.lid (𝓞 K) N) hunit
  rw [(P.tensor Q).height_eq hmn, P.height_eq hm, Q.height_eq hn,
    ← (P.tensor Q).normProduct_apply (m ⊗ₜ[𝓞 K] n),
    ← P.normProduct_apply m, ← Q.normProduct_apply n,
    Module.Invertible.cardQuot_span_singleton_tmul (R := 𝓞 K) hm hn,
    normProduct_tensor_tmul, Nat.cast_mul]
  exact (div_mul_div_comm _ _ _ _).symm

/-- The normalized logarithmic normed-module height of Milne, *Abelian Varieties*, IV §6,
is additive for the tensor metric. -/
theorem normalizedLogHeight_tensor (P : ArchimedeanNorms K M) (Q : ArchimedeanNorms K N) :
    (P.tensor Q).normalizedLogHeight = P.normalizedLogHeight + Q.normalizedLogHeight := by
  simp only [normalizedLogHeight_def, height_tensor,
    Real.log_mul (P.height_pos).ne' (Q.height_pos).ne', add_div]

end ArchimedeanNorms

end NumberField
