/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import DedekindIdealArithmetic.NumberField.ModuleHeight

/-!
# Pullback of archimedean metrics

A module equivalence induces a completion-linear equivalence on every
archimedean fibre. Pulling back definite seminorms along these equivalences
gives `ArchimedeanNorms.comap`, without requiring either module to be
invertible or installing norm instances on the fibres.

Pullback is contravariant and preserves the weighted norm product of a
section. For invertible modules, the corresponding height statements express
isometry invariance using the pulled-back norm data.

## References

* J. S. Milne, *Abelian Varieties*, IV §6, normed-module heights.
-/

@[expose] public section

open scoped NumberField TensorProduct

universe u w₁ w₂ w₃

namespace NumberField
namespace ArchimedeanNorms

variable {K : Type u} [Field K]
variable {M : Type w₁} [AddCommGroup M] [Module (𝓞 K) M]
variable {N : Type w₂} [AddCommGroup N] [Module (𝓞 K) N]
variable {L : Type w₃} [AddCommGroup L] [Module (𝓞 K) L]

/-- Pull back archimedean norms along a module equivalence, using its
completion-linear base change on each entire fibre. -/
noncomputable def comap (Q : ArchimedeanNorms K N) (e : M ≃ₗ[𝓞 K] N) :
    ArchimedeanNorms K M where
  seminorm v := (Q.seminorm v).comp
    (e.baseChange (𝓞 K) v.Completion M N).toLinearMap
  eq_zero_of_map_eq_zero v x h := by
    apply (e.baseChange (𝓞 K) v.Completion M N).injective
    simpa only [map_zero] using
      Q.eq_zero_of_map_eq_zero v ((e.baseChange (𝓞 K) v.Completion M N) x) h

/-- A pulled-back norm evaluates the target norm on the base-changed vector. -/
@[simp]
theorem comap_apply (Q : ArchimedeanNorms K N) (e : M ≃ₗ[𝓞 K] N)
    (v : InfinitePlace K) (x : v.Completion ⊗[𝓞 K] M) :
    (Q.comap e).apply v x = Q.apply v ((e.baseChange (𝓞 K) v.Completion M N) x) :=
  rfl

/-- On a pure tensor, metric pullback applies the original module equivalence
to the second tensor factor. -/
theorem comap_apply_tmul (Q : ArchimedeanNorms K N) (e : M ≃ₗ[𝓞 K] N)
    (v : InfinitePlace K) (a : v.Completion) (m : M) :
    (Q.comap e).apply v (a ⊗ₜ[𝓞 K] m) = Q.apply v (a ⊗ₜ[𝓞 K] e m) := by
  rw [comap_apply, LinearEquiv.baseChange_tmul]

/-- Pullback along the identity leaves the metric unchanged. -/
@[simp]
theorem comap_refl (P : ArchimedeanNorms K M) :
    P.comap (LinearEquiv.refl (𝓞 K) M) = P := by
  apply ext
  intro v x
  rw [comap_apply]
  change P.apply v (((1 : M ≃ₗ[𝓞 K] M).baseChange (𝓞 K) v.Completion M M) x) =
    P.apply v x
  rw [LinearEquiv.baseChange_one]
  rfl

/-- Pullback reverses composition of module equivalences. -/
theorem comap_trans (Q : ArchimedeanNorms K L)
    (e : M ≃ₗ[𝓞 K] N) (f : N ≃ₗ[𝓞 K] L) :
    Q.comap (e.trans f) = (Q.comap f).comap e := by
  apply ext
  intro v x
  simp only [comap_apply, LinearEquiv.baseChange_trans, LinearEquiv.trans_apply]

/-- Transporting the standard unit metric along an integral trivialization
assigns norm one to the section corresponding to the integral unit. -/
theorem unit_comap_apply_one_tmul_symm_one (e : M ≃ₗ[𝓞 K] 𝓞 K)
    (v : InfinitePlace K) :
    ((unit K).comap e).apply v
      ((1 : v.Completion) ⊗ₜ[𝓞 K] e.symm (1 : 𝓞 K)) = 1 := by
  rw [comap_apply_tmul, e.apply_symm_apply, unit_apply_one_tmul]

variable [NumberField K]

/-- Pulling back a metric preserves the weighted norm product of every
integral section, including the zero section. -/
@[simp]
theorem normProduct_comap (Q : ArchimedeanNorms K N) (e : M ≃ₗ[𝓞 K] N) (m : M) :
    (Q.comap e).normProduct m = Q.normProduct (e m) := by
  classical
  simp only [normProduct_apply, comap_apply_tmul]

/-- A module equivalence preserves the index/product evaluation at every
integral section when the source metric is pulled back from the target.
Neither invertibility nor finiteness of the section quotients is required. -/
theorem integralEvalHeight_comap (Q : ArchimedeanNorms K N)
    (e : M ≃ₗ[𝓞 K] N) (m : M) :
    (Q.comap e).integralEvalHeight m = Q.integralEvalHeight (e m) := by
  have hindex : (Submodule.span (𝓞 K) {e m}).cardQuot =
      (Submodule.span (𝓞 K) {m}).cardQuot := by
    simpa only [Submodule.map_span, Set.image_singleton, LinearEquiv.coe_coe,
      LinearEquiv.range, Submodule.cardQuot_top, mul_one] using
      Submodule.cardQuot_map_of_injective e.toLinearMap e.injective
        (Submodule.span (𝓞 K) {m})
  simp only [integralEvalHeight_apply, ← normProduct_apply, normProduct_comap, hindex]

/-- The normed-module height of Milne, *Abelian Varieties*, IV §6, is invariant
under a module equivalence equipped with the pulled-back archimedean norms. -/
theorem height_comap [Module.Invertible (𝓞 K) M] [Module.Invertible (𝓞 K) N]
    (Q : ArchimedeanNorms K N) (e : M ≃ₗ[𝓞 K] N) :
    (Q.comap e).height = Q.height := by
  let : Nontrivial (M → M) :=
    (smul_left_injective' (M := 𝓞 K) (α := M)).nontrivial
  let : Nontrivial M := Function.nontrivial_of_nontrivial M M
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  have hem : e m ≠ 0 := e.map_ne_zero_iff.mpr hm
  calc
    (Q.comap e).height = (Q.comap e).integralEvalHeight m :=
      (Q.comap e).height_eq hm
    _ = Q.integralEvalHeight (e m) := integralEvalHeight_comap Q e m
    _ = Q.height := (Q.height_eq hem).symm

/-- The normalized logarithmic normed-module height of Milne, *Abelian Varieties*, IV §6,
is invariant under a module equivalence equipped with the pulled-back norms. -/
theorem normalizedLogHeight_comap [Module.Invertible (𝓞 K) M]
    [Module.Invertible (𝓞 K) N] (Q : ArchimedeanNorms K N) (e : M ≃ₗ[𝓞 K] N) :
    (Q.comap e).normalizedLogHeight = Q.normalizedLogHeight := by
  simp only [normalizedLogHeight_def, height_comap]

end ArchimedeanNorms
end NumberField
