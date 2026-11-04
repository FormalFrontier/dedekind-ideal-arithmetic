/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances

/-!
# Isometric extensions between infinite-place completions

Mathlib's `NumberField.LiesOver.completionMap` extends the field algebra map
between completions at infinite places. This module supplies its computation
on the original field and preservation of the ordinary, unsquared norm.
The lower place may be taken to be `w.comap (algebraMap K L)`; no finiteness
or real-place hypothesis is required.

The map and its continuity are reused from Mathlib's
`NumberTheory/NumberField/Completion/LiesOverInstances.lean`, rather than
constructed through choices of complex embeddings.
-/

@[expose] public section

universe u v

namespace NumberField.InfinitePlace.Completion

section Extension

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (v : InfinitePlace K) (w : InfinitePlace L) [w.LiesOver v]

/-- The completion map extends the algebra map of the original fields, without
requiring a completion-algebra instance in the statement. -/
theorem completionMap_algebraMap (k : K) :
    NumberField.LiesOver.completionMap (v := v) (w := w)
        (algebraMap K v.Completion k) =
      algebraMap L w.Completion (algebraMap K L k) := by
  change NumberField.LiesOver.completionMap
      ((WithAbs.toAbs v.1 k : WithAbs v.1) : v.Completion) = _
  rw [NumberField.LiesOver.completionMap_coe]
  apply ext
  rw [algebraMap_toCompletion, UniformSpace.Completion.algebraMap_def]
  simp [WithAbs.algebraMap_left_apply, WithAbs.algebraMap_right_apply]

/-- The completion map preserves the ordinary completion norm. -/
@[simp]
theorem norm_completionMap (x : v.Completion) :
    ‖NumberField.LiesOver.completionMap (v := v) (w := w) x‖ = ‖x‖ := by
  refine induction_on v x ?_ ?_
  · exact isClosed_eq
      (continuous_norm.comp NumberField.LiesOver.continuous_completionMap) continuous_norm
  · intro a
    rw [NumberField.LiesOver.completionMap_coe, norm_coe, norm_coe]
    exact comp_of_comap_eq (InfinitePlace.LiesOver.comap_eq w v) a.ofAbs

/-- Extension to infinite-place completions is an isometry. -/
theorem isometry_completionMap :
    Isometry (NumberField.LiesOver.completionMap (v := v) (w := w)) :=
  AddMonoidHomClass.isometry_of_norm _ (norm_completionMap v w)

end Extension

/-- Extending the identity field map, with its canonical self-algebra structure,
gives the identity on the completion. -/
@[simp]
theorem completionMap_self {K : Type u} [Field K] (v : InfinitePlace K) :
    @NumberField.LiesOver.completionMap K K _ _ (Algebra.id K) v v
      ⟨by ext x; simp [AbsoluteValue.under_def]⟩ = RingHom.id v.Completion := by
  have : v.LiesOver v := ⟨by ext x; simp [AbsoluteValue.under_def]⟩
  apply RingHom.ext
  intro x
  refine induction_on v x
    (isClosed_eq NumberField.LiesOver.continuous_completionMap continuous_id) ?_
  intro a
  change NumberField.LiesOver.completionMap
      (algebraMap K v.Completion a.ofAbs) = algebraMap K v.Completion a.ofAbs
  simpa only [Algebra.algebraMap_self, RingHom.id_apply] using
    completionMap_algebraMap v v a.ofAbs

end NumberField.InfinitePlace.Completion
