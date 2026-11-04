/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.PicardGroup

/-!
# Indices of sections of modules

An injective linear map relates the index of a submodule to the index of its
image and the index of its range. Applied to the map `r ↦ r • m`, this gives
the scalar law for the index of a nonzero section of a torsion-free module.
No finiteness assumption on either quotient, or nonvanishing assumption on
the scalar, is needed for this law.

An invertible module over a domain admits an embedding into the ring through
an ideal presentation. Over a ring with finite quotients, this proves that
the quotient by the span of a nonzero section is finite. The same presentation
also gives a common nonzero scalar multiple of any two nonzero sections.
-/

@[expose] public section

namespace Submodule

section Ring

variable {R M N : Type*} [Ring R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The index of an image under an injective linear map is the product of the
index in the source and the index of the range. -/
theorem cardQuot_map_of_injective (f : M →ₗ[R] N) (hf : Function.Injective f)
    (p : Submodule R M) :
    (p.map f).cardQuot = p.cardQuot * (LinearMap.range f).cardQuot := by
  exact AddSubgroup.index_map_of_injective (H := p.toAddSubgroup)
    (f := f.toAddMonoidHom) hf

/-- Multiplying a nonzero section of a torsion-free module by a scalar
multiplies its index by the index of the principal left ideal of the scalar.
This also holds for the zero scalar and for infinite quotients, whose indices
are defined to be zero. -/
theorem cardQuot_span_singleton_smul [IsDomain R] [Module.IsTorsionFree R M]
    {m : M} (hm : m ≠ 0) (r : R) :
    (span R {r • m}).cardQuot = (span R {r}).cardQuot * (span R {m}).cardQuot := by
  simpa only [← span_image, Set.image_singleton, LinearMap.toSpanSingleton_apply,
    LinearMap.range_toSpanSingleton] using
    cardQuot_map_of_injective (LinearMap.toSpanSingleton R M m)
      (smul_left_injective R hm) (span R {r})

end Ring

/-- Over an infinite Dedekind domain, the scalar factor in the index of a
section is the absolute norm of the principal ideal of the scalar. -/
theorem cardQuot_span_singleton_smul_eq_absNorm_mul
    {R M : Type*} [CommRing R] [IsDedekindDomain R] [Infinite R]
    [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M]
    {m : M} (hm : m ≠ 0) (r : R) :
    (span R {r • m}).cardQuot =
      Ideal.absNorm (Ideal.span {r}) * (span R {m}).cardQuot :=
  cardQuot_span_singleton_smul hm r

end Submodule

namespace Module.Invertible

variable {R M : Type*} [CommRing R] [IsDomain R]
variable [AddCommGroup M] [Module R M] [Module.Invertible R M]

/-- Over a domain with finite quotients, the quotient of an invertible module
by the span of a nonzero section is finite. -/
theorem finite_quotient_span_singleton [Ring.HasFiniteQuotients R]
    {m : M} (hm : m ≠ 0) : Finite (M ⧸ Submodule.span R {m}) := by
  obtain ⟨I, ⟨e⟩⟩ := exists_linearEquiv_ideal R M
  let f : M →ₗ[R] R := I.subtype.comp e.toLinearMap
  have hf : Function.Injective f := I.subtype_injective.comp e.injective
  have hfm : f m ≠ 0 := by
    intro h
    exact hm (hf (by simpa only [map_zero] using h))
  let : Finite (R ⧸ Ideal.span {f m}) :=
    Ring.HasFiniteQuotients.finiteQuotient (mt Ideal.span_singleton_eq_bot.mp hfm)
  have hmap : (Submodule.span R {m}).map f = Submodule.span R {f m} := by
    simp only [← Submodule.span_image, Set.image_singleton]
  apply Nat.finite_of_card_ne_zero
  change (Submodule.span R {m}).cardQuot ≠ 0
  intro hzero
  have hzero' : (Submodule.span R {f m}).cardQuot = 0 := by
    rw [← hmap, Submodule.cardQuot_map_of_injective f hf, hzero, zero_mul]
  exact (Nat.card_pos.ne' : Nat.card (R ⧸ Ideal.span {f m}) ≠ 0) hzero'

/-- Two nonzero sections of an invertible module over a domain have a common
nonzero scalar multiple. -/
theorem exists_nonzero_smul_eq {m n : M} (hm : m ≠ 0) (hn : n ≠ 0) :
    ∃ r s : R, r ≠ 0 ∧ s ≠ 0 ∧ r • m = s • n := by
  obtain ⟨I, ⟨e⟩⟩ := exists_linearEquiv_ideal R M
  let f : M →ₗ[R] R := I.subtype.comp e.toLinearMap
  have hf : Function.Injective f := I.subtype_injective.comp e.injective
  have hfm : f m ≠ 0 := by
    intro h
    exact hm (hf (by simpa only [map_zero] using h))
  have hfn : f n ≠ 0 := by
    intro h
    exact hn (hf (by simpa only [map_zero] using h))
  refine ⟨f n, f m, hfn, hfm, hf ?_⟩
  simp only [map_smul, smul_eq_mul, mul_comm]

end Module.Invertible
