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
Over a Dedekind domain with finite quotients, the index of a nonzero pure
tensor is the product of the indices of its factors. This includes finite
fields: no assumption that the base ring is infinite is needed. The ideal
comparisons use Mathlib's invertible-module presentations and linear-disjointness
multiplication equivalences.
-/

@[expose] public section

open scoped TensorProduct

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

/-- Multiplicativity for nonzero ideals does not require the ring to be
infinite: over a finite domain both ideals are the unit ideal. -/
private theorem cardQuot_mul_of_ne_bot
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    (I J : Ideal R) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    (I * J).cardQuot = I.cardQuot * J.cardQuot := by
  cases finite_or_infinite R with
  | inl hR =>
    let : Finite R := hR
    let : IsSimpleOrder (Ideal R) :=
      Ring.isField_iff_isSimpleOrder_ideal.mp (Finite.isField_of_domain R)
    have hI' : I = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top I).resolve_left hI
    have hJ' : J = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top J).resolve_left hJ
    simp only [hI', hJ', Ideal.top_mul, cardQuot_top, mul_one]
  | inr hR =>
    let : Infinite R := hR
    exact _root_.cardQuot_mul I J

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

namespace Module.Invertible

variable {R M N : Type*} [CommRing R] [IsDedekindDomain R]
variable [Ring.HasFiniteQuotients R]
variable [AddCommGroup M] [Module R M] [Module.Invertible R M]
variable [AddCommGroup N] [Module R N] [Module.Invertible R N]

/-- Over a Dedekind domain with finite quotients, the index of the span of a
nonzero pure tensor in a tensor product of invertible modules is the product
of the indices of its factors. The modules need not be free, and the base
ring may be finite. -/
theorem cardQuot_span_singleton_tmul {m : M} {n : N} (hm : m ≠ 0) (hn : n ≠ 0) :
    (Submodule.span R {m ⊗ₜ[R] n}).cardQuot =
      (Submodule.span R {m}).cardQuot * (Submodule.span R {n}).cardQuot := by
  obtain ⟨I, ⟨eM⟩⟩ := exists_linearEquiv_ideal R M
  obtain ⟨J, ⟨eN⟩⟩ := exists_linearEquiv_ideal R N
  let f : M →ₗ[R] R := I.subtype.comp eM.toLinearMap
  let g : N →ₗ[R] R := J.subtype.comp eN.toLinearMap
  have hf : Function.Injective f := I.subtype_injective.comp eM.injective
  have hg : Function.Injective g := J.subtype_injective.comp eN.injective
  have hfm : f m ≠ 0 := by
    intro h
    exact hm (hf (by simpa only [map_zero] using h))
  have hgn : g n ≠ 0 := by
    intro h
    exact hn (hg (by simpa only [map_zero] using h))
  have hI : I ≠ ⊥ := by
    intro h
    apply hfm
    have hmem : f m ∈ I := (eM m).property
    simpa only [h, Submodule.mem_bot] using hmem
  have hJ : J ≠ ⊥ := by
    intro h
    apply hgn
    have hmem : g n ∈ J := (eN n).property
    simpa only [h, Submodule.mem_bot] using hmem
  let : Module.Flat R J := Module.Flat.of_linearEquiv eN.symm
  let e : M ⊗[R] N ≃ₗ[R] I * J :=
    TensorProduct.congr eM eN ≪≫ₗ
      (Submodule.LinearDisjoint.of_left_le_one_of_flat I J
        (le_top.trans Ideal.one_eq_top.ge)).mulMap
  let t : M ⊗[R] N →ₗ[R] R := (I * J).subtype.comp e.toLinearMap
  have ht : Function.Injective t := (I * J).subtype_injective.comp e.injective
  have ht_tmul : t (m ⊗ₜ[R] n) = f m * g n := by
    simp [t, e, f, g]
  have hf_range : LinearMap.range f = I := by
    simp only [f, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top,
      Submodule.range_subtype]
  have hg_range : LinearMap.range g = J := by
    simp only [g, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top,
      Submodule.range_subtype]
  have ht_range : LinearMap.range t = I * J := by
    simp only [t, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top,
      Submodule.range_subtype]
  have hM : (Ideal.span {f m}).cardQuot =
      (Submodule.span R {m}).cardQuot * I.cardQuot := by
    simpa only [← Submodule.span_image, Set.image_singleton, hf_range] using
      Submodule.cardQuot_map_of_injective f hf (Submodule.span R {m})
  have hN : (Ideal.span {g n}).cardQuot =
      (Submodule.span R {n}).cardQuot * J.cardQuot := by
    simpa only [← Submodule.span_image, Set.image_singleton, hg_range] using
      Submodule.cardQuot_map_of_injective g hg (Submodule.span R {n})
  have hT : (Ideal.span {f m * g n}).cardQuot =
      (Submodule.span R {m ⊗ₜ[R] n}).cardQuot * (I * J).cardQuot := by
    simpa only [← Submodule.span_image, Set.image_singleton, ht_tmul, ht_range] using
      Submodule.cardQuot_map_of_injective t ht (Submodule.span R {m ⊗ₜ[R] n})
  have hIJ := Submodule.cardQuot_mul_of_ne_bot I J hI hJ
  have hmul : (Ideal.span {f m * g n}).cardQuot =
      (Ideal.span {f m}).cardQuot * (Ideal.span {g n}).cardQuot := by
    rw [← Ideal.span_singleton_mul_span_singleton]
    exact Submodule.cardQuot_mul_of_ne_bot _ _
      (mt Ideal.span_singleton_eq_bot.mp hfm) (mt Ideal.span_singleton_eq_bot.mp hgn)
  apply mul_right_cancel₀
    (mul_ne_zero (Ring.HasFiniteQuotients.cardQuot_pos I hI).ne'
      (Ring.HasFiniteQuotients.cardQuot_pos J hJ).ne')
  calc
    (Submodule.span R {m ⊗ₜ[R] n}).cardQuot * (I.cardQuot * J.cardQuot) =
        (Ideal.span {f m * g n}).cardQuot := by rw [← hIJ, ← hT]
    _ = (Ideal.span {f m}).cardQuot * (Ideal.span {g n}).cardQuot := hmul
    _ = ((Submodule.span R {m}).cardQuot * I.cardQuot) *
        ((Submodule.span R {n}).cardQuot * J.cardQuot) := by rw [hM, hN]
    _ = ((Submodule.span R {m}).cardQuot * (Submodule.span R {n}).cardQuot) *
        (I.cardQuot * J.cardQuot) := by ac_rfl

end Module.Invertible
