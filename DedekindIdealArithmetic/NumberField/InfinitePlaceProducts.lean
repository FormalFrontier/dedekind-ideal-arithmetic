/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.NumberTheory.NumberField.Completion.Ramification

/-!
# Weighted products over infinite places

For an extension `L / K` of number fields and a function `f` on the infinite places
of `K` with values in a commutative monoid, the product of
`f (w.comap (algebraMap K L)) ^ w.mult` over the infinite places of `L` is the
`Module.finrank K L`-th power of the corresponding weighted product over `K`.
The additive version uses natural scalar multiplication in a commutative additive
monoid.

The proof regroups the product along restriction of places. The weight of each
fibre is computed using `mult_mul_finrank`, `inertiaDeg_eq_finrank` and
`sum_inertiaDeg_eq_finrank`; the regrouping and power identities are the finite
big-operator lemmas. In particular, no order or positivity on the codomain is needed.
-/

@[expose] public section

namespace NumberField.InfinitePlace

open scoped NumberField.LiesOver

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L]

open scoped Classical in
private theorem sum_mult_comap_eq (v : InfinitePlace K) :
    ∑ w ∈ Finset.univ.filter (fun w : InfinitePlace L ↦
      w.comap (algebraMap K L) = v), w.mult = v.mult * Module.finrank K L := by
  have hfibre : Finset.univ.filter (fun w : InfinitePlace L ↦
      w.comap (algebraMap K L) = v) = (v.placesOver L).toFinset := by
    ext w
    constructor
    · intro hw
      have hcomap : w.comap (algebraMap K L) = v := (Finset.mem_filter.mp hw).2
      have hlies : w.LiesOver v := ⟨congrArg Subtype.val hcomap⟩
      exact (Set.mem_toFinset (s := v.placesOver L)).mpr hlies
    · intro hw
      let : w.LiesOver v := (Set.mem_toFinset (s := v.placesOver L)).mp hw
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, LiesOver.comap_eq w v⟩
  rw [hfibre]
  calc
    ∑ w ∈ (v.placesOver L).toFinset, w.mult =
        ∑ w ∈ (v.placesOver L).toFinset, v.mult * v.inertiaDeg w := by
      refine Finset.sum_congr rfl fun w hw ↦ ?_
      let : w.LiesOver v := (Set.mem_toFinset (s := v.placesOver L)).mp hw
      rw [inertiaDeg_eq_finrank v w, mult_mul_finrank v w]
    _ = v.mult * Module.finrank K L := by
      rw [← Finset.mul_sum, sum_inertiaDeg_eq_finrank K L v]

/-- Pulling back a function along restriction of infinite places raises its
multiplicity-weighted product to the extension degree. -/
@[to_additive sum_mult_nsmul_comap
  /-- Pulling back a function along restriction of infinite places scales its
  multiplicity-weighted sum by the extension degree. -/]
theorem prod_comap_pow_mult {A : Type*} [CommMonoid A] (f : InfinitePlace K → A) :
    ∏ w : InfinitePlace L, f (w.comap (algebraMap K L)) ^ w.mult =
      (∏ v : InfinitePlace K, f v ^ v.mult) ^ Module.finrank K L := by
  classical
  calc
    _ = ∏ v : InfinitePlace K,
        ∏ w ∈ Finset.univ.filter (fun w : InfinitePlace L ↦
          w.comap (algebraMap K L) = v), f (w.comap (algebraMap K L)) ^ w.mult := by
      have hprod := Finset.prod_fiberwise
        (ι := InfinitePlace L) (κ := InfinitePlace K) (M := A)
        (Finset.univ : Finset (InfinitePlace L))
        (fun w : InfinitePlace L ↦ w.comap (algebraMap K L))
        (fun w : InfinitePlace L ↦ f (w.comap (algebraMap K L)) ^ w.mult)
      exact hprod.symm
    _ = ∏ v : InfinitePlace K, (f v ^ v.mult) ^ Module.finrank K L := by
      refine Finset.prod_congr rfl fun v _ ↦ ?_
      calc
        _ = ∏ w ∈ Finset.univ.filter (fun w : InfinitePlace L ↦
            w.comap (algebraMap K L) = v), f v ^ w.mult := by
          refine Finset.prod_congr rfl fun w hw ↦ ?_
          rw [(Finset.mem_filter.mp hw).2]
        _ = f v ^ (∑ w ∈ Finset.univ.filter (fun w : InfinitePlace L ↦
            w.comap (algebraMap K L) = v), w.mult) :=
          Finset.prod_pow_eq_pow_sum _ _ _
        _ = (f v ^ v.mult) ^ Module.finrank K L := by
          rw [sum_mult_comap_eq, pow_mul]
    _ = _ := Finset.prod_pow _ _ _

end NumberField.InfinitePlace
