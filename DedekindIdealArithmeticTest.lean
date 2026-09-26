/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

import DedekindIdealArithmetic

/-!
# Public-interface examples for Dedekind ideal arithmetic

These examples use only the ordinary aggregate import, not `import all` or
implementation-private declarations. They cover all six library theorems,
the zero/unit-ideal norm boundaries, a principal prime in the integers,
identity localization and localization of a ring with trivial class group.
They are named private theorems so their proof terms persist in the compiled
artifact for auditing, rather than transient anonymous `example` commands.
This module is a default build target, not part of the library's public API.
-/

open scoped nonZeroDivisors

universe u v

namespace DedekindIdealArithmeticTest

section IdealNorm

variable {S : Type u} [CommRing S] [IsDedekindDomain S]
  [Ring.HasFiniteQuotients S] [Infinite S]

-- Generic strict inclusion needs a nonzero smaller ideal.
private theorem strictNorm {I J : Ideal S} (hIJ : I < J) (hI : I ≠ ⊥) :
    J.absNorm < I.absNorm :=
  Ideal.absNorm_lt_absNorm_of_lt hIJ hI

-- This is the usage example in the README.
private theorem nestedNormEquality {I J : Ideal S} (hIJ : I ≤ J)
    (hnorm : I.absNorm = J.absNorm) :
    I = J :=
  Ideal.eq_of_le_of_absNorm_eq hIJ hnorm

-- The equality criterion still works when the smaller ideal is zero.
private theorem zeroNorm {J : Ideal S} (hnorm : J.absNorm = 0) : J = ⊥ := by
  apply (Ideal.eq_of_le_of_absNorm_eq (I := ⊥) bot_le ?_).symm
  simpa using hnorm.symm

-- The unit ideal provides a concrete strict-superideal client.
private theorem intTwoNorm :
    (⊤ : Ideal ℤ).absNorm < (Ideal.span {(2 : ℤ)}).absNorm := by
  have hproper : Ideal.span {(2 : ℤ)} ≠ ⊤ := by
    intro h
    have hu : IsUnit (2 : ℤ) := Ideal.span_singleton_eq_top.mp h
    simp [Int.isUnit_iff] at hu
  have hnonzero : Ideal.span {(2 : ℤ)} ≠ ⊥ := by simp
  exact Ideal.absNorm_lt_absNorm_of_lt (lt_top_iff_ne_top.mpr hproper) hnonzero

-- Dropping the nonzero hypothesis would incorrectly reverse 1 and 0 here.
private theorem nonzeroHypothesisNecessary :
    ¬ (⊤ : Ideal ℤ).absNorm < (⊥ : Ideal ℤ).absNorm := by simp

end IdealNorm

section PrincipalPrime

variable {S : Type u} [CommRing S] [IsDedekindDomain S] [Infinite S]
  [Module.Free ℤ S] [Module.Finite ℤ S]

private theorem principalPrime (p : ℕ) (hp : Nat.Prime p) (α : S)
    (hnorm : (Algebra.norm ℤ α).natAbs = p) :
    ∃ P ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) S, Submodule.IsPrincipal P :=
  Ideal.exists_principal_prime_over_of_norm_natAbs_eq p hp α hnorm

-- For S = Z the norm is the identity: this supplies a real norm witness.
private theorem intPrimeWitness (p : ℕ) (hp : Nat.Prime p) :
    ∃ P ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) ℤ, Submodule.IsPrincipal P := by
  exact Ideal.exists_principal_prime_over_of_norm_natAbs_eq p hp (p : ℤ) (by simp)

-- Absolute value also permits a negative element-norm witness.
private theorem negativeIntPrimeWitness (p : ℕ) (hp : Nat.Prime p) :
    ∃ P ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) ℤ, Submodule.IsPrincipal P := by
  exact Ideal.exists_principal_prime_over_of_norm_natAbs_eq p hp (-(p : ℤ)) (by simp)

end PrincipalPrime

section ClassGroupLocalization

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
  [Algebra A B] [IsDedekindDomain A] [IsDedekindDomain B]
  [Module.IsTorsionFree A B]

-- Surjectivity gives a preimage for a chosen target class, with no generator premise.
private theorem classGroupPreimage (M : Submonoid A) [IsLocalization M B]
    (c : ClassGroup B) :
    ∃ a : ClassGroup A, ClassGroup.extendedHom A B a = c :=
  ClassGroup.extendedHom_surjective_of_isLocalization M c

-- Both structure-valued consequences are usable with their exact assumptions.
private theorem pidAndUfd (M : Submonoid A) [IsLocalization M B]
    (g : ClassGroup A) (hgen : ∀ x : ClassGroup A, x ∈ Subgroup.zpowers g)
    (hkill : ClassGroup.extendedHom A B g = 1) :
    IsPrincipalIdealRing B ∧ UniqueFactorizationMonoid B :=
  ⟨ClassGroup.isPrincipalIdealRing_of_generator_of_isLocalization M g hgen hkill,
    ClassGroup.uniqueFactorizationMonoid_of_generator_of_isLocalization M g hgen hkill⟩

-- Localizing only at 1 works for arbitrary source class group, not just a PID.
private theorem identityLocalization : Function.Surjective (ClassGroup.extendedHom A A) := by
  let _ : IsLocalization (⊥ : Submonoid A) A := IsLocalization.self bot_le
  exact ClassGroup.extendedHom_surjective_of_isLocalization (⊥ : Submonoid A)

end ClassGroupLocalization

-- A downstream construction supplies the localization hypotheses via native APIs.
private theorem trivialClassGroupLocalization {A : Type u} [CommRing A] [IsDedekindDomain A]
    [Subsingleton (ClassGroup A)] (a : A) (ha : a ≠ 0) :
    IsPrincipalIdealRing (Localization.Away a) := by
  let hM : Submonoid.powers a ≤ A⁰ :=
    powers_le_nonZeroDivisors_of_noZeroDivisors ha
  let _ : IsDomain (Localization.Away a) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors _ hM
  let _ : Module.IsTorsionFree A (Localization.Away a) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (IsLocalization.injective _ hM)
  let _ : IsDedekindDomain (Localization.Away a) :=
    IsLocalization.isDedekindDomain A hM _
  apply ClassGroup.isPrincipalIdealRing_of_generator_of_isLocalization
    (Submonoid.powers a) (1 : ClassGroup A)
  · intro x
    rw [Subsingleton.elim x 1]
    exact Subgroup.mem_zpowers (1 : ClassGroup A)
  · simp

end DedekindIdealArithmeticTest
