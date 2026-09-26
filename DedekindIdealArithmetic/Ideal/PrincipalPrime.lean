/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
Original formalization: Prism.
-/
module

public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Principal primes from element norms

This file turns an element whose algebraic norm has prime absolute value into
a principal prime ideal above the corresponding rational prime. The statement
is formulated for any infinite Dedekind domain that is finite free over `ℤ`.
-/

public section

namespace Ideal

variable {S : Type*} [CommRing S] [IsDedekindDomain S] [Infinite S]
  [Module.Free ℤ S] [Module.Finite ℤ S]

/-- An element whose algebraic norm has prime absolute value generates a prime
ideal above that rational prime. -/
theorem exists_principal_prime_over_of_norm_natAbs_eq
    (p : ℕ) (hp : Nat.Prime p) (α : S)
    (hnorm : (Algebra.norm ℤ α).natAbs = p) :
    ∃ P ∈ primesOver (span {(p : ℤ)}) S, Submodule.IsPrincipal P := by
  let I : Ideal S := span {α}
  have habs : I.absNorm = p := by
    rw [show I = span {α} from rfl, absNorm_span_singleton, hnorm]
  have hIprime : I.IsPrime := by
    apply isPrime_of_irreducible_absNorm
    rw [habs]
    exact (Nat.irreducible_iff_nat_prime p).mpr hp
  have hIlies : I.LiesOver (span {(p : ℤ)}) := by
    constructor
    have hprimeabs : Nat.Prime I.absNorm := by rw [habs]; exact hp
    simpa only [habs, Nat.cast_ofNat] using span_singleton_absNorm hprimeabs
  exact ⟨I, ⟨hIprime, hIlies⟩, ⟨α, rfl⟩⟩

end Ideal
