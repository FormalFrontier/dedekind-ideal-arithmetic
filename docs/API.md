# Generated API reference

This reference covers the six authored public theorems of dedekind-ideal-arithmetic.
Import `DedekindIdealArithmetic` or the individual source module linked below.
`DedekindIdealArithmeticTest` contains private checked clients, not public API.

This page is not a private/generated-declaration census or proof audit.

Headers below are native doc-gen4 display signatures, not complete declarations
with proof bodies. Short names use the source's `Ideal` or `ClassGroup`
namespace, scoped notation and imports. Implicit parameters are displayed;
universe variables retain their native names. Source links target this same checkout.

The source/pin hashes and generation provenance are in [api-manifest.json](api-manifest.json).
See [generation instructions](README.md) and the [mathematical overview](../README.md).

## ClassGroup.extendedHom_surjective_of_isLocalization

```lean
theorem ClassGroup.extendedHom_surjective_of_isLocalization {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B] (M : Submonoid A) [IsLocalization M B] : Function.Surjective ⇑(extendedHom A B)
```

Extension of ideal classes to a Dedekind localization is surjective.

[Source](../DedekindIdealArithmetic/ClassGroup/Localization.lean#L36) (line 36).

## ClassGroup.isPrincipalIdealRing_of_generator_of_isLocalization

```lean
theorem ClassGroup.isPrincipalIdealRing_of_generator_of_isLocalization {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B] (M : Submonoid A) [IsLocalization M B] (g : ClassGroup A) (hgen : ∀ (x : ClassGroup A), x ∈ Subgroup.zpowers g) (hkill : (extendedHom A B) g = 1) : IsPrincipalIdealRing B
```

A Dedekind localization is a PID if a generator of the source class group
becomes trivial. The hypothesis `hgen` says that every class is an integral
power of `g`.

[Source](../DedekindIdealArithmetic/ClassGroup/Localization.lean#L56) (line 56).

## ClassGroup.uniqueFactorizationMonoid_of_generator_of_isLocalization

```lean
theorem ClassGroup.uniqueFactorizationMonoid_of_generator_of_isLocalization {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B] (M : Submonoid A) [IsLocalization M B] (g : ClassGroup A) (hgen : ∀ (x : ClassGroup A), x ∈ Subgroup.zpowers g) (hkill : (extendedHom A B) g = 1) : UniqueFactorizationMonoid B
```

A Dedekind localization is a UFD if a generator of the source class group
becomes trivial.

[Source](../DedekindIdealArithmetic/ClassGroup/Localization.lean#L79) (line 79).

## Ideal.absNorm_lt_absNorm_of_lt

```lean
theorem Ideal.absNorm_lt_absNorm_of_lt {S : Type u_1} [CommRing S] [IsDedekindDomain S] [Ring.HasFiniteQuotients S] [Infinite S] {I J : Ideal S} (hIJ : I < J) (hI : I ≠ ⊥) : absNorm J < absNorm I
```

Absolute norm is strictly antitone along strict inclusions whose smaller
ideal is nonzero.

[Source](../DedekindIdealArithmetic/Ideal/AbsNorm.lean#L27) (line 27).

## Ideal.eq_of_le_of_absNorm_eq

```lean
theorem Ideal.eq_of_le_of_absNorm_eq {S : Type u_1} [CommRing S] [IsDedekindDomain S] [Ring.HasFiniteQuotients S] [Infinite S] {I J : Ideal S} (hIJ : I ≤ J) (hnorm : absNorm I = absNorm J) : I = J
```

Nested ideals with equal absolute norm are equal.

[Source](../DedekindIdealArithmetic/Ideal/AbsNorm.lean#L41) (line 41).

## Ideal.exists_principal_prime_over_of_norm_natAbs_eq

```lean
theorem Ideal.exists_principal_prime_over_of_norm_natAbs_eq {S : Type u_1} [CommRing S] [IsDedekindDomain S] [Infinite S] [Module.Free ℤ S] [Module.Finite ℤ S] (p : ℕ) (hp : Nat.Prime p) (α : S) (hnorm : ((Algebra.norm ℤ) α).natAbs = p) : ∃ P ∈ (span {↑p}).primesOver S, Submodule.IsPrincipal P
```

An element whose algebraic norm has prime absolute value generates a prime
ideal above that rational prime.

[Source](../DedekindIdealArithmetic/Ideal/PrincipalPrime.lean#L25) (line 25).
