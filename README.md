# dedekind-ideal-arithmetic

Reusable Lean theory of ideal norms, principal-prime extraction, localization
of ideal class groups, and intrinsic heights of normed invertible modules over
rings of integers. The library uses mathlib's ideals, algebraic norms, module
invertibility, quotient indices, completions and class groups.

## Headline results

These results build on mathlib's ideal, norm, module, localization and class-group
interfaces; this library does not redefine them.

- **Norm detects strict ideal inclusion and equality.** In an infinite
  commutative Dedekind domain with finite quotients, `I < J` and `I ≠ ⊥`
  imply `J.absNorm < I.absNorm`. If `I ≤ J` and their absolute norms agree,
  then `I = J`, even for the zero ideal. Neither result requires a finite-free
  presentation over `ℤ`. See [strict norm comparison](DedekindIdealArithmetic/Ideal/AbsNorm.lean#L29)
  and [equality](DedekindIdealArithmetic/Ideal/AbsNorm.lean#L42).
- **A supplied prime-norm element yields a principal prime.** In an infinite
  Dedekind domain finite free over `ℤ`, a natural prime `p` and a supplied
  `α` with `(Algebra.norm ℤ α).natAbs = p` give a principal prime above
  `(p)`. This is conditional existence, not a search for `α`, a class-number
  computation or a claim that every prime has a witness. See
  [principal-prime extraction](DedekindIdealArithmetic/Ideal/PrincipalPrime.lean#L27).
- **Localization can kill the class group and give a PID/UFD.** For Dedekind
  domains `A` and `B` (possibly in different universes), an `A`-algebra `B`
  torsion-free over `A`, and an actual `IsLocalization M B`, extension
  `Cl(A) → Cl(B)` is [surjective](DedekindIdealArithmetic/ClassGroup/Localization.lean#L37)
  without a generator hypothesis. If every source class is an integral power
  of a supplied `g` and `g` extends to one, the library supplies the
  [PID criterion](DedekindIdealArithmetic/ClassGroup/Localization.lean#L59)
  and [UFD consequence](DedekindIdealArithmetic/ClassGroup/Localization.lean#L81).
  No class-group computation, injectivity or basic-open cover is asserted.
- **Section indices, finite quotients and common multiples.** Over a domain,
  scaling a nonzero section of a torsion-free module multiplies its quotient
  index by the principal left-ideal index, including zero scalars and infinite
  quotients. Over a commutative domain with finite quotients, an invertible
  module has finite quotient by every nonzero section. Any two nonzero sections
  of an invertible module over a commutative domain admit a common nonzero scalar
  multiple. See [module indices](DedekindIdealArithmetic/Module/Index.lean).
- **Intrinsic heights of normed invertible modules.** For a number field `K`,
  an invertible `𝓞 K`-module with definite seminorms on its archimedean fibres
  has a positive multiplicative height: the quotient index divided by the
  weighted norm product, evaluated at **every** nonzero integral section.
  No global integral basis or principal ideal presentation is assumed.
  The normalized logarithmic height subtracts the weighted logarithmic norm
  sum from the logarithmic index and divides by `[K : ℚ]`; it can be negative.
  Tensor products multiply heights and add logarithmic heights; positive
  placewise rescaling divides by the weighted factor and subtracts its
  degree-normalized logarithm. Pullback along an integral module equivalence
  preserves both heights. A supplied rational frame evaluates this same height
  as the reciprocal of the product of its coefficient-ideal norm and the
  weighted norm product of its rational unit vector, without an integral basis.
  See [module heights](DedekindIdealArithmetic/NumberField/ModuleHeight.lean),
  [rational-frame heights](DedekindIdealArithmetic/NumberField/RationalFrameHeight.lean)
  and the metric modules below.
- **Fractional-ideal norm factorization and finite-place height factors.** Over
  a Dedekind domain finite free over `ℤ`, the norm of a nonzero fractional ideal
  is the finite-support product of prime-ideal norms raised to its signed
  factorization exponents; its fraction field needs no number-field structure.
  For a number field `K` and an invertible `𝓞 K`-module, this gives the height
  in every rational frame as the product of residue cardinalities with negative
  coefficient-ideal exponents, divided by the weighted archimedean norm product. See
  [fractional norms](DedekindIdealArithmetic/Ideal/FractionalNorm.lean) and
  [finite-place height factors](DedekindIdealArithmetic/NumberField/FinitePlaceHeight.lean).
- **Principal exponents determine scalar completion norms.** For any Dedekind
  domain and fraction field, a nonzero scalar has adic valuation equal to the
  exponential of its negative principal fractional-ideal count. With an infinite
  base ring and finite quotients, its norm in the adic completion is the residue
  cardinality raised to that negative count. No finite-free presentation over
  the integers or norm on the fraction field is required. See
  [adic norms](DedekindIdealArithmetic/Ideal/AdicNorm.lean).

## Mathematical scope

Import `DedekindIdealArithmetic` for the complete public interface, or one of
the modules below for a smaller import. The [generated API reference](docs/API.md)
covers the six ideal-norm, principal-prime and localization results; its
[reproduction contract](docs/README.md) describes exact source/pin binding and limits.

| Module | Public declarations | Meaning |
| --- | --- | --- |
| [`DedekindIdealArithmetic.Ideal.AbsNorm`](DedekindIdealArithmetic/Ideal/AbsNorm.lean) | `Ideal.absNorm_lt_absNorm_of_lt`, `Ideal.eq_of_le_of_absNorm_eq` | Strict ideal inclusion reverses absolute norm when the smaller ideal is nonzero; nested equal-norm ideals are equal, including the zero-ideal case |
| [`DedekindIdealArithmetic.Ideal.AdicNorm`](DedekindIdealArithmetic/Ideal/AdicNorm.lean) | `IsDedekindDomain.HeightOneSpectrum.valuation_eq_exp_neg_count_spanSingleton`, `IsDedekindDomain.HeightOneSpectrum.norm_algebraMap_eq_zpow_neg_count_spanSingleton`, `NumberField.FinitePlace.norm_algebraMap` | Principal fractional-ideal counts determine adic valuations and selected completion norms; the principal weight cancels the norm of its nonzero generator |
| [`DedekindIdealArithmetic.Ideal.FractionalNorm`](DedekindIdealArithmetic/Ideal/FractionalNorm.lean) | `FractionalIdeal.absNorm_eq_finprod_count`, `FractionalIdeal.absNorm_spanSingleton_eq_cardQuot_mul`, `FractionalIdeal.absNorm_extendedHom` | Nonzero fractional-ideal norms factor as finite-support products of prime norms with signed exponents; principal norms equal span index times ideal norm, including zero ideals/elements; extension raises norm to the relative rank |
| [`DedekindIdealArithmetic.Ideal.PrincipalPrime`](DedekindIdealArithmetic/Ideal/PrincipalPrime.lean) | `Ideal.exists_principal_prime_over_of_norm_natAbs_eq` | An element with prime absolute algebraic norm generates a principal prime above that rational prime |
| [`DedekindIdealArithmetic.ClassGroup.Localization`](DedekindIdealArithmetic/ClassGroup/Localization.lean) | `ClassGroup.extendedHom_surjective_of_isLocalization`, `ClassGroup.isPrincipalIdealRing_of_generator_of_isLocalization`, `ClassGroup.uniqueFactorizationMonoid_of_generator_of_isLocalization` | Class-group extension to a Dedekind localization is onto; killing a generator of the source class group gives a PID and hence a UFD |
| [`DedekindIdealArithmetic.Module.Index`](DedekindIdealArithmetic/Module/Index.lean) | `Submodule.cardQuot_map_of_injective`, `Submodule.cardQuot_span_singleton_smul`, `Module.Invertible.finite_quotient_span_singleton`, `Module.Invertible.exists_nonzero_smul_eq`, `Module.Invertible.cardQuot_span_singleton_tmul` | Quotient-index laws, finite section quotients and common scalar multiples; pure-tensor section indices multiply for invertible modules over a Dedekind domain with finite quotients |
| [`DedekindIdealArithmetic.Module.TensorCoordinates`](DedekindIdealArithmetic/Module/TensorCoordinates.lean) | `LinearEquiv.scalarExtensionCoordinate`, `LinearEquiv.scalarExtensionCoordinate_tmul`, `LinearEquiv.scalarExtensionCoordinate_symm_apply` | Extend a supplied linear coordinate through a semiring algebra by base change and the tensor unit equivalence |
| [`DedekindIdealArithmetic.Module.CoefficientIdeal`](DedekindIdealArithmetic/Module/CoefficientIdeal.lean) | `LinearEquiv.coefficientMap_injective`, `LinearEquiv.coefficientIdeal`, `LinearEquiv.mem_coefficientIdeal_iff`, `LinearEquiv.coefficientIdeal_ne_zero`, `LinearEquiv.coefficientIdeal_rid`, `LinearEquiv.coefficientMap_eq_smul`, `LinearEquiv.coefficientIdeal_eq_spanSingleton_mul`, `LinearEquiv.fibreCoordinate`, `LinearEquiv.fibreCoordinate_change` | A supplied frame gives semiring-algebra fibre coordinates with pure-tensor, inverse, unit and frame-change laws; a rational frame realizes a finite torsion-free module as its nonzero coefficient fractional ideal; changing frames multiplies the map and ideal by the corresponding nonzero scalar and principal ideal |
| [`DedekindIdealArithmetic.Module.CoefficientIdealNorm`](DedekindIdealArithmetic/Module/CoefficientIdealNorm.lean) | `LinearEquiv.cardQuot_span_singleton_mul_absNorm_coefficientIdeal` | Over a Dedekind domain finite free over the integers, every section's span index times the coefficient-ideal norm is the principal fractional norm of its coefficient, without integral freeness or invertibility |
| [`DedekindIdealArithmetic.Module.RankOneSeminorm`](DedekindIdealArithmetic/Module/RankOneSeminorm.lean) | `Seminorm.extendScalarsRankOne`, `Seminorm.extendScalarsRankOne_apply_tmul`, `Seminorm.extendScalarsRankOne_unique`, `Seminorm.extendScalarsRankOne_normSeminorm` | For a normed field algebra and an invertible source vector space, uniquely extend a possibly degenerate seminorm by `pₗ(a ⊗ x) = ‖a‖ * p(x)`; definiteness is preserved and the unit line recovers the field norm |
| [`DedekindIdealArithmetic.NumberField.ArchimedeanNorms`](DedekindIdealArithmetic/NumberField/ArchimedeanNorms.lean) | `NumberField.ArchimedeanNorms`, `ArchimedeanNorms.normProduct`, `ArchimedeanNorms.normProduct_smul`, `InfinitePlace.one_tmul_injective` (within `NumberField`) | Definite completion-fibre seminorms, their weighted product and scalar law, and injectivity of specialization for flat integral modules |
| [`DedekindIdealArithmetic.NumberField.ModuleHeight`](DedekindIdealArithmetic/NumberField/ModuleHeight.lean) | `NumberField.ArchimedeanNorms.height_eq`, `NumberField.ArchimedeanNorms.height_pos`, `NumberField.ArchimedeanNorms.normalizedLogHeight_eq`, `NumberField.ArchimedeanNorms.unit_height`, `NumberField.ArchimedeanNorms.unit_normalizedLogHeight` | Section-independent positive height, normalized logarithmic formula and the standard unit metric |
| [`DedekindIdealArithmetic.NumberField.MetricTensorProduct`](DedekindIdealArithmetic/NumberField/MetricTensorProduct.lean) | `NumberField.ArchimedeanNorms.tensor`, `NumberField.ArchimedeanNorms.tensor_apply_tmul`, `NumberField.ArchimedeanNorms.height_tensor`, `NumberField.ArchimedeanNorms.normalizedLogHeight_tensor` | Tensor metrics on invertible integral modules, multiplicative on fibre pure tensors; heights multiply and logarithmic heights add |
| [`DedekindIdealArithmetic.NumberField.MetricRescaling`](DedekindIdealArithmetic/NumberField/MetricRescaling.lean) | `NumberField.ArchimedeanNorms.rescale`, `NumberField.ArchimedeanNorms.rescale_apply`, `NumberField.ArchimedeanNorms.height_rescale`, `NumberField.ArchimedeanNorms.normalizedLogHeight_rescale` | Positive placewise factors multiply whole-fibre norms, divide height by their weighted product and subtract their degree-normalized weighted logarithmic sum |
| [`DedekindIdealArithmetic.NumberField.MetricTransport`](DedekindIdealArithmetic/NumberField/MetricTransport.lean) | `NumberField.ArchimedeanNorms.comap`, `NumberField.ArchimedeanNorms.comap_apply`, `NumberField.ArchimedeanNorms.height_comap`, `NumberField.ArchimedeanNorms.normalizedLogHeight_comap` | Contravariant metric pullback along integral module equivalences; both heights are preserved for invertible modules |
| [`DedekindIdealArithmetic.NumberField.Completion.Extension`](DedekindIdealArithmetic/NumberField/Completion/Extension.lean) | `NumberField.InfinitePlace.Completion.completionMap_algebraMap`, `NumberField.InfinitePlace.Completion.norm_completionMap`, `NumberField.InfinitePlace.Completion.isometry_completionMap` | For field algebras and infinite places with `w.LiesOver v`, Mathlib's completion map extends the field map isometrically; the identity field map gives the identity |
| [`DedekindIdealArithmetic.NumberField.RationalFibre`](DedekindIdealArithmetic/NumberField/RationalFibre.lean) | `NumberField.InfinitePlace.rationalFibre_injective`, `NumberField.ArchimedeanNorms.rationalEval`, `NumberField.ArchimedeanNorms.rationalEval_eq_zero_iff`, `NumberField.ArchimedeanNorms.unit_rationalEval` | Injective specialization of the rational fibre without integral-module flatness, placewise evaluation of explicit metric data, and the whole rational unit-fibre model |
| [`DedekindIdealArithmetic.NumberField.RationalFrameHeight`](DedekindIdealArithmetic/NumberField/RationalFrameHeight.lean) | `NumberField.ArchimedeanNorms.normProduct_eq_rationalFrame`, `NumberField.ArchimedeanNorms.height_eq_rationalFrame`, `NumberField.ArchimedeanNorms.normalizedLogHeight_eq_rationalFrame` | Scalar-coordinate norm-product identity for all sections; evaluation of intrinsic height and its normalized logarithm in every supplied rational frame for invertible modules |
| [`DedekindIdealArithmetic.NumberField.FinitePlaceHeight`](DedekindIdealArithmetic/NumberField/FinitePlaceHeight.lean) | `NumberField.FinitePlace.absNorm_eq_finprod_count`, `NumberField.ArchimedeanNorms.height_eq_finitePlace` | Nonzero fractional-ideal norms as real finite-support products of residue cardinalities; height in any rational frame uses negative coefficient-ideal exponents and the weighted archimedean denominator |
| [`DedekindIdealArithmetic.NumberField.InfinitePlaceProducts`](DedekindIdealArithmetic/NumberField/InfinitePlaceProducts.lean) | `NumberField.InfinitePlace.prod_comap_pow_mult`, `NumberField.InfinitePlace.sum_mult_nsmul_comap` | Restriction of infinite places raises multiplicity-weighted products to the relative degree, and scales weighted sums by that degree, for arbitrary commutative monoids or additive commutative monoids |

The norm-order results assume a commutative infinite Dedekind domain with
`Ring.HasFiniteQuotients`. They do **not** assume a finite-free presentation over
`ℤ`. The nonzero hypothesis in the strict inequality is essential: the zero
ideal has absolute norm zero in an infinite ring, while the unit ideal has norm
one. The equality criterion includes the zero-ideal case.

Principal-prime extraction assumes an infinite Dedekind domain finite free over
`ℤ`, a natural prime `p`, and a supplied element `α` with
`(Algebra.norm ℤ α).natAbs = p`. The theorem does not find that element, compute
a class number, or assert that every rational prime admits such an element.

The localization results assume Dedekind domains `A` and `B`, an `A`-algebra
structure on `B`, `Module.IsTorsionFree A B`, and an actual `IsLocalization M B`
instance. Surjectivity alone requires no generator. For the PID/UFD conclusions,
every class of `A` must lie in `Subgroup.zpowers g` and the extension of `g` must
be trivial. Neither class group is assumed finite. No injectivity of class-group
extension, concrete class-group computation or concrete basic-open cover is
provided.

For an injective linear map `f : M →ₗ[R] N`, the index of `p.map f` is
`p.cardQuot * (LinearMap.range f).cardQuot`, without assuming either quotient
finite. Infinite quotients have index zero. For a nonzero section of a
torsion-free module over an infinite Dedekind domain, the scalar factor is
the absolute norm of the scalar's principal ideal.

For heights, `M` has the hypothesis `Module.Invertible (𝓞 K) M`, not
`Module.Free (𝓞 K) M`; nonprincipal invertible ideals are included.
`NumberField.ArchimedeanNorms K M` supplies a definite seminorm on **all**
vectors of each completion fibre `v.Completion ⊗[𝓞 K] M`, homogeneous for the
ordinary, unsquared completion norm. No norm instance on the tensor product
or on `M` is required. For every `m ≠ 0`, with `m_v = 1 ⊗ m`,

$$
 H = \frac{\#(M/\mathcal O_K m)}
              {\prod_{v\mid\infty}\lVert m_v\rVert_v^{\varepsilon_v}},
 \qquad h = \frac{\log H}{[K:\mathbb Q]},
 \qquad \varepsilon_v = \begin{cases}1&v\text{ real},\\2&v\text{ complex}.\end{cases}
$$

The numerator is `Submodule.cardQuot (Submodule.span (𝓞 K) {m})`, the
cardinality of the quotient, not prescribed index data. Quotient finiteness,
positivity of the denominator and independence of the nonzero integral section
are conclusions, not metric fields. The standard metric on `𝓞 K` has `H = 1`
and `h = 0`.

The tensor metric multiplies norms on pure tensors of completion-fibre vectors.
For invertible integral modules `M, N` with metrics `P, Q`, positive factors
`c : InfinitePlace K → ℝ≥0ˣ`, and `e : M ≃ₗ[𝓞 K] N`, the metric laws are

$$
\begin{aligned}
 H(P\otimes Q)&=H(P)H(Q), & h(P\otimes Q)&=h(P)+h(Q),\\
 H(cP)&=\frac{H(P)}{\prod_{v\mid\infty}c_v^{\varepsilon_v}}, &
 h(cP)&=h(P)-\frac{\sum_{v\mid\infty}\varepsilon_v\log c_v}{[K:\mathbb Q]},\\
 H(e^*Q)&=H(Q), & h(e^*Q)&=h(Q).
\end{aligned}
$$

Here `cP = P.rescale c` and `e*Q = Q.comap e`; the latter specifies the
isometry condition, not invariance under an arbitrary change of metric.
Multiplicative height is positive but need not be at least one.

For a supplied rational frame `e : K ⊗[𝓞 K] M ≃ₗ[K] K`, let
`I = e.coefficientIdeal` and `u = e.symm 1`. The same intrinsic height satisfies

$$
 H(P)=\left(N(I)\prod_{v\mid\infty}P_v(u)^{\varepsilon_v}\right)^{-1},\qquad
 h(P)=\frac{-\log N(I)-\sum_{v\mid\infty}\varepsilon_v\log P_v(u)}{[K:\mathbb Q]}.
$$

The ideal norm is rational-valued and cast to the reals; it is not itself an
inverse norm. The quotient-index comparison holds for every section, including
zero, over a Dedekind domain finite free over the integers. The archimedean
scalar-coordinate formula needs no finiteness or torsion-freeness of the
integral module.

For a finite place `w`, write `q_w = #(𝓞 K / w.maximalIdeal.asIdeal)` and
`c_w(I) = FractionalIdeal.count K w.maximalIdeal I`. Then

$$
 N(I)=\prod_{w\nmid\infty}q_w^{c_w(I)},\qquad
 H(P)=\frac{\prod_{w\nmid\infty}q_w^{-c_w(I)}}
                 {\prod_{v\mid\infty}P_v(u)^{\varepsilon_v}}.
$$

The products over finite places are finite-support products (`finprod`), not
analytic infinite products. The residue cardinality `q_w` already includes
its residue degree; there are no additional finite-place weights. The norm
factorization requires `I ≠ 0`, which is automatic for a coefficient ideal.
No section, integral basis or additional metric data are needed for this height
evaluation. See the [rational-frame guide](docs/RationalFrameHeight.md) for the
sign conventions, zero-ideal boundary and generic arithmetic identities.

A supplied frame `e : K ⊗[R] M ≃ₗ[K] K` also gives an `F`-linear coordinate
`e.fibreCoordinate F : F ⊗[R] M ≃ₗ[F] F` for compatible semiring algebras.
It sends `a ⊗ m` to `a * algebraMap K F (e.coefficientMap m)` and the image
of `e.symm 1` to one. This coordinate API assumes no module finiteness,
torsion-freeness, invertibility, fraction-field structure or norms.

Further modules extend seminorms on lines and compare completions isometrically.
Multiplicity-weighted products over restricted infinite places satisfy the
relative extension-degree formula. Fractional-ideal absolute norms obey the
relative-rank extension formula for torsion-free extensions of Dedekind domains
finite free over the integers. The arithmetic finite-place expression does not
construct norms on finite-completion fibres, their unit balls or tensor transport
of finite local frames. Finite-extension height transport also remains open.
The fixed-field construction and metric laws do not supply the full
normed-module height theory.

## Using the library

Add the dependency to your `lakefile.toml`:

```toml
[[require]]
name = "dedekind-ideal-arithmetic"
git = "https://github.com/FormalFrontier/dedekind-ideal-arithmetic.git"
rev = "main"
```

GitHub `main` contains reviewed releases. Lake resolves a release when you first
add or explicitly update the dependency; your `lake-manifest.json` retains that
commit until you update it again. To pin a specific release, replace `main` with
the full commit identifier of that release from the GitHub history. Then use
`import DedekindIdealArithmetic`, as in the example below.

Use a common Lean toolchain and mathlib revision throughout your client's
dependency closure, matching the release pins below. When combining libraries,
choose mutually compatible published releases and align their pins; retain the
resolved graph in `lake-manifest.json`. Following `main` or overriding only
mathlib does not guarantee compatibility.

The library and its example module use Lean's native module system. Public
declarations and imports are explicit; downstream users need only an ordinary
import, not access to implementation-private bodies. The producer modules use
public imports and public sections; the test module uses a plain import of
the aggregate. Importing the aggregate is not an import-all proof interface
for private client declarations.

```lean
module

import DedekindIdealArithmetic

example {S : Type*} [CommRing S] [IsDedekindDomain S]
    [Ring.HasFiniteQuotients S] [Infinite S] {I J : Ideal S}
    (hIJ : I ≤ J) (hnorm : I.absNorm = J.absNorm) : I = J :=
  Ideal.eq_of_le_of_absNorm_eq hIJ hnorm
```

[DedekindIdealArithmeticTest.lean](DedekindIdealArithmeticTest.lean) checks this
pattern, the six ideal-arithmetic results and their composition with mathlib APIs.
It includes the zero/unit-ideal boundary, positive and negative norm witnesses
in `ℤ`, identity localization and a localization of a ring with trivial class
group. It imports only `DedekindIdealArithmetic` through the ordinary public
interface and is built by the default target; it is not a library API to import.
The short snippet above demonstrates the same public API pattern.

## Reproducible build and checks

Install [elan](https://github.com/leanprover/elan) and clone this repository with
the access required by its current hosting. The declared inputs are Lean
`leanprover/lean4:v4.34.0-rc2` and mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`. The committed
`lake-manifest.json` locks all transitive dependencies. There is no other Formal
Frontier library dependency or path into a source-research workspace.

From the repository root:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake build
```

Verify that the cache fetch succeeds before building. After removing `.lake` or
changing the Lean/mathlib pins, fetch the matching cache again. The default build
compiles both the public library and the example module. To select them explicitly:

```sh
lake build DedekindIdealArithmetic DedekindIdealArithmeticTest
lake env lean -DwarningAsError=true -T0 DedekindIdealArithmeticTest.lean
```

The final command is an ordinary warning-fatal elaboration of the client.
`-T0` disables the allocation-count timeout; it does not set kernel trust to zero.
It is **not** a separate stored-proof recheck or a complete transitive axiom audit.
The build and client elaboration do not establish the transitive axiom
dependencies of all declarations, including private and generated declarations.
The entries in [formalization.yaml](formalization.yaml) summarize the mathematical
scope, not a complete declaration census.

## References

- J. S. Milne, *Abelian Varieties*, IV §6, 6.2–6.3. Reference for the normed-module
  height conventions, tensor products, positive metric rescaling and isometry
  invariance; these fixed-field results are not the full rational, geometric
  or finite-extension theory.
- Charles A. Weibel, [*The K-book: An Introduction to Algebraic K-theory*](https://sites.math.rutgers.edu/~weibel/Kbook/Kbook.pdf),
  complete-book build dated 2013-08-29, Chapter I, section 3. Background for the
  motivating cyclotomic examples, not a formalization of the whole book or
  concrete class-number computations.

## Formal sources and attribution

Authors: Formal Frontier Agents.

These proofs use the pinned mathlib APIs directly. In particular, norm order
uses `AddSubgroup.index_strictAnti`; principal-prime extraction uses
`Ideal.absNorm_span_singleton`, `Ideal.isPrime_of_irreducible_absNorm` and
`Ideal.span_singleton_absNorm`; localization uses `ClassGroup.extendedHom`,
`ClassGroup.mk0_surjective`, `ClassGroup.mk0_eq_one_iff` and
`IsLocalization.map_under`. The relevant upstream modules are
`Mathlib.RingTheory.Ideal.Norm.AbsNorm`,
`Mathlib.RingTheory.ClassGroup.ExtendedHom` and
`Mathlib.RingTheory.Localization.Ideal` at the exact pin above. Their authors and
license notices remain part of the upstream dependency. The height construction
also uses mathlib's `Module.Invertible`, ideal presentations, flat base change,
`Submodule.cardQuot`, completion seminorms and `InfinitePlace.prod_eq_abs_norm`.
Tensor metrics reuse its base-change equivalences, and completion extensions
reuse `NumberField.LiesOver.completionMap`. The finite-place formulas use
mathlib's fractional-ideal factorization and signed `FractionalIdeal.count`,
finite-support products, and finite-place/height-one-prime equivalence.

Prism contributed the norm-order and principal-prime formalizations; Atlas
contributed the class-group/localization formalization. Development, checking
and review have involved AI agents in the Formal Frontier project; these are
agent identities, not claims of human authorship or independent certification.
The source-maintainer team collectively maintains the library.

The norm-order and principal-prime proof expression adapts Prism's earlier
original 13-cyclotomic and 17-cyclotomic formalizations. Both supplied finite-index
norm-comparison and principal-prime-from-norm expression antecedents. This is
original-project expression reuse, not merely a bibliographic influence or a claim
of wholly new proof text. No book excerpt, research file or concrete cyclotomic
computation is shipped.
The [documentation adapter provenance](docs/README.md#provenance)
credits Anchor and Prism's original tooling and this library's adaptation.

Original Formal Frontier contributions are available under the
[Apache License, Version 2.0](LICENSE) (`Apache-2.0`). The collective author credit
does not identify a copyright holder or replace upstream authorship. Existing
copyright, attribution and license notices for reused third-party material
remain applicable. Dependency notices apply separately.

The library can be used solely through its declared dependencies.
