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
  preserves both heights. See [module heights](DedekindIdealArithmetic/NumberField/ModuleHeight.lean)
  and the metric modules below.

## Mathematical scope

Import `DedekindIdealArithmetic` for the complete public interface, or one of
the modules below for a smaller import. The [generated API reference](docs/API.md)
covers the six ideal-norm, principal-prime and localization results; its
[reproduction contract](docs/README.md) describes exact source/pin binding and limits.

| Module | Public declarations | Meaning |
| --- | --- | --- |
| [`DedekindIdealArithmetic.Ideal.AbsNorm`](DedekindIdealArithmetic/Ideal/AbsNorm.lean) | `Ideal.absNorm_lt_absNorm_of_lt`, `Ideal.eq_of_le_of_absNorm_eq` | Strict ideal inclusion reverses absolute norm when the smaller ideal is nonzero; nested equal-norm ideals are equal, including the zero-ideal case |
| [`DedekindIdealArithmetic.Ideal.PrincipalPrime`](DedekindIdealArithmetic/Ideal/PrincipalPrime.lean) | `Ideal.exists_principal_prime_over_of_norm_natAbs_eq` | An element with prime absolute algebraic norm generates a principal prime above that rational prime |
| [`DedekindIdealArithmetic.ClassGroup.Localization`](DedekindIdealArithmetic/ClassGroup/Localization.lean) | `ClassGroup.extendedHom_surjective_of_isLocalization`, `ClassGroup.isPrincipalIdealRing_of_generator_of_isLocalization`, `ClassGroup.uniqueFactorizationMonoid_of_generator_of_isLocalization` | Class-group extension to a Dedekind localization is onto; killing a generator of the source class group gives a PID and hence a UFD |
| [`DedekindIdealArithmetic.Module.Index`](DedekindIdealArithmetic/Module/Index.lean) | `Submodule.cardQuot_map_of_injective`, `Submodule.cardQuot_span_singleton_smul`, `Module.Invertible.finite_quotient_span_singleton`, `Module.Invertible.exists_nonzero_smul_eq`, `Module.Invertible.cardQuot_span_singleton_tmul` | Quotient-index laws, finite section quotients and common scalar multiples; pure-tensor section indices multiply for invertible modules over a Dedekind domain with finite quotients |
| [`DedekindIdealArithmetic.Module.CoefficientIdeal`](DedekindIdealArithmetic/Module/CoefficientIdeal.lean) | `LinearEquiv.coefficientIdeal`, `LinearEquiv.mem_coefficientIdeal_iff`, `LinearEquiv.coefficientIdeal_ne_zero`, `LinearEquiv.coefficientIdeal_rid` | A supplied fraction-field frame of a finitely generated module over a commutative ring gives a nonzero fractional coefficient ideal, with membership and unit formulas |
| [`DedekindIdealArithmetic.Module.RankOneSeminorm`](DedekindIdealArithmetic/Module/RankOneSeminorm.lean) | `Seminorm.extendScalarsRankOne`, `Seminorm.extendScalarsRankOne_apply_tmul`, `Seminorm.extendScalarsRankOne_unique`, `Seminorm.extendScalarsRankOne_normSeminorm` | For a normed field algebra and an invertible source vector space, uniquely extend a possibly degenerate seminorm by `pₗ(a ⊗ x) = ‖a‖ * p(x)`; definiteness is preserved and the unit line recovers the field norm |
| [`DedekindIdealArithmetic.NumberField.ArchimedeanNorms`](DedekindIdealArithmetic/NumberField/ArchimedeanNorms.lean) | `NumberField.ArchimedeanNorms`, `ArchimedeanNorms.normProduct`, `ArchimedeanNorms.normProduct_smul`, `InfinitePlace.one_tmul_injective` (within `NumberField`) | Definite completion-fibre seminorms, their weighted product and scalar law, and injectivity of specialization for flat integral modules |
| [`DedekindIdealArithmetic.NumberField.ModuleHeight`](DedekindIdealArithmetic/NumberField/ModuleHeight.lean) | `NumberField.ArchimedeanNorms.height_eq`, `NumberField.ArchimedeanNorms.height_pos`, `NumberField.ArchimedeanNorms.normalizedLogHeight_eq`, `NumberField.ArchimedeanNorms.unit_height`, `NumberField.ArchimedeanNorms.unit_normalizedLogHeight` | Section-independent positive height, normalized logarithmic formula and the standard unit metric |
| [`DedekindIdealArithmetic.NumberField.MetricTensorProduct`](DedekindIdealArithmetic/NumberField/MetricTensorProduct.lean) | `NumberField.ArchimedeanNorms.tensor`, `NumberField.ArchimedeanNorms.tensor_apply_tmul`, `NumberField.ArchimedeanNorms.height_tensor`, `NumberField.ArchimedeanNorms.normalizedLogHeight_tensor` | Tensor metrics on invertible integral modules, multiplicative on fibre pure tensors; heights multiply and logarithmic heights add |
| [`DedekindIdealArithmetic.NumberField.MetricRescaling`](DedekindIdealArithmetic/NumberField/MetricRescaling.lean) | `NumberField.ArchimedeanNorms.rescale`, `NumberField.ArchimedeanNorms.rescale_apply`, `NumberField.ArchimedeanNorms.height_rescale`, `NumberField.ArchimedeanNorms.normalizedLogHeight_rescale` | Positive placewise factors multiply whole-fibre norms, divide height by their weighted product and subtract their degree-normalized weighted logarithmic sum |
| [`DedekindIdealArithmetic.NumberField.MetricTransport`](DedekindIdealArithmetic/NumberField/MetricTransport.lean) | `NumberField.ArchimedeanNorms.comap`, `NumberField.ArchimedeanNorms.comap_apply`, `NumberField.ArchimedeanNorms.height_comap`, `NumberField.ArchimedeanNorms.normalizedLogHeight_comap` | Contravariant metric pullback along integral module equivalences; both heights are preserved for invertible modules |
| [`DedekindIdealArithmetic.NumberField.Completion.Extension`](DedekindIdealArithmetic/NumberField/Completion/Extension.lean) | `NumberField.InfinitePlace.Completion.completionMap_algebraMap`, `NumberField.InfinitePlace.Completion.norm_completionMap`, `NumberField.InfinitePlace.Completion.isometry_completionMap` | For field algebras and infinite places with `w.LiesOver v`, Mathlib's completion map extends the field map isometrically; the identity field map gives the identity |

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

Auxiliary modules construct coefficient ideals in supplied rational frames,
scalar extensions of seminorms on lines, and isometric completion maps. Their
characteristic and unit formulas are not rational-height or finite-extension
height evaluations. Rational finite-place/local-frame evaluation, independence
of that evaluation from local frames, and finite-extension height transport
remain open. The fixed-field integral construction and metric laws do not
supply the full normed-module height theory.

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
reuse `NumberField.LiesOver.completionMap`.

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
