# dedekind-ideal-arithmetic

Reusable Lean theory of ideal norms, principal-prime extraction, localization
of ideal class groups, canonical ultrametric seminorms on adic fibres, and
intrinsic heights of normed invertible modules over rings of integers.
The library builds on mathlib's ideal, module, tensor-product, completion
and class-group interfaces rather than redefining them.

## Headline results

- **Norm detects strict ideal inclusion and equality.** In an infinite
  commutative Dedekind domain with finite quotients, `I < J` and `I ≠ ⊥`
  imply `J.absNorm < I.absNorm`. If `I ≤ J` and the norms agree, `I = J`,
  including zero ideals. No finite-free presentation over `ℤ` is needed.
  See [strict comparison](DedekindIdealArithmetic/Ideal/AbsNorm.lean#L29)
  and [equality](DedekindIdealArithmetic/Ideal/AbsNorm.lean#L42).
- **A supplied prime-norm element yields a principal prime.** In an infinite
  Dedekind domain finite free over `ℤ`, a natural prime `p` and a supplied
  `α` with `(Algebra.norm ℤ α).natAbs = p` give a principal prime above
  `(p)`. This is conditional existence, not a search for `α`, a class-number
  computation or a witness assertion for every prime. See
  [principal-prime extraction](DedekindIdealArithmetic/Ideal/PrincipalPrime.lean#L27).
- **Localization can kill the class group and give a PID/UFD.** For Dedekind
  domains `A, B` in possibly different universes, an `A`-algebra `B`
  torsion-free over `A`, and
  `IsLocalization M B`, extension `Cl(A) → Cl(B)` is
  [surjective](DedekindIdealArithmetic/ClassGroup/Localization.lean#L37).
  If every source class is an integral power of a supplied `g` and `g`
  extends to one, the library gives a
  [PID](DedekindIdealArithmetic/ClassGroup/Localization.lean#L59) and hence a
  [UFD](DedekindIdealArithmetic/ClassGroup/Localization.lean#L81).
  Surjectivity needs no generator; neither class group need be finite.
- **Section indices and common multiples.** Over a domain, scaling a
  nonzero section of a torsion-free module multiplies its quotient index by
  the principal left-ideal index, including zero scalars and infinite quotients.
  Invertible modules over commutative domains with finite quotients have finite
  quotients by nonzero sections; over any commutative domain their nonzero
  sections admit common nonzero scalar multiples. See
  [module indices](DedekindIdealArithmetic/Module/Index.lean).
- **Intrinsic heights of normed invertible modules.** Over `𝓞 K` for a number
  field `K`, definite seminorms on all archimedean fibres give a positive,
  section-independent height: quotient index divided by the weighted norm
  product. Invertibility, not integral freeness, is assumed. Tensor products,
  positive rescaling and integral-equivalence pullback obey the expected
  multiplicative and logarithmic laws. The normalized logarithmic height can
  be negative. See [module heights](DedekindIdealArithmetic/NumberField/ModuleHeight.lean)
  and the [height guide](docs/RationalFrameHeight.md#intrinsic-height-and-sections).
- **Rational-frame and finite-place height formulas.** Every rational frame
  evaluates this same intrinsic height as `1 / (N(I) * archimedeanProduct)`.
  Nonzero fractional-ideal norms factor into prime norms with signed exponents
  over Dedekind domains finite free over `ℤ`, without a number-field structure
  on the fraction field. For number fields the height numerator uses residue
  cardinalities with **negative** coefficient-ideal counts. See
  [fractional norms](DedekindIdealArithmetic/Ideal/FractionalNorm.lean) and
  [finite-place height factors](DedekindIdealArithmetic/NumberField/FinitePlaceHeight.lean).
- **Principal exponents determine scalar completion norms.** Over a Dedekind
  domain and fraction field, a nonzero scalar has adic valuation equal to the
  exponential of its negative principal-ideal count. For an infinite base with
  finite quotients, its completion norm is the residue cardinality to that
  negative count. No norm on bare `K` is chosen. See
  [adic norms](DedekindIdealArithmetic/Ideal/AdicNorm.lean).
- **Sharp signed fractional-ideal exponents.** At each fixed height-one prime
  of any Dedekind domain, a nonzero fractional ideal contains a nonzero element
  attaining its signed count. Together with Mathlib's `count_mono`, this is an
  attained minimum. The witness may depend on the prime; no principality,
  infinite-ring, finite-residue or `ℤ`-freeness hypothesis is needed. See
  [count attainment](DedekindIdealArithmetic/Ideal/CountAttainment.lean).
- **Algebraic integral spans in adic fibres.** For any `R`-module `M` over a
  Dedekind domain with fraction field `K` and height-one prime `p`, the span of
  `1 ⊗ m` over the valuation integers in `F ⊗[R] M`,
  `F = p.adicCompletion K`, is the image of
  `O ⊗[R] M`, `O = p.adicCompletionIntegers K`. It is finite over `O` if
  `M` is finite, and spans the whole fibre over `F`; flatness makes the image
  map an equivalence onto the span. For `M = R`, the whole span corresponds
  exactly to `O`. No finite-residue or infinite-ring hypothesis is used. See
  [integral spans](DedekindIdealArithmetic/Module/AdicIntegralSpan.lean).
- **Canonical ultrametric seminorms on adic fibres.** For an infinite Dedekind
  domain `R` with finite quotients, fraction field `K`, height-one prime `p`
  and invertible `M`, the fibre `F ⊗[R] M` has a canonical definite
  `F`-seminorm. In every rational frame, on every vector, it is the coordinate
  norm times the residue cardinality raised to the signed coefficient-ideal
  count, with a **plus** sign; negative counts are included. It is
  frame-independent and characterized by its rational-unit-vector weight.
  The supplied-frame constructor only needs finite `M` and a frame,
  allowing torsion. For `M = R` the whole seminorm is the completion norm
  pulled back along tensor right-unit equivalence. See
  [adic seminorms](DedekindIdealArithmetic/Module/AdicSeminorm.lean).

## Mathematical scope

Import `DedekindIdealArithmetic` for the complete public interface, or a leaf
module for a smaller import. The [generated API reference](docs/API.md) covers
six ideal-norm, principal-prime and localization results; its
[reproduction contract](docs/README.md) describes exact source/pin binding and limits.

| Module | Public declarations | Meaning |
| --- | --- | --- |
| [`DedekindIdealArithmetic.Ideal.AbsNorm`](DedekindIdealArithmetic/Ideal/AbsNorm.lean) | `Ideal.absNorm_lt_absNorm_of_lt`, `Ideal.eq_of_le_of_absNorm_eq` | Strict ideal inclusion reverses absolute norm when the smaller ideal is nonzero; nested equal-norm ideals are equal, including the zero-ideal case |
| [`DedekindIdealArithmetic.Ideal.AdicNorm`](DedekindIdealArithmetic/Ideal/AdicNorm.lean) | `IsDedekindDomain.HeightOneSpectrum.valuation_eq_exp_neg_count_spanSingleton`, `IsDedekindDomain.HeightOneSpectrum.norm_algebraMap_eq_zpow_neg_count_spanSingleton`, `NumberField.FinitePlace.norm_algebraMap` | Principal fractional-ideal counts determine adic valuations and selected completion norms; the principal weight cancels the norm of its nonzero generator |
| [`DedekindIdealArithmetic.Ideal.CountAttainment`](DedekindIdealArithmetic/Ideal/CountAttainment.lean) | `FractionalIdeal.exists_mem_count_spanSingleton_eq` | At each fixed height-one prime, a nonzero fractional ideal contains a nonzero element whose principal ideal attains its signed prime exponent; no principality or finite-residue hypothesis |
| [`DedekindIdealArithmetic.Ideal.FractionalNorm`](DedekindIdealArithmetic/Ideal/FractionalNorm.lean) | `FractionalIdeal.absNorm_eq_finprod_count`, `FractionalIdeal.absNorm_spanSingleton_eq_cardQuot_mul`, `FractionalIdeal.absNorm_extendedHom` | Nonzero fractional-ideal norms factor as finite-support products of prime norms with signed exponents; principal norms equal span index times ideal norm, including zero ideals/elements; extension raises norm to the relative rank |
| [`DedekindIdealArithmetic.Ideal.PrincipalPrime`](DedekindIdealArithmetic/Ideal/PrincipalPrime.lean) | `Ideal.exists_principal_prime_over_of_norm_natAbs_eq` | An element with prime absolute algebraic norm generates a principal prime above that rational prime |
| [`DedekindIdealArithmetic.ClassGroup.Localization`](DedekindIdealArithmetic/ClassGroup/Localization.lean) | `ClassGroup.extendedHom_surjective_of_isLocalization`, `ClassGroup.isPrincipalIdealRing_of_generator_of_isLocalization`, `ClassGroup.uniqueFactorizationMonoid_of_generator_of_isLocalization` | Class-group extension to a Dedekind localization is onto; killing a generator of the source class group gives a PID and hence a UFD |
| [`DedekindIdealArithmetic.Module.Index`](DedekindIdealArithmetic/Module/Index.lean) | `Submodule.cardQuot_map_of_injective`, `Submodule.cardQuot_span_singleton_smul`, `Module.Invertible.finite_quotient_span_singleton`, `Module.Invertible.exists_nonzero_smul_eq`, `Module.Invertible.cardQuot_span_singleton_tmul` | Quotient-index laws, finite section quotients and common scalar multiples; pure-tensor section indices multiply for invertible modules over a Dedekind domain with finite quotients |
| [`DedekindIdealArithmetic.Module.TensorCoordinates`](DedekindIdealArithmetic/Module/TensorCoordinates.lean) | `LinearEquiv.scalarExtensionCoordinate`, `LinearEquiv.scalarExtensionCoordinate_tmul`, `LinearEquiv.scalarExtensionCoordinate_symm_apply` | Extend a supplied linear coordinate through a semiring algebra by base change and the tensor unit equivalence |
| [`DedekindIdealArithmetic.Module.AdicIntegralSpan`](DedekindIdealArithmetic/Module/AdicIntegralSpan.lean) | `Module.adicIntegralSpan`, `Module.adicIntegralSpan_le_iff`, `Module.adicIntegralSpanMap`, `Module.range_adicIntegralSpanMap`, `Module.adicIntegralSpanEquiv`, `Module.mem_adicIntegralSpan_self_iff` | The valuation-integer span of integral sections is a scalar-extension image, finite when the original module is finite, equivalent to the integer tensor fibre for flat modules, and exactly the integer ring in the scalar model |
| [`DedekindIdealArithmetic.Module.AdicSeminorm`](DedekindIdealArithmetic/Module/AdicSeminorm.lean) | `LinearEquiv.adicSeminorm`, `LinearEquiv.adicSeminorm_eq`, `Module.adicSeminorm`, `Module.adicSeminorm_apply`, `Module.adicSeminorm_unique`, `Module.adicSeminorm_eq_zero_iff`, `Module.adicSeminorm_add_le_max`, `Module.adicSeminorm_self`, `Module.adicSeminorm_fixed_unit` | Definite, frame-independent ultrametric seminorms on adic fibres, with pure-tensor, integral-section and rational-fibre evaluations and whole-scalar-fibre normalization |
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

## Conventions and limitations

The [height guide](docs/RationalFrameHeight.md) explains the section-index
formula, rational frames and metric operations. Completion norms are unsquared;
archimedean weights are one at real places and two at complex places.
Multiplicative height has no degree root; `h = log H / [K : ℚ]` can be negative.
The nonzero fractional-ideal hypothesis is essential for norm factorization:
the zero ideal has norm zero but all counts zero. Finite-place products are
finite-support products, with no extra residue-degree weights.

The [adic-fibre guide](docs/AdicFibres.md) separates purely algebraic integral
spans from seminorms using the residue-cardinality normalization `q > 1`.
It explains signed counts, frame changes and zero coefficients. A supplied
frame's coordinate API works for compatible semiring algebras, including
noncommutative target semirings, without finiteness or norm assumptions.
No global norm on bare `K` or norm/metric instance on a module fibre is installed.

All tensor products here are algebraic, not completed. No equality of integral
spans with seminorm unit balls, module topology, closedness, completeness,
local tensor compatibility or finite-extension height transport is asserted.
Completeness of the scalar field alone gives no topology on a module fibre;
a bare `Seminorm` installs none. These results are not the full normed-module
height theory. Localization gives no injectivity, class-group computation or
concrete basic-open cover. The strict norm inequality excludes the zero ideal,
whose norm in an infinite ring is zero, whereas the unit ideal has norm one.

## Using the library

Add the dependency to your `lakefile.toml`:

```toml
[[require]]
name = "dedekind-ideal-arithmetic"
git = "https://github.com/FormalFrontier/dedekind-ideal-arithmetic.git"
rev = "main"
```

GitHub `main` contains reviewed releases. Lake resolves a release on first
addition or explicit update; `lake-manifest.json` retains that commit until
updated. To pin a specific release, replace `main` with its full GitHub commit.
Use compatible published releases with a common Lean toolchain and mathlib
revision throughout your dependency closure. Following `main` or overriding
only mathlib does not guarantee compatibility; retain the resolved manifest.

The library uses Lean's module system with explicit public declarations and
imports. Clients need an ordinary import, not implementation-private bodies:

```lean
module

import DedekindIdealArithmetic

example {S : Type*} [CommRing S] [IsDedekindDomain S]
    [Ring.HasFiniteQuotients S] [Infinite S] {I J : Ideal S}
    (hIJ : I ≤ J) (hnorm : I.absNorm = J.absNorm) : I = J :=
  Ideal.eq_of_le_of_absNorm_eq hIJ hnorm
```

[DedekindIdealArithmeticTest.lean](DedekindIdealArithmeticTest.lean) checks this
ordinary aggregate-import pattern, the six ideal-arithmetic results and their
composition with mathlib APIs, including zero/unit ideals, signed integer norm
witnesses and identity/trivial-class-group localizations. It is built by the
default target, not a library API to import. The aggregate does not expose
private client declarations as an import-all proof interface.

## Reproducible build and checks

Install [elan](https://github.com/leanprover/elan) and clone this repository.
The declared inputs are Lean `leanprover/lean4:v4.34.0-rc2` and mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`; `lake-manifest.json` locks all
transitive dependencies. No other Formal Frontier library is required.
From the repository root:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake build
```

Ensure the cache fetch succeeds. After removing `.lake` or changing pins,
fetch the matching cache again. The default build compiles the public library
and example module; to select them and elaborate the client explicitly:

```sh
lake build DedekindIdealArithmetic DedekindIdealArithmeticTest
lake env lean -DwarningAsError=true -T0 DedekindIdealArithmeticTest.lean
```

The last command makes warnings fatal; `-T0` disables the allocation-count
timeout, not kernel trust. It is not a stored-proof recheck or a complete
transitive axiom audit, including private and generated declarations.
[formalization.yaml](formalization.yaml) summarizes scope, not a declaration census.

## References

- J. S. Milne, *Abelian Varieties*, IV §6, 6.2–6.3. Reference for normed-module
  height conventions, tensor products, positive metric rescaling and isometry
  invariance; not the full rational, geometric or finite-extension theory.
- Charles A. Weibel, [*The K-book: An Introduction to Algebraic K-theory*](https://sites.math.rutgers.edu/~weibel/Kbook/Kbook.pdf),
  complete-book build dated 2013-08-29, Chapter I, section 3. Background for the
  motivating cyclotomic examples, not the whole book or concrete class-number
  computations.

## Formal sources and attribution

Authors: Formal Frontier Agents. The library uses mathlib's APIs and follows
its mathematical formalizations. Prism contributed norm order and
principal-prime extraction; Atlas contributed localization. AI agents have
participated in development, checking and review, without claims of human
authorship or independent certification. Full mathematical and formalization
credit, including Anchor and Prism's documentation tooling, is in
[CREDITS.md](CREDITS.md). Original contributions are licensed under
[Apache-2.0](LICENSE); upstream authorship and third-party notices remain applicable.
