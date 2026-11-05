# Credits and license

Authors: Formal Frontier Agents.

The mathematical references are listed in the [README](README.md#references).
The library uses mathlib at
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, with Lean
`leanprover/lean4:v4.34.0-rc2`.

## Mathematical formalization

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
finite-support products, and finite-place/height-one-prime equivalence. The adic
seminorm construction also uses mathlib's residue-cardinality completion norm,
`WithAbs` normed-field and algebra structures, `normSeminorm`, and
`TensorProduct.AlgebraTensorModule.cancelBaseChange`; it reuses this library's
rank-one seminorm scalar extension rather than choosing a norm on `K`.
The integral-span map reuses `LinearMap.liftBaseChange` and
`LinearMap.range_liftBaseChange`, together with Mathlib's flat-module API.

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

## Documentation tooling

Prism (AI agent) adapted the generator, tests and recipe from original Group Rings
tooling, itself adapted from Anchor's (AI agent) original Ideal Completion adapter.
This Dedekind adaptation changes the inventory, per-module ownership, displayed
assumptions and explanation. In group-rings, Prism added the
retained-input/explicit-refresh split and parentless controls to remove the
recipe's internal-Git-object dependency. Beacon supplied related portability
design advice, not copied implementation. These are original Formal Frontier
contributions under Apache-2.0.

Generated Markdown contains this project's docstrings and displayed mathematical
signatures, not copied dependency implementations or docstrings. No doc-gen4 web
assets are shipped. Lean, mathlib and doc-gen4 retain their credit and licenses
upstream. See the [documentation adapter provenance](docs/README.md#provenance)
and the [API-reference guide](docs/README.md) for reproduction and its limits.

## License and notices

Original Formal Frontier contributions are available under the
[Apache License, Version 2.0](LICENSE) (`Apache-2.0`). The collective author credit
does not identify a copyright holder or replace upstream authorship. Existing
copyright, attribution and license notices for reused third-party material
remain applicable. Dependency notices apply separately.

The library can be used solely through its declared dependencies.
