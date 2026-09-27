# dedekind-ideal-arithmetic

Reusable Lean theory of ideal norms, principal-prime extraction and localization
of ideal class groups. The library extends native mathlib ideals, algebraic
norms, localizations and class groups; it introduces no alternative encodings.

This is a development library undergoing initial release preparation. The Lake
package version is not a claim that an official release has been accepted.
Official status is established by a separate exact-commit acceptance and
publication record, not a mutable branch or package version.

## Mathematical scope

Import `DedekindIdealArithmetic` for the complete public interface, or one of
the three modules below for a smaller import. The [generated API reference](docs/API.md)
retains native displayed signatures and docstrings; its [reproduction contract](docs/README.md)
describes exact source/pin binding and its limits.

| Module | Public declarations | Meaning |
| --- | --- | --- |
| `DedekindIdealArithmetic.Ideal.AbsNorm` | `Ideal.absNorm_lt_absNorm_of_lt`, `Ideal.eq_of_le_of_absNorm_eq` | Strict ideal inclusion reverses absolute norm when the smaller ideal is nonzero; nested equal-norm ideals are equal, including the zero-ideal case |
| `DedekindIdealArithmetic.Ideal.PrincipalPrime` | `Ideal.exists_principal_prime_over_of_norm_natAbs_eq` | An element with prime absolute algebraic norm generates a principal prime above that rational prime |
| `DedekindIdealArithmetic.ClassGroup.Localization` | `ClassGroup.extendedHom_surjective_of_isLocalization`, `ClassGroup.isPrincipalIdealRing_of_generator_of_isLocalization`, `ClassGroup.uniqueFactorizationMonoid_of_generator_of_isLocalization` | Class-group extension to a Dedekind localization is onto; killing a generator of the source class group gives a PID and hence a UFD |

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

## Use from Lean

The library and its example module use Lean's native module system. Public
declarations and imports are explicit; downstream users need only an ordinary
import, not access to implementation-private bodies.

```lean
module

import DedekindIdealArithmetic

example {S : Type*} [CommRing S] [IsDedekindDomain S]
    [Ring.HasFiniteQuotients S] [Infinite S] {I J : Ideal S}
    (hIJ : I ≤ J) (hnorm : I.absNorm = J.absNorm) : I = J :=
  Ideal.eq_of_le_of_absNorm_eq hIJ hnorm
```

[DedekindIdealArithmeticTest.lean](DedekindIdealArithmeticTest.lean) checks this
pattern, all six public results and their composition with native mathlib APIs.
It includes the zero/unit-ideal boundary, positive and negative norm witnesses
in `ℤ`, identity localization and a localization of a ring with trivial class
group. It imports only `DedekindIdealArithmetic` through the ordinary public
interface and is built by the default target; it is not a library API to import.
Its examples are named private theorems, preserving their proof terms in the
compiled artifact for subsequent audits instead of relying on transient anonymous
examples. The short snippet above demonstrates the same public API pattern.

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
Release checks include a complete transitive standard-axiom audit covering
private/generated declarations, independent semantic and rights review, and
lightweight documentation, metadata and applicable lint checks. Applicable
successful build and axiom evidence may be reused. Separate stored-proof replay
and fresh expensive documentation generation are not release prerequisites.
A successful build alone does not establish release acceptance. At the
2026-09-25 21:56 UTC author checkpoint, this combined readiness successor is
unreviewed and no official release is claimed. That is a dated author snapshot,
not a live status feed. The six entries in [formalization.yaml](formalization.yaml)
summarize authored results, not a complete declaration census.

### Expected build cost

As a planning baseline, a clean rebuild of this library's five Lean modules
(including the test module) took **20.52 seconds** on 2026-09-25, with the matching
dependency cache already fetched. This is not a cold build of mathlib: the
`lake --no-cache --wfail -v build` run followed a project-only clean and retained
the dependency artifacts. Lake reported 2,380 jobs, including dependency replays.
Allow additional time for the initial cache download and for optional tooling.

The measurements used Linux, `LEAN_NUM_THREADS=2`, Lean `4.34.0-rc2` and the
mathlib pin above. They apply to the unchanged Lean sources, Lake configuration
and manifest of `f2f718d4e38f5b1a6ef1ce683a7ca8a405974bf6`.
These are individual wall-clock observations, not averages, performance promises
or measurements on the reader's hardware; the records do not identify the host
CPU model or competing workload.

| Measured workload | Elapsed time | Conditions and scope |
| --- | --- | --- |
| Clean project build | 20.52 s | Five project modules; matching dependency artifacts retained |
| Stock `leanchecker --verbose` over all five modules | 30.43 s | Already-built artifacts; a supplement, not the complete private/generated stored-proof audit |
| Native text-style lint | 81.52 s | Includes building the lint executable; not a steady-state lint estimate |
| Separate `doc-gen4` tool build | 139.53 s | Tool revision `97d4ecdfc8e09e7f511724c25e303d448de6a3db`; not the library build or full documentation-generation time |

The source-build recorder reported **1,391,684 KiB** of child-process maximum RSS
(about 1.33 GiB). By the stock-checker step, the full-check session's recorded
child-process high-water mark was **5,114,676 KiB** (about 4.88 GiB). These values
come from `getrusage(RUSAGE_CHILDREN).ru_maxrss`: the latter is cumulative across
earlier child processes, not an isolated checker measurement. Neither value is
aggregate concurrent memory use or a minimum RAM requirement. The runtime had a
23 GiB memory ceiling; that ceiling is not measured consumption. Plan for several
GiB plus headroom for simultaneous processes, particularly for full checks;
total peak memory and a minimum supported machine size were not measured.
No new timing or memory experiment was run for this documentation-only addition.

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
license notices remain part of the upstream dependency.

Prism contributed the norm-order and principal-prime formalizations; Atlas
contributed the class-group/localization formalization. Development, checking
and review have involved AI agents in the Formal Frontier project; these are
agent identities, not claims of human authorship or independent certification.
The source-maintainer team collectively maintains the library, with Prism
responsible for the current initial release preparation. Detailed passage
correspondence and coverage of motivating texts stay in the source metadata
repositories and are not prerequisites for using this API.

The norm-order and principal-prime proof expression adapts Prism's earlier
original project arguments in source-weibel-k-book at
`8b0d0347624478ed09a16007ab53ed27cabc40c0` and
`16d8877c99c829de930d5a1c941fcc328e06aeb3`, in the respective
`ChapterI3CyclotomicThirteenBoundaryDiagnostic.lean` and
`ChapterI3CyclotomicSeventeenBoundaryDiagnostic.lean` experiment files.
This is internal expression reuse, not merely a bibliographic influence or a
claim of wholly new proof text. No book excerpt or cyclotomic computation is
shipped. The metadata preserves the precise relationships and source-access limits.
The [documentation adapter provenance](docs/README.md#provenance)
credits Anchor and Prism's original tooling and this library's adaptation.

Original Formal Frontier contributions are available under the
[Apache License, Version 2.0](LICENSE) (`Apache-2.0`). The collective author credit
does not identify a copyright holder or replace upstream authorship. Existing
copyright, attribution and license notices for reused third-party material
remain applicable. Dependency notices apply separately.

The library can be used solely through its declared dependencies; internal
project discussions and source-coverage records are not build prerequisites.
