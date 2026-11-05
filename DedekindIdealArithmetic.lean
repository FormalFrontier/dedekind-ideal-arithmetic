/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import DedekindIdealArithmetic.ClassGroup.Localization
public import DedekindIdealArithmetic.Ideal.AbsNorm
public import DedekindIdealArithmetic.Ideal.AdicNorm
public import DedekindIdealArithmetic.Ideal.CountAttainment
public import DedekindIdealArithmetic.Ideal.FractionalNorm
public import DedekindIdealArithmetic.Ideal.PrincipalPrime
public import DedekindIdealArithmetic.Module.AdicIntegralSpan
public import DedekindIdealArithmetic.Module.AdicSeminorm
public import DedekindIdealArithmetic.Module.CoefficientIdeal
public import DedekindIdealArithmetic.Module.CoefficientIdealNorm
public import DedekindIdealArithmetic.Module.RankOneSeminorm
public import DedekindIdealArithmetic.NumberField.Completion.Extension
public import DedekindIdealArithmetic.NumberField.FinitePlaceHeight
public import DedekindIdealArithmetic.NumberField.InfinitePlaceProducts
public import DedekindIdealArithmetic.NumberField.MetricRescaling
public import DedekindIdealArithmetic.NumberField.MetricTensorProduct
public import DedekindIdealArithmetic.NumberField.MetricTransport
public import DedekindIdealArithmetic.NumberField.ModuleHeight
public import DedekindIdealArithmetic.NumberField.RationalFibre
public import DedekindIdealArithmetic.NumberField.RationalFrameHeight

/-!
# Dedekind ideal arithmetic

Public entry point for ideal absolute-norm order comparison, principal primes
from element norms, localization of ideal class groups, canonical ultrametric
seminorms on adic fibres, and heights of normed invertible modules over number
fields. The archimedean metric API includes tensor products, positive rescaling,
pullback along module equivalences, and evaluation on rational fibres.

A supplied rational frame gives coordinates on scalar-extended fibres, including
over semiring algebras whose target need not be commutative. These coordinates
require no arithmetic, finiteness or norm hypotheses. Over a fraction field,
rational frames identify finite torsion-free modules with their nonzero
coefficient ideals, without choosing an integral basis.

At each fixed height-one prime of any Dedekind domain, a nonzero fractional
ideal contains a nonzero element whose principal fractional ideal attains its
signed prime exponent. No principality or residue-finiteness hypothesis is needed.

The adic valuation-integer ring `O` spans the integral sections inside each
algebraic adic fibre. This span is the image of `O ⊗[R] M`, is finite over `O`
when `M` is finite over `R`, and spans the whole fibre over the completion field.
For flat `M` the image map is an equivalence onto this span; for `M = R` the
whole span corresponds exactly to `O` under the tensor right-unit equivalence.
These algebraic statements require neither infinite rings nor finite quotients.

For an infinite Dedekind domain `R` with finite quotients, fraction field `K`,
height-one prime `p` and invertible `R`-module `M`, `Module.adicSeminorm` is a
canonical definite ultrametric `F`-seminorm on `F ⊗[R] M`, where
`F = p.adicCompletion K` has its residue-cardinality norm. In every rational
frame `e`, its value at every `x` is
`(Ideal.absNorm p.asIdeal : ℝ) ^ FractionalIdeal.count K p e.coefficientIdeal *
  ‖e.fibreCoordinate F x‖`.
The supplied-frame constructor `LinearEquiv.adicSeminorm` requires only a
finitely generated module and a rational frame, not integral invertibility,
freeness or torsion-freeness. The seminorm is frame-independent and uniquely determined by
its coefficient-ideal weight at a rational unit vector. The API evaluates pure
tensors, integral sections and rational-fibre vectors. On the scalar module,
the whole seminorm is the completion norm composed with the tensor right-unit
equivalence, and the same vector `1 ⊗ 1` has value one in every scalar frame.

This construction uses Mathlib's `WithAbs` tag for the adic absolute value, the
norm-preserving algebra map to `F`, rank-one seminorm scalar extension and an
`F`-linear base-change cancellation. No norm or metric instance is installed on
`K` or on a module fibre; no number-field or finite-free-over-integers hypothesis
is required. The universes of `R`, `K` and `M` are independent.

For number fields, a rational frame evaluates the intrinsic height through its
coefficient-ideal norm and the weighted archimedean product at its unit vector.
Nonzero fractional-ideal norms are finite-support products of prime norms raised
to their signed exponents. The height therefore also has a finite-place formula
with negative coefficient-ideal exponents. The plus sign on the count in the
adic seminorm does not change this height formula or define a second height.

Scalar extension of seminorms on lines and isometric maps between archimedean
completions provide further constructions. Weighted products over restricted
infinite places satisfy the relative extension-degree formula. Fractional-ideal
norms satisfy the relative-rank extension formula for torsion-free extensions of
Dedekind domains finite free over the integers. The index comparison includes
zero sections; the height formulas concern invertible modules without an
integral basis. The adic fibres are algebraic tensor products: completed-lattice
constructions, unit-ball identifications, local tensor compatibility and
finite-extension height transport remain open. The individual modules document
the hypotheses and interfaces.
-/
