/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import DedekindIdealArithmetic.ClassGroup.Localization
public import DedekindIdealArithmetic.Ideal.AbsNorm
public import DedekindIdealArithmetic.Ideal.FractionalNorm
public import DedekindIdealArithmetic.Ideal.PrincipalPrime
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
from element norms, localization of ideal class groups, and heights of normed
invertible modules over number fields. The metric API includes tensor products,
positive rescaling, pullback along module equivalences, and placewise evaluation
on rational fibres with explicit archimedean norm data.

Over a fraction field, rational frames identify finite torsion-free modules
with their coefficient ideals, without choosing an integral basis. Scalar
extension of seminorms on lines and isometric maps between archimedean
completions provide further auxiliary constructions. Weighted products over
restricted infinite places satisfy the relative extension-degree formula.
Fractional-ideal absolute norms satisfy the relative-rank extension formula
for torsion-free extensions of Dedekind domains finite free over the integers.

A rational frame evaluates the intrinsic height through the absolute norm of
its coefficient ideal and the weighted archimedean product of its unit vector.
Nonzero fractional-ideal norms are finite-support products of prime norms raised
to their signed exponents. The height therefore also has a finite-place exponent
formula. The index comparison holds also for zero sections; the height formulas
concern invertible modules and do not assume an integral basis. Norms on finite
completion fibres, local-frame transport and finite-extension height transport
are not provided. The individual modules document the hypotheses and interfaces.
-/
