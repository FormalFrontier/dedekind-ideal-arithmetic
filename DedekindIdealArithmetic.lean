/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import DedekindIdealArithmetic.ClassGroup.Localization
public import DedekindIdealArithmetic.Ideal.AbsNorm
public import DedekindIdealArithmetic.Ideal.PrincipalPrime
public import DedekindIdealArithmetic.Module.CoefficientIdeal
public import DedekindIdealArithmetic.Module.RankOneSeminorm
public import DedekindIdealArithmetic.NumberField.Completion.Extension
public import DedekindIdealArithmetic.NumberField.MetricRescaling
public import DedekindIdealArithmetic.NumberField.MetricTensorProduct
public import DedekindIdealArithmetic.NumberField.MetricTransport
public import DedekindIdealArithmetic.NumberField.ModuleHeight

/-!
# Dedekind ideal arithmetic

Public entry point for ideal absolute-norm order comparison, principal primes
from element norms, localization of ideal class groups, and heights of normed
invertible modules over number fields. The metric API includes tensor products,
positive rescaling, and pullback along module equivalences. Coefficient ideals
in rational frames, scalar extension of seminorms on lines, and isometric maps
between archimedean completions provide auxiliary constructions.

The individual modules document the hypotheses and interfaces.
-/
