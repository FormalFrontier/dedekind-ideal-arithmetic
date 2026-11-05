# Adic fibres, integral spans and canonical seminorms

Let `R` be a commutative Dedekind domain, `K` its fraction field and
`p : IsDedekindDomain.HeightOneSpectrum R` a fixed height-one prime. Write

\[
 F=p.\texttt{adicCompletion}\ K,\qquad
 O=p.\texttt{adicCompletionIntegers}\ K,\qquad V=F\otimes_R M.
\]

Here `O` is Mathlib's valuation-integer ring, a `ValuationSubring F`.
The tensor product is algebraic. The universes of `R`, `K` and `M` are
independent. Integral spans and seminorms have different hypotheses and APIs;
in particular, the algebraic span is not defined as a seminorm unit ball.

## Signed counts and scalar norms

For a fractional ideal `I`, put
\(c_p(I)=\texttt{FractionalIdeal.count}\ K\ p\ I\in\mathbb Z\).
These are signed factorization exponents, not their positive parts.

Over any such `R` and `K`, every **nonzero** fractional ideal `I` contains an
`a ≠ 0` with

\[
 c_p((a))=c_p(I).
\]

This is `FractionalIdeal.exists_mem_count_spanSingleton_eq` in
[`CountAttainment.lean`](../DedekindIdealArithmetic/Ideal/CountAttainment.lean).
Mathlib's existing `FractionalIdeal.count_mono` gives
\(c_p(I)\leq c_p((a))\) for each nonzero `a ∈ I`, so the count is an
attained minimum. The witness is chosen separately for each prime; there is
no simultaneous generator or principality assertion. Negative exponents are
included. No infinite-ring, finite-quotient or finite-free-over-`ℤ` hypothesis
is needed.

For a nonzero scalar `a : K`,
[`AdicNorm.lean`](../DedekindIdealArithmetic/Ideal/AdicNorm.lean) gives

\[
 p.\mathrm{valuation}(a)=\operatorname{exp}(-c_p((a))).
\]

This valuation identity also needs no residue-field finiteness. If `R` is
infinite and has `Ring.HasFiniteQuotients R`, let
\(q=\texttt{Ideal.absNorm}\ p.\texttt{asIdeal}=\#(R/p)>1\).
Mathlib's selected norm on `F` uses this full residue cardinality, and

\[
 \|\operatorname{algebraMap}_{K,F}(a)\|_F=q^{-c_p((a))},\qquad
 q^{c_p((a))}\|\operatorname{algebraMap}_{K,F}(a)\|_F=1.
\]

The corresponding declarations are
`valuation_eq_exp_neg_count_spanSingleton`,
`norm_algebraMap_eq_zpow_neg_count_spanSingleton` and
`zpow_count_spanSingleton_mul_norm_algebraMap_eq_one`, in the namespace
`IsDedekindDomain.HeightOneSpectrum`. No norm on bare `K` is chosen.
For a number-field finite place, `NumberField.FinitePlace.norm_algebraMap`
also identifies the restricted completion norm with that place.

The exponent formulas require `a ≠ 0`: `count` of the zero fractional ideal
is zero, but the norm of zero is zero, not `q ^ 0`. The separate formula
`norm_algebraMap_eq_adicAbv` includes zero.

## Algebraic integral spans

For **any** `M` with `[AddCommGroup M] [Module R M]`,
[`AdicIntegralSpan.lean`](../DedekindIdealArithmetic/Module/AdicIntegralSpan.lean)
defines

\[
 L_p(M)=\operatorname{span}_O\{1\otimes m:m\in M\}\subseteq V.
\]

This is `Module.adicIntegralSpan`. Its section and universal-property API is
`one_tmul_mem_adicIntegralSpan` and `adicIntegralSpan_le_iff`: an
`O`-submodule contains `L_p(M)` exactly when it contains every `1 ⊗ m`.

The canonical `O`-linear map

\[
 T:O\otimes_R M\longrightarrow V,\qquad o\otimes m\longmapsto o\otimes m
\]

is `Module.adicIntegralSpanMap`, defined with `LinearMap.liftBaseChange`.
Its pure-tensor formula is `adicIntegralSpanMap_tmul`, and
`range_adicIntegralSpanMap` says `range T = L_p(M)`, reusing Mathlib's
`LinearMap.range_liftBaseChange`.

- If `[Module.Finite R M]`, the instance `instFiniteAdicIntegralSpan` makes
  `L_p(M)` finite over `O`.
- Its `F`-span is the whole `V`, by `span_adicIntegralSpan_eq_top`, without
  finiteness or flatness of `M`.
- If `[Module.Flat R M]`, `adicIntegralSpanMap_injective` makes `T`
  injective, and `adicIntegralSpanEquiv` gives
  `O ⊗[R] M ≃ₗ[O] L_p(M)`. Its underlying map into `V` is `T`, as stated
  by `adicIntegralSpanEquiv_apply`. Invertible modules supply flatness.
- For `M = R`, `mem_adicIntegralSpan_self_iff` applies to **every**
  `x : F ⊗[R] R`:
  \[
   x\in L_p(R)\quad\Longleftrightarrow\quad
   (\texttt{TensorProduct.AlgebraTensorModule.rid}\ R\ F\ F)(x)\in O.
  \]

None of these span/map statements requires an infinite ring, finite residue
fields, a normed-field instance, a seminorm, torsion-freeness of `M`, or a
global generator. Flatness is used only for the injectivity and equivalence.

## Coordinates in a supplied frame

A frame `e : K ⊗[R] M ≃ₗ[K] K` supplies

```lean
e.fibreCoordinate F : F ⊗[R] M ≃ₗ[F] F
```

from [`CoefficientIdeal.lean`](../DedekindIdealArithmetic/Module/CoefficientIdeal.lean).
On pure tensors its value is
`a * algebraMap K F (e.coefficientMap m)`; it sends the image of `e.symm 1`
to one. The inverse, unit-vector and frame-change formulas are part of the
same coordinate API, built using
[`TensorCoordinates.lean`](../DedekindIdealArithmetic/Module/TensorCoordinates.lean).

This coordinate construction is more general than the adic setting: it works
for compatible semiring algebras, including a possibly noncommutative target
semiring. It assumes no finiteness, torsion-freeness, invertibility,
fraction-field structure or norm. The coefficient **fractional ideal** and
the seminorm construction below have their own stronger hypotheses.

## Canonical seminorms

Now assume that `R` is infinite with finite quotients. For a finite
`R`-module `M` and a supplied rational frame `e`, put
`I_e = e.coefficientIdeal`. This ideal is nonzero. The constructor
`LinearEquiv.adicSeminorm` in
[`AdicSeminorm.lean`](../DedekindIdealArithmetic/Module/AdicSeminorm.lean)
defines a definite ultrametric `F`-seminorm by the whole-fibre formula

\[
 \boxed{\quad N_p(x)=q^{+c_p(I_e)}
              \|e.\mathrm{fibreCoordinate}\ F\,(x)\|_F
              \quad(x\in V).\quad}
\]

The exponent is the **signed** count with a **plus** sign; it may be
negative. The supplied-frame constructor requires finiteness and the frame,
not integral invertibility, freeness or torsion-freeness; torsion in `M` is
allowed. `LinearEquiv.adicSeminorm_eq` identifies the constructions from any
two supplied frames under these same hypotheses.

For `[Module.Invertible R M]`, `Module.adicSeminorm` chooses a rational
frame and is independent of it. Its characteristic formula
`Module.adicSeminorm_apply` holds in **every** frame for **every** fibre
vector. The API includes:

- `adicSeminorm_eq_zero_iff`: `N_p(x) = 0 ↔ x = 0`;
- `adicSeminorm_add_le_max`: `N_p(x + y) ≤ max (N_p(x)) (N_p(y))`;
- `adicSeminorm_smul`: `N_p(a • x) = ‖a‖ * N_p(x)` for `a : F`;
- `adicSeminorm_apply_unitVector`: the image of `e.symm 1` has value
  `q ^ c_p(I_e)`; `adicSeminorm_unique` says this value characterizes the
  seminorm among `F`-seminorms;
- `adicSeminorm_apply_tmul`, `adicSeminorm_apply_one_tmul` and
  `adicSeminorm_apply_rationalFibre`: evaluation on pure tensors, integral
  sections and the entire rational fibre.

The last three evaluations use
`NumberField.HeightOneSpectrum.adicAbv K p` on the coefficient in `K`.
For example, for `a : F` and `m : M`,

\[
 N_p(a\otimes m)=q^{c_p(I_e)}\|a\|_F
     |e(1\otimes m)|_p.
\]

At a zero coefficient this value is zero; one must not substitute its count
into the nonzero principal-ideal exponent formula.

Under a frame change with nonzero multiplier `z`, the coefficient ideal
changes to `z I_e` and the fibre coordinate is multiplied by `z`.
The principal-weight cancellation above makes the two changes cancel.
This explains the plus sign. It does not change the **negative** exponents
in the finite-place height numerator in the
[rational-frame height guide](RationalFrameHeight.md#finite-place-exponents),
or define a second height.

## Scalar normalization and construction

For `M = R`, `Module.adicSeminorm_self` identifies the **whole** seminorm as

```lean
(normSeminorm F F).comp
  (TensorProduct.AlgebraTensorModule.rid R F F).toLinearMap
```

`adicSeminorm_one_tmul_one` gives value one at `1 ⊗ 1`.
`adicSeminorm_fixed_unit` says that in **every** scalar frame the coefficient
weight and coordinate norm cancel at this same fixed vector, not merely at
a frame-dependent unit vector.

The construction tags the fraction field as
`A = WithAbs (NumberField.HeightOneSpectrum.adicAbv K p)`.
`norm_algebraMap_withAbs` proves norm compatibility of `A → F`, giving
`normedAlgebraAdicCompletion : NormedAlgebra A F`. It then reuses
`Seminorm.extendScalarsRankOne` and the `F`-linear base-change cancellation
`TensorProduct.AlgebraTensorModule.cancelBaseChange`. It installs no global
norm on bare `K` or norm/metric instance on a module fibre. No number-field
structure, finite-free presentation over `ℤ` or integral basis is required.

## Boundaries

The algebraic integral span and the seminorm are separate constructions;
no theorem here identifies `L_p(M)` with `{x | N_p(x) ≤ 1}`. No completed
tensor product, module topology, closedness, completeness, local tensor
compatibility or finite-extension height transport is asserted. A bare
`Seminorm F V` installs no topology on `V`; completeness of the scalar field
`F` alone does not give such a topology or prove the fibre complete.
