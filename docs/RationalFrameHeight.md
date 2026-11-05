# Evaluating intrinsic height in a rational frame

For a number field `K`, an invertible module `M` over its ring of integers
`𝓞 K`, and `P : NumberField.ArchimedeanNorms K M`, the theorem
`NumberField.ArchimedeanNorms.height_eq_rationalFrame` evaluates the existing
intrinsic height in any supplied rational frame

\[
 e:K\otimes_{\mathcal O_K}M\xrightarrow{\sim}K.
\]

Write \(u=e^{-1}(1)\) and
\(I=\{e(1\otimes m):m\in M\}\). The fractional ideal \(I\) is
`e.coefficientIdeal`, not additional arithmetic data. Then

\[
 \boxed{\quad
 H(P)=\left(N(I)\prod_{v\mid\infty}P_v(u)^{\operatorname{mult}(v)}\right)^{-1}.
 \quad}
\]

The formal interface is in
[`RationalFrameHeight.lean`](../DedekindIdealArithmetic/NumberField/RationalFrameHeight.lean):

```lean
NumberField.ArchimedeanNorms.height_eq_rationalFrame
  (P : NumberField.ArchimedeanNorms K M)
  (e : K ⊗[𝓞 K] M ≃ₗ[K] K)
```

Invertibility supplies finiteness, projectivity, flatness and torsion-freeness
through the module instances. No integral trivialization or assumption
`Module.Free (𝓞 K) M` is needed. The frame is supplied explicitly; the
left-hand side has no frame argument and no second height is defined.

## Intrinsic height and sections

The intrinsic construction is in
[`ModuleHeight.lean`](../DedekindIdealArithmetic/NumberField/ModuleHeight.lean).
For **every** nonzero integral section `m`, write `m_v = 1 ⊗ m`. Then

\[
 H(P)=\frac{\#(M/\mathcal O_Km)}
            {\prod_{v\mid\infty}P_v(m_v)^{\varepsilon_v}},\qquad
 h(P)=\frac{\log H(P)}{[K:\mathbf Q]},\qquad
 \varepsilon_v=\begin{cases}1&v\text{ real},\\2&v\text{ complex}.\end{cases}
\]

The numerator is `Submodule.cardQuot (Submodule.span (𝓞 K) {m})`, not
prescribed index data. Finiteness of this quotient, positivity of the norm
product and independence of the nonzero section are conclusions, not fields
of the metric. Nonprincipal invertible modules are included. No norm instance
on `M` or on a completion tensor fibre is required. The standard unit metric
on `𝓞 K` has `H = 1` and `h = 0`.

The generic index API in
[`Index.lean`](../DedekindIdealArithmetic/Module/Index.lean) supports this
construction. For an injective linear map `f : M →ₗ[R] N` and a submodule
`S`, it gives

\[
 \#(N/f(S))=\#(M/S)\,\#(N/\operatorname{range}f).
\]

Neither quotient is assumed finite; infinite quotients have `cardQuot = 0`.
Over a domain, scaling a nonzero section of a torsion-free module multiplies
its quotient index by the principal left-ideal index, including zero scalars
and infinite quotients. For an infinite Dedekind domain this scalar factor
is the absolute norm of the scalar's principal ideal. Over a commutative
domain with finite quotients, invertible modules have finite quotients by
nonzero sections. Any two nonzero sections of an invertible module over a
commutative domain admit a common nonzero scalar multiple.

## Meaning and normalization

- `ArchimedeanNorms` gives definite seminorms on all vectors of the completion
  fibres `v.Completion ⊗[𝓞 K] M`. The completion norms are ordinary, unsquared
  norms, with multiplicity one at real places and two at complex places.
- `P.rationalEval v u`, from
  [`RationalFibre.lean`](../DedekindIdealArithmetic/NumberField/RationalFibre.lean),
  evaluates that seminorm after the canonical scalar-extension map. Its scalar
  law uses `‖algebraMap K v.Completion a‖ = v a`. Different infinite places do
  not require competing normed-field instances on `K`.
- `FractionalIdeal.absNorm` takes values in `ℚ`; its value is cast to `ℝ` in
  the height formula. It extends integral ideal norm multiplicatively and
  sends a principal fractional ideal `(a)` to `|Algebra.norm ℚ a|`. It has no
  reciprocal hidden in its definition.
- Multiplicative height has **no degree root**. The theorem
  `normalizedLogHeight_eq_rationalFrame` states, with \(n=[K:\mathbf Q]\),
  \[
   h(P)=\frac{-\log N(I)-
       \sum_{v\mid\infty}\operatorname{mult}(v)\log P_v(u)}{n}.
  \]
  All factors in the reciprocal are positive. Neither `H(P) ≥ 1` nor
  `h(P) ≥ 0` is asserted.

The generic `Seminorm.extendScalarsRankOne` interface in
[`RankOneSeminorm.lean`](../DedekindIdealArithmetic/Module/RankOneSeminorm.lean)
explains seminorm extension on a line. It is not additional data in these
height formulas.

## Arithmetic comparison

Two generic index/norm laws isolate the arithmetic calculation.

1. `FractionalIdeal.absNorm_spanSingleton_eq_cardQuot_mul`, in
   [`FractionalNorm.lean`](../DedekindIdealArithmetic/Ideal/FractionalNorm.lean),
   works for a Dedekind domain `R` finite free over `ℤ`, a fraction field `F`,
   a fractional ideal `J`, and **every** `x : J`, including zero:
   \[
    N((x))=\#(J/Rx)\,N(J).
   \]
   It also includes the zero ideal. Infinite quotient cardinalities are
   interpreted as zero, following `Submodule.cardQuot`.
2. `LinearEquiv.cardQuot_span_singleton_mul_absNorm_coefficientIdeal`, in
   [`CoefficientIdealNorm.lean`](../DedekindIdealArithmetic/Module/CoefficientIdealNorm.lean),
   transports this identity through the coefficient range equivalence. For
   a finite torsion-free `R`-module with a rational frame, it gives
   \[
    \#(M/Rm)\,N(I)=N((e(1\otimes m)))
   \]
   for **every** section. It assumes neither invertibility nor freeness over
   `R`, and does not need a number-field structure on the fraction field.

For the first law, Mathlib's `FractionalIdeal.equivNum` identifies `J` with
its denominator-cleared integral ideal `J.num`. Compose this equivalence
with the integral ideal's subtype map into `R`, and apply
`Submodule.cardQuot_map_of_injective` to the span of `x`. The integral ideal
norm is its quotient index. Multiplicativity and
`FractionalIdeal.den_mul_self_eq_num'` then cancel the norm of the nonzero
denominator principal ideal. This does not require an integral basis of `J`.
The second law uses the existing
`LinearEquiv.ofInjective e.coefficientMap e.coefficientMap_injective`.

Over a number field, put \(a=e(1\otimes m)\). Mathlib's
`FractionalIdeal.absNorm_span_singleton` specializes the arithmetic identity to

\[
 \#(M/\mathcal O_Km)\,N(I)=|N_{K/\mathbf Q}(a)|.
\]

The theorem `ArchimedeanNorms.normProduct_eq_rationalFrame` gives the
independent archimedean identity

\[
 \prod_{v\mid\infty}P_v(1\otimes m)^{\operatorname{mult}(v)}
 =|N_{K/\mathbf Q}(a)|
   \prod_{v\mid\infty}P_v(u)^{\operatorname{mult}(v)}.
\]

It follows from `1 ⊗ m = a • u`, rational-evaluation homogeneity and
`InfinitePlace.prod_eq_abs_norm`. This identity needs no finiteness,
torsion-freeness or invertibility assumption on `M`. For an invertible module,
choose a nonzero integral section, substitute both identities into `height_eq`,
and cancel its positive finite quotient index. Taking logarithms yields the
normalized formula.

## Finite-place exponents

The generic norm factorization
`FractionalIdeal.absNorm_eq_finprod_count`, in
[`FractionalNorm.lean`](../DedekindIdealArithmetic/Ideal/FractionalNorm.lean),
works for a Dedekind domain `R` finite free over `ℤ`, a fraction field `F`,
and a **nonzero** fractional ideal `J`:

\[
 N(J)=\prod_{\mathfrak p}^{\mathrm{fin}}
       N(\mathfrak p)^{c_{\mathfrak p}(J)},\qquad
 c_{\mathfrak p}(J)=\texttt{FractionalIdeal.count}\ F\ \mathfrak p\ J.
\]

Here the primes are `IsDedekindDomain.HeightOneSpectrum R`, and the equality
is in `ℚ`. No number-field structure, `ℚ`-algebra structure on `F` or integral
basis is assumed. The exponents are signed integers in the factorization
`J = ∏ᶠ 𝔭, 𝔭 ^ c_𝔭(J)`: positive exponents give ideal factors, while negative
exponents give inverse ideal factors. Mathlib supplies this factorization and
its finite-support API; multiplicativity of its fractional-ideal norm gives
the displayed norm identity.

For a number field, a finite place `w : NumberField.FinitePlace K`
corresponds to the height-one prime
`𝔭_w = w.maximalIdeal.asIdeal`. Put

\[
 q_w=\#(\mathcal O_K/\mathfrak p_w),\qquad
 c_w(J)=\texttt{FractionalIdeal.count}\ K\ w.\texttt{maximalIdeal}\ J.
\]

Thus `q_w = Ideal.absNorm w.maximalIdeal.asIdeal`; it is the full residue
cardinality, not just the rational prime below `w`. If that prime is `p` and
the residue degree is `f_w`, then `q_w = p ^ f_w`. There are no extra
residue-degree, ramification or other finite-place weights.
`NumberField.FinitePlace.absNorm_eq_finprod_count` casts the norm identity to
`ℝ` and reindexes it using Mathlib's finite-place/height-one-prime equivalence:

\[
 N(J)=\prod_{w\nmid\infty}^{\mathrm{fin}}q_w^{c_w(J)}\quad(J\ne0).
\]

These are **finite-support products**, written `∏ᶠ` (`finprod`) in Lean.
Only finitely many exponents are nonzero, so all remaining factors equal one;
no analytic convergence or limiting product is involved. The hypothesis
`J ≠ 0` is essential: `count` is zero at the zero ideal, so its displayed
product would be one, whereas its absolute norm is zero. The zero-inclusive
index/norm laws in the preceding section are distinct statements.

Substituting `J = I = e.coefficientIdeal` in the reciprocal formula gives

\[
 \boxed{\quad
 H(P)=\frac{\displaystyle\prod_{w\nmid\infty}^{\mathrm{fin}}q_w^{-c_w(I)}}
             {\displaystyle\prod_{v\mid\infty}
                  P_v(u)^{\operatorname{mult}(v)}}.
 \quad}
\]

This is `NumberField.ArchimedeanNorms.height_eq_finitePlace`, in
[`FinitePlaceHeight.lean`](../DedekindIdealArithmetic/NumberField/FinitePlaceHeight.lean).
The numerator has the **negative** coefficient-ideal exponents because it is
`N(I)⁻¹`. The denominator uses `P.rationalEval v (e.symm 1)`, with weight
one at real places and two at complex places. The theorem assumes
`Module.Invertible (𝓞 K) M` and a supplied rational frame, not an integral
basis, a chosen section or additional metric data. The coefficient ideal is
nonzero by `e.coefficientIdeal_ne_zero`, so the zero-ideal boundary requires
no extra hypothesis in the height theorem. It evaluates the same `P.height`,
not a new height or a family of finite-place norms. The normalization is
unchanged: no degree root in multiplicative height; the logarithmic formula
above is `normalizedLogHeight_eq_rationalFrame`.

## Frame changes and metric rescaling

For another frame `e'`, put \(z=e'(e^{-1}(1))\ne0\). The laws
`LinearEquiv.coefficientMap_eq_smul` and
`LinearEquiv.coefficientIdeal_eq_spanSingleton_mul` give \(I'=zI\), while
\(u'=z^{-1}u\). The ideal norm acquires \(|N_{K/\mathbf Q}(z)|\), and the
weighted archimedean product acquires its inverse. Every frame therefore gives
the same right-hand side, also directly because it equals `P.height`.

Positive metric rescaling is a different operation. `P.rescale c`, for
`c : InfinitePlace K → ℝ≥0ˣ`, leaves `I` unchanged and multiplies each
whole-fibre seminorm, hence each rational evaluation, by
`((c v : ℝ≥0) : ℝ)`. For invertible integral modules with metrics `P, Q`
and an integral module equivalence `f : M ≃ₗ[𝓞 K] N`, the metric laws are

\[
\begin{aligned}
 H(P\otimes Q)&=H(P)H(Q), & h(P\otimes Q)&=h(P)+h(Q),\\
 H(cP)&=\frac{H(P)}{\prod_v c_v^{\varepsilon_v}}, &
 h(cP)&=h(P)-\frac{\sum_v\varepsilon_v\log c_v}{[K:\mathbf Q]},\\
 H(f^*Q)&=H(Q), & h(f^*Q)&=h(Q).
\end{aligned}
\]

The tensor metric multiplies norms on pure tensors of completion-fibre
vectors. Here `cP = P.rescale c` and `f*Q = Q.comap f`; the latter specifies
metric pullback, not invariance under an arbitrary change of metric.
The corresponding APIs are in
[`MetricTensorProduct.lean`](../DedekindIdealArithmetic/NumberField/MetricTensorProduct.lean),
[`MetricRescaling.lean`](../DedekindIdealArithmetic/NumberField/MetricRescaling.lean)
and [`MetricTransport.lean`](../DedekindIdealArithmetic/NumberField/MetricTransport.lean).

For the standard unit metric on `𝓞 K` and the multiplication frame,
`coefficientIdeal_rid` and `unit_rationalEval_one` make both factors one;
all finite-place exponents vanish, agreeing with `unit_height`.
Constant positive rescaling by \(t\) gives
height \(t^{-n}\) and normalized logarithmic height \(-\log t\). These
metrics illustrate both the reciprocal convention and genuine variation.

## Scope

These are fixed-field evaluations of the intrinsic height, including an
arithmetic finite-place exponent formula with finite support. The separate
[adic-fibre guide](AdicFibres.md) describes canonical seminorms on
finite-completion fibres and their algebraic integral spans. Neither account
identifies those spans with seminorm unit balls or provides local tensor
compatibility or height transport through finite extensions. These results
do not supply the full normed-module height theory. A dual-evaluation
interpretation via the inverse coefficient ideal is not required for the
index proof and is not asserted here.

The library does contain isometric completion maps over field extensions in
[`Completion/Extension.lean`](../DedekindIdealArithmetic/NumberField/Completion/Extension.lean),
multiplicity-weighted restriction laws for arbitrary commutative-monoid
products and additive-commutative-monoid sums over infinite places in
[`InfinitePlaceProducts.lean`](../DedekindIdealArithmetic/NumberField/InfinitePlaceProducts.lean),
and the relative-rank fractional-ideal norm extension formula for
torsion-free extensions of Dedekind domains finite free over `ℤ` in
[`FractionalNorm.lean`](../DedekindIdealArithmetic/Ideal/FractionalNorm.lean).
These scalar and arithmetic comparisons are distinct from height transport.
