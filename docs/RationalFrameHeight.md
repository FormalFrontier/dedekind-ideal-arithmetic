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

## Frame changes and metric rescaling

For another frame `e'`, put \(z=e'(e^{-1}(1))\ne0\). The laws
`LinearEquiv.coefficientMap_eq_smul` and
`LinearEquiv.coefficientIdeal_eq_spanSingleton_mul` give \(I'=zI\), while
\(u'=z^{-1}u\). The ideal norm acquires \(|N_{K/\mathbf Q}(z)|\), and the
weighted archimedean product acquires its inverse. Every frame therefore gives
the same right-hand side, also directly because it equals `P.height`.

Positive metric rescaling is a different operation. `P.rescale c` leaves `I`
unchanged and multiplies each rational evaluation by `((c v : ℝ≥0) : ℝ)`.
The reciprocal formula divides height by
\(\prod_v c_v^{\operatorname{mult}(v)}\), as in `height_rescale`.

For the standard unit metric on `𝓞 K` and the multiplication frame,
`coefficientIdeal_rid` and `unit_rationalEval_one` make both factors one,
agreeing with `unit_height`. Constant positive rescaling by \(t\) gives
height \(t^{-n}\) and normalized logarithmic height \(-\log t\). These
metrics illustrate both the reciprocal convention and genuine variation.

## Scope

These are fixed-field evaluations of the intrinsic height. They do not supply
explicit finite-place local norms, finite-place support, a local-frame height
formula, or height transport through finite extensions. A dual-evaluation
interpretation via the inverse coefficient ideal is not required for the
index proof and is not asserted here.
