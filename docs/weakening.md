# Results from the literature

The proof of `main` uses results on Lorentzian geometry, ordinary differential equations
and wave equations from the literature. All of them are proved in the formalization, at
the strength that `main` needs; nothing is assumed. This file relates each Lean statement
to the statement in its source: what is dropped, specialized or added, and how it is
proved. The blueprint (`blueprint/blueprint.tex`, Section Background) states the results
in the same form. Paths are relative to `LorentzianCalderon/`.

## Sources

- [BGP] C. Bär, N. Ginoux, F. Pfäffle, *Wave equations on Lorentzian manifolds and
  quantization*, ESI Lectures in Mathematics and Physics, EMS, 2007.
- [BS] A. N. Bernal, M. Sánchez, *Smoothness of time functions and the metric splitting
  of globally hyperbolic spacetimes*, Comm. Math. Phys. 257 (2005), 43–50,
  doi:10.1007/s00220-005-1346-1.
- [Hartman] P. Hartman, *Ordinary differential equations*, Classics in Applied
  Mathematics 38, SIAM, 2002.
- [HM] A. Hounnonkpe, E. Minguzzi, *Globally hyperbolic spacetimes can be defined without
  the 'causal' condition*, Class. Quantum Grav. 36 (2019), 197001,
  doi:10.1088/1361-6382/ab3f11.
- [O'Neill] B. O'Neill, *Semi-Riemannian geometry. With applications to relativity*,
  Pure and Applied Mathematics 103, Academic Press, 1983.
- [Rauch] J. Rauch, *Hyperbolic partial differential equations and geometric optics*,
  Graduate Studies in Mathematics 133, AMS, 2012.

## Principles

- **Fewer conclusions.** A statement keeps only the conclusions the proof of `main` uses.
- **More hypotheses.** A hypothesis that every use can supply is added when it makes the
  proof cheaper (for instance, that a geodesic is causal).
- **The Minkowski exterior.** The metrics of `main` are Minkowskian outside `M₀`.
  `IsSpacetime` records this (field `exterior`, with a sign `σ` such that `σ∂ₜ` is
  future-directed there), so every result is stated for such metrics only. The temporal
  functions and the retarded solutions use it.

## Proved as stated

- `Facts.borel` ([Rauch], Thm 4.3.1): `Facts/Borel.lean`.
- `Facts.gauss` ([O'Neill], Lemma 5.1): `Geometry/Gauss.lean`.
- `Facts.isOpen_chronFuture` ([O'Neill], Lemma 14.3): `Causal/Chron.lean`.
- `Facts.chronLT_of_conjugate` ([O'Neill], Cor 14.5 with Prop 10.10):
  `Geometry/ConjugateChron.lean`, by Jacobi fields from the derivative of `exp` and an
  explicit second-order variation `σ + sV + s²Z` (pointwise, without the index form). It
  does not use global hyperbolicity.
- `Facts.chronLT_of_not_nullPregeodesic` ([O'Neill], Prop 10.46, without the clause that the
  timelike curve can be chosen arbitrarily close): `Geometry/NullPregeodesic.lean`, by a
  local-to-global argument on totally normal neighbourhoods (`Geometry/NormalNbhd.lean`)
  and [O'Neill], Lemma 5.33 (`Geometry/LocalCausality.lean`), instead of O'Neill's
  variations.
- `CausalLE.trans_chronLT` and `ChronLT.trans_causalLE`, push-up ([O'Neill], Cor 14.1):
  `Geometry/PushUp.lean`, from local push-up in totally normal neighbourhoods along a causal
  curve (`Geometry/LocalCausality.lean`).
- `Facts.isClosed_causalLE` ([O'Neill], Lemma 14.22): `Geometry/CausalClosed.lean`, from
  the compactness of causal diamonds. `J⁺(p)` is closed, since a limit of points of
  `J⁺(p)` lies in some open `I⁻(q)` together with the nearby points, which lie in the
  compact diamond `J⁺(p) ∩ J⁻(q)`; then `pₖ ≤ qₖ → (p, q)` gives `a ≤ q` for every
  `a ≪ p`, and `p ≤ q` as such `a` approach `p`.
- `Facts.isCompact_causalFutureSet_inter_causalPastSet` ([BGP], Lemma A.5.7):
  `Geometry/CausalClosed.lean`. `J⁺(K) ∩ J⁻(K')` lies in a finite union of causal
  diamonds (cover `K` by sets `I⁺(p)` and `K'` by sets `I⁻(q)`, which are open), which are
  compact by the definition of global hyperbolicity, and it is closed.

## Specialized

### `Facts.ode_smooth_dependence` ([Hartman], Ch. V, Thms 2.1, 3.1, 4.1)

Hartman treats `x' = F(t, x, p)` with a time-dependent field and parameters `p` in an open
set; the solution with `x(t₀) = x₀` is smooth in `(t, t₀, x₀, p)` on its open domain. The
proof of `main` needs only an autonomous field on an open set `U`, so the Lean statement
is that special case: `F : V → V` smooth on `U`, with a parameter ranging over a whole
normed space and not entering the equation. The proof (`ODE/`) follows Hartman's route:
maximal flows, `C¹` dependence through the variational equation and Grönwall, and
induction on the order of smoothness via the augmented field `(z, A) ↦ (F z, DF(z) A)`.

### `Facts.imprisonment` ([O'Neill], Lemma 14.13)

O'Neill: if strong causality holds on a compact `K`, a future-inextendible causal curve
starting in `K` eventually leaves `K` never to return. The Lean statement concludes only
that the curve does not stay in `K` for all parameters, which is what its uses (geodesic
rays in `Geometry/Imprison.lean`) need. The proof (`Causal/Imprisonment.lean`) uses a
temporal function `ψ` instead of strong causality: on `K`, `dψ(v) ≥ κ|v|` for future
causal `v`, so a curve imprisoned in `K` has finite length and hence a limit.

### `Facts.geodesic_extension` ([O'Neill], Lemma 5.8)

O'Neill: a geodesic on `[0, b)` that extends continuously to `b` extends as a geodesic;
the proof uses a convex neighbourhood of the limit point. The Lean statement adds the
hypothesis that all velocities are future causal, which its only use, the ray
`r ↦ exp_y(r w)` with `w` future causal (`Geometry/Imprison.lean`), satisfies. Then a
cone estimate and the geodesic equation bound the velocity near `b`, and the extension
follows from the ODE alone, without convex neighbourhoods
(`Geometry/GeodesicExtension.lean`).

### `Facts.exists_causal_geodesic` ([O'Neill], Prop 14.19 with Lemma 14.16)

O'Neill: causally related points of a globally hyperbolic spacetime are joined by a
maximizing causal geodesic, timelike if the points are chronologically related. The Lean
statement is for points that are causally but not chronologically related (`p ≤ q`,
`p ≠ q`, not `p ≪ q`), and concludes that the geodesic is null. Such a geodesic comes from
[O'Neill], Prop 10.46 (`Facts.chronLT_of_not_nullPregeodesic`): a causal curve from `p` to `q`
is a null pregeodesic, reparametrized affinely (`Geometry/Horismos.lean`); no limit curves
are needed. Timelike geodesics between chronologically related points near a null
geodesic are handled locally in exponential charts (`Geometry/Crossing.lean`).

### `Facts.exists_retarded` ([BGP], Thm 3.3.1, Cor 3.4.3; with Thms 3.2.11–12)

For a smooth family `F(s)` of test functions supported in a fixed compact `K`, there is a
family `V(s)`, smooth in `(s, x)`, with `□V(s) = F(s)` and `supp V(s) ⊆ J⁺(K)`. In BGP,
`V(s) = G₊(F(s))` with the Green's operator `G₊` of Cor 3.4.3, whose support property is
part of Thm 3.3.1; by uniqueness (Thm 3.2.11), `G₊ F(s)` is the solution of the Cauchy
problem with zero data on a Cauchy hypersurface in the past of `K`, so `G₊` is continuous
from `D_K` to `C^∞` (Thm 3.2.12), and a continuous linear map takes smooth families to
smooth families. A single source is the constant family.

The proof (`Green/Retarded.lean`) works in coordinates adapted to a standard time (zero
shift, flat for large `|y|`): the equation is periodized in space and solved by
Fourier–Galerkin approximation with energy estimates (`PDE/`). The support in `J⁺(K)`
comes from energy estimates on small lenses for slightly narrowed metrics `g + ε dψ²` and
the limit `ε → 0` (`Green/Sweep.lean`).

### `Facts.exists_temporal` and `Facts.exists_cauchyTemporal` ([BS], Thm 1.1)

Bernal–Sánchez: a globally hyperbolic spacetime has a Cauchy temporal function `ψ`, and
splits as `ℝ × Σ` along the flow of `∇ψ/g(dψ, dψ)`. Global hyperbolicity in the sense of
`main`, compactness of the causal diamonds, is equivalent to the traditional one here by
[HM], Thm 2.8; the proof does not use this. `Facts.exists_temporal` states only that a
smooth temporal function exists:

```lean
theorem Facts.exists_temporal (hg : IsSpacetime g Y) :
    ∃ ψ : E n → ℝ, ContDiff ℝ ∞ ψ ∧ ∀ x, IsFutureTimelike g Y x (-grad g ψ x)
```

It is proved (`Facts/Temporal.lean`) without a smoothing theorem. Compact diamonds give
chronology and causality (`Causal/Chronology.lean`, `Causal/Causality.lean`, the latter by
a measure-zero argument that needs `n ≥ 2`). "Fuzzy chains", short steps close to future
causal vectors, have bounded length in compact sets (`Causal/Fuzzy.lean`). The supremum of
`length + 3σ x⁰(start)` over fuzzy chains ending at `p` is a time function that increases
by at least the Euclidean length of every fuzzy step (`Causal/FuzzyTime.lean`, using the
Minkowski exterior for uniform constants); its mollification is smooth with `dψ(v) ≥ |v|`
for future causal `v` (`Causal/Mollify.lean`).

`Facts.exists_cauchyTemporal` (`Causal/TimeFlow.lean`) is the Cauchy temporal function
with its flow, without the surjectivity of `ψ`, and is derived from
`Facts.exists_temporal` using the Minkowski exterior. From any temporal `ψ₀`, smooth maxima
and minima with `σx⁰ + ½⟨x⟩` and `σx⁰ + A` give a temporal `ψ` equal to `σx⁰ + A` outside a
compact set (`Causal/StandardTime.lean`). Such a `ψ` is steep, `κ|v| ≤ dψ(v)` for future
causal `v` (`Causal/Steep.lean`); hence it tends to `∞` along inextendible causal curves,
its level sets are Cauchy, and the flow of `∇ψ/g(dψ, dψ)`, a bounded field, is complete
(`Causal/TimeFlow.lean`, `ODE/Global.lean`).

## Replaced by direct arguments

These results from the literature are not stated in the formalization; the proof of `main`
uses the arguments below instead.

### Linear ODEs ([Hartman], Ch. IV, Lemma 1.1)

Hartman: a linear system `x' = A(t)x + b(t)` with continuous coefficients on an interval
has a solution on the whole interval. The proof needs only the scalar equation
`β' = -aβ + f`, `β(t₀) = 0` on a compact interval (`Waves/Transport.lean`), solved by the
integrating factor (`exists_linear_scalar_ode`, `Waves/Flow.lean`).

### The Cauchy problem ([BGP], Thms 3.2.11–12)

BGP: the Cauchy problem with smooth data on a Cauchy hypersurface has a unique smooth
solution, depending continuously on the data. The proof uses instead:

- uniqueness in the form: `□v = 0` and `supp v ⊆ J⁺(K)` with `K` compact imply `v = 0`
  (`eq_zero_of_support_subset_causalFutureSet`, `Green/Basic.lean`), by duality with the
  advanced solution `G⁻ϑ` of a test function `ϑ`: `∫ v ϑ = ∫ v □G⁻ϑ = ∫ □v G⁻ϑ = 0`, the
  supports meeting in the compact set `J⁺(K) ∩ J⁻(supp ϑ)`;
- retarded solutions for smooth families of sources, `Facts.exists_retarded` above;
- a global solution of `□v = 0` with a prescribed differential at a point,
  `Facts.exists_solution_fderiv_eq` (`Green/Prescribed.lean`), from retarded and advanced
  solutions and `Facts.borel`: a function `w` with `dw(p) = ζ` whose `□w` is flat on the level
  set of a Cauchy temporal function through `p` (Taylor coefficients determined
  recursively, the level set being noncharacteristic), corrected by `G⁺` of the part of
  `□w` above the level set and `G⁻` of the part below.

### Antisymmetry of `≤` ([O'Neill], pp. 407–408)

Used only to show that a causal geodesic segment is not closed (`Geometry/Junction.lean`),
which follows from a temporal function, as it increases strictly along causal curves.

### [BGP], Cor A.5.4 and [O'Neill], Lemma 14.29

Used only to show that `J⁺(B) ∩ {ψ ≤ c}` is compact and small for a small ball `B` around
`q₀` and `c` slightly above `ψ(q₀)` (`Induction/FrontierLens.lean`). This is proved
directly: a point of that set outside a fixed sphere around `q₀` would give, by a crossing
argument on the compact sphere and closedness of `J⁺`, a point `y ≥ q₀` on the sphere with
`ψ(y) ≤ ψ(q₀)`, which is impossible since `ψ` increases strictly along causal curves.
