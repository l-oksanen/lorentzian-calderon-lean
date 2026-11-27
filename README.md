# Uniqueness for the Lorentzian Calderón problem with Minkowski exterior

A Lean 4 formalization, on top of Mathlib, of uniqueness for the Lorentzian Calderón
problem on a box: for `n ≥ 2` and `M₀ = [-T, T] × [-1, 1]ⁿ ⊆ ℝ^{1+n}`, two globally
hyperbolic Lorentzian metrics on `ℝ^{1+n}` that are Minkowskian outside `M₀` and have
the same Cauchy data set for the wave equation on `∂M₀` agree up to a diffeomorphism
that is the identity outside `M₀`. This is a special case of Corollary 1.4 of
M. Lassas, L. Oksanen and M. Salo, *The Lorentzian Calderón problem*.

The theorem, `LorentzianCalderon.main`, is proved without `sorry`, using only the axioms
`propext`, `Quot.sound` and `Classical.choice`. Every result from the literature that the
proof uses is proved in the formalization as well; `docs/weakening.md` relates each of
them to its source.

## Repository map

- `Challenge.lean` states the result with its definitions. It imports only Mathlib,
  and is what a reader audits.
- `Solution.lean` imports the proof, `LorentzianCalderon/Main.lean`.
- `comparator.json` tells `lake comparator` to check that `Solution` proves the
  statement of `Challenge` with the axioms above only.
- `LorentzianCalderon/` is the proof development. `Defs.lean` repeats the
  definitions of the challenge; Comparator checks that the statement of `main`
  and the definitions it uses agree with those of the challenge.
  `Facts/Vocabulary.lean` holds the definitions used to state the results from the
  literature (spacetimes, piecewise smooth paths, the chronological relation,
  inextendible curves, Cauchy hypersurfaces and temporal functions, geodesics, the
  exponential map, conjugate points, null pregeodesics); they are internal to the proof.
- `blueprint/blueprint.tex` is the informal proof, each item naming its Lean
  declarations. Its Background section states the results from the literature in the
  form proved here.
- `formalization.yaml` records provenance, sources, automation and review.
- `docs/weakening.md` relates each result from the literature, as proved, to its source.

## Checking

```sh
lake exe cache get
lake comparator --paranoid
```

`lake comparator` reads `comparator.json`, builds `Challenge` and `Solution`, and checks
that `LorentzianCalderon.main` in `Solution` is accepted by Lean's kernel, has the statement
of `Challenge` with the same definitions, and depends only on the permitted axioms.
`--paranoid` also runs the independent checkers bundled with Lean, among them NanoDa and
con-ron; on 32 cores this takes about half an hour once Mathlib is fetched. The check runs in a `bwrap` sandbox; where that cannot run, add
`--inadvisably-no-sandbox`.

## Time orientation

The blueprint and the formalization state the results from the literature for the future
time orientation only. Past versions follow by reversing the time orientation `Y ↦ -Y`
(`LorentzianCalderon/Causal/Basic.lean`), which exchanges causal futures and pasts; for
instance the advanced solution is the retarded one for `-Y`.
