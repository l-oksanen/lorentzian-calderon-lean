module

public import LorentzianCalderon.Causal.Causality
public import LorentzianCalderon.Causal.Mollify

public section

namespace LorentzianCalderon.Facts

noncomputable section
open scoped ContDiff

variable {n : ℕ} {g : MatrixField n} {Y : E n → E n}

/-- A temporal function exists: a smooth `ψ` with `-grad ψ` future-directed timelike.
Bernal–Sánchez, Comm. Math. Phys. 257 (2005), Theorem 1.1, p. 43, for globally hyperbolic
spacetimes in the traditional sense (Hounnonkpe–Minguzzi, Theorem 2.8). Proved here for metrics
that are Minkowskian outside a box: causality from compact diamonds (`Causal/Causality.lean`),
then a time function from fuzzy chains, mollified (`Causal/FuzzyTime.lean`,
`Causal/Mollify.lean`). That it can be chosen Cauchy, and the splitting `M ≅ ℝ × Σ`, are
derived in `Causal/Steep.lean` and `Causal/TimeFlow.lean`. -/
theorem exists_temporal (hg : IsSpacetime g Y) :
    ∃ ψ : E n → ℝ, ContDiff ℝ ∞ ψ ∧ ∀ x, IsFutureTimelike g Y x (-grad g ψ x) :=
  exists_temporal_of_antisymm hg fun _ _ hpq hqp => causalLE_antisymm hg hpq hqp

end

end LorentzianCalderon.Facts
