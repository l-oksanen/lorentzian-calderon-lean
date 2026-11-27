module

public import LorentzianCalderon.Induction.StepCLocal
public import LorentzianCalderon.Induction.StepCPatch

public section

/-!
# The induction, Step C

Blueprint, Lemma `lem_induction`, Step C (extension): if `P(τ)` holds, then `P(τ - δ)` holds for
some `δ > 0`. The proof runs through the local extension `lem_ind_local_extension`, with its
steps C1 (admissible null directions at the cluster point `p₀` of `lem_frontier`, `lem_reach`,
`lem_open_directions`, `lem_span`), C2 (the local gauge `Ψ_{q₀} = (Φ'_I)⁻¹ ∘ Φ_I` built from the
emission-time functions of `lem_emission`, the one-sided waves of `lem_onesided` and the
`g`-waves of `lem_g_waves`), C3 (the local continuation step `prop_local_step`) and C4
(`Ψ_{q₀} = id` outside `W`, by `lem_propagation`), and the patching `lem_ind_patching` over a
finite cover of `Σ_τ ∩ W` by rigidity (`lem_rigidity`).

The hypotheses are the standing assumptions after the orientation reduction (blueprint,
`def_setting`): admissible metrics `g`, `g'` with time orientations `Y`, `Y'` making them
spacetimes (`IsSpacetime` includes `2 ≤ n`), with `∂ₜ` future-directed outside `M₀` for both,
the inclusion of Cauchy data sets, and a Cauchy temporal function `ψ` of `g` with its flow `Φ`
as given by `Facts.exists_cauchyTemporal`.
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology

variable {n : ℕ} {T : ℝ} {g g' : MatrixField n} {Y Y' : E n → E n} {ψ : E n → ℝ}
  {Φ : ℝ → E n → E n} {τ : ℝ} {Ψ : E n → E n}

/-- **Step C** of `lem_induction`: the extension property `P(τ)` propagates to `P(τ - δ)` for some
`δ > 0`. -/
theorem ExtensionProperty.exists_extend_below (hP : ExtensionProperty g g' ψ (W n T) τ Ψ)
    (hgA : IsAdmissibleMetric n T g) (hg'A : IsAdmissibleMetric n T g')
    (hg : IsSpacetime g Y) (hg' : IsSpacetime g' Y')
    (hY : ∀ x ∉ M0 n T, form (g x) (EuclideanSpace.single 0 1) (Y x) < 0)
    (hY' : ∀ x ∉ M0 n T, form (g' x) (EuclideanSpace.single 0 1) (Y' x) < 0)
    (hC : CauchyDataSubset n T g g') (hψ : IsCauchyTemporal g Y ψ)
    (hΦ : ContDiff ℝ ∞ fun p : ℝ × E n => Φ p.1 p.2) (hΦ0 : ∀ x, Φ 0 x = x)
    (hΦψ : ∀ t x, ψ (Φ t x) = ψ x + t) :
    ∃ δ > 0, ∃ Ψ' : E n → E n, ExtensionProperty g g' ψ (W n T) (τ - δ) Ψ' :=
  hP.exists_extend_below_of_local hg hg' hψ.smooth.continuous hΦ.continuous hΦ0 hΦψ hgA hg'A
    fun _ hq₀W hq₀ => hP.exists_local_extension hgA hg'A hg hg' hY hY' hC hψ hΦ.continuous hΦ0
      hΦψ hq₀W hq₀

end

end LorentzianCalderon
