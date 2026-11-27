module

public import LorentzianCalderon.Causal.FuzzyTime
public import LorentzianCalderon.Causal.SmoothMax

public section

/-!
# A temporal function by mollifying the fuzzy time

Let `u` increase by at least `‖z' - z‖` along every fuzzy step `z → z'` of size `ε`, as the fuzzy
time function does. Mollify it, `ψ = ρ ⋆ u` with `ρ ≥ 0` smooth, `∫ ρ = 1`, supported in the ball
of radius `ε / 2`. For `v` future causal at `x` and small
`s > 0`, each translate `z = x - y`, `y ∈ supp ρ`, makes `z → z + s v` a fuzzy step (witness
`x`, vector `s v`), so `ψ(x + s v) - ψ(x) ≥ s ‖v‖` and `dψ_x(v) ≥ ‖v‖ > 0`
(`exists_smooth_steep`). Hence `-grad ψ` is future timelike (`exists_temporal_of_antisymm`).
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Set Filter Metric MeasureTheory

variable {n : ℕ} {g : MatrixField n} {Y : E n → E n}

/-- A locally bounded function that increases by `‖z' - z‖` along fuzzy steps of size `ε` has a
smooth mollification `ψ` with `dψ_x(v) ≥ ‖v‖` for all future causal `v` at `x`. -/
theorem exists_smooth_steep {u : E n → ℝ} {ε C : ℝ} (hε : 0 < ε) (hu : LowerSemicontinuous u)
    (hbd : ∀ p, |u p| ≤ 3 * ‖p‖ + C)
    (hsteep : ∀ z z', IsFuzzyStep g Y ε z z' → u z + ‖z' - z‖ ≤ u z') :
    ∃ ψ : E n → ℝ, ContDiff ℝ ∞ ψ ∧
      ∀ x v, IsFutureCausal g Y x v → ‖v‖ ≤ fderiv ℝ ψ x v := by
  let φ : ContDiffBump (0 : E n) := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  set ρ := φ.normed volume
  have hloc : LocallyIntegrable u volume := by
    have hc : Continuous fun p : E n => 3 * ‖p‖ + C := by fun_prop
    refine hc.locallyIntegrable.mono hu.measurable.aestronglyMeasurable
      (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact (hbd p).trans (le_abs_self _)
  set L := ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)
  set ψ := convolution ρ u L volume
  have hψ : ContDiff ℝ ∞ ψ := contDiff_infty.2 fun k =>
    (φ.hasCompactSupport_normed (μ := volume)).contDiff_convolution_left L (n := (k : ℕ∞)) (φ.contDiff_normed (μ := volume)) hloc
  have hex := (φ.hasCompactSupport_normed (μ := volume)).convolutionExists_left L (φ.continuous_normed (μ := volume)) hloc
  have hψx : ∀ y, ψ y = ∫ t, ρ t * u (y - t) := fun y => by
    simp [ψ, convolution_def, L]
  have hint : ∀ y, Integrable (fun t => ρ t * u (y - t)) volume := fun y => by
    have h := hex y
    rw [ConvolutionExistsAt] at h
    simpa [L, ρ] using h
  have hmono : ∀ x v, IsFutureCausal g Y x v → ∀ s : ℝ, 0 < s → s * ‖v‖ < ε →
      ψ x + s * ‖v‖ ≤ ψ (x + s • v) := by
    intro x v hv s hs hsv
    have hv0 : 0 < ‖v‖ := norm_pos_iff.2 hv.ne_zero
    have hpt : ∀ t, ρ t * u (x - t) + ρ t * (s * ‖v‖) ≤ ρ t * u (x + s • v - t) := by
      intro t
      by_cases ht : ρ t = 0
      · simp [ht]
      have htb : t ∈ ball (0 : E n) (ε / 2) := by
        have : t ∈ Function.support ρ := ht
        rwa [φ.support_normed_eq] at this
      rw [mem_ball_zero_iff] at htb
      have hstep : IsFuzzyStep g Y ε (x - t) (x + s • v - t) := by
        have hΔ : x + s • v - t - (x - t) = s • v := by abel
        have hnorm : ‖s • v‖ = s * ‖v‖ := by rw [norm_smul, Real.norm_of_nonneg hs.le]
        refine ⟨by rwa [hΔ, hnorm], x, s • v, ?_, hv.smul hs, ?_⟩
        · rw [dist_eq_norm, sub_sub_cancel]
          linarith
        · rw [hΔ, sub_self, norm_zero, hnorm]
          positivity
      have := hsteep _ _ hstep
      rw [show x + s • v - t - (x - t) = s • v by abel, norm_smul,
        Real.norm_of_nonneg hs.le] at this
      have hρ : 0 ≤ ρ t := φ.nonneg_normed t
      nlinarith
    have hρint : Integrable ρ volume := φ.integrable_normed
    have h1 : ∫ t, (ρ t * u (x - t) + ρ t * (s * ‖v‖)) ≤ ∫ t, ρ t * u (x + s • v - t) :=
      integral_mono ((hint x).add (hρint.mul_const (s * ‖v‖))) (hint (x + s • v)) hpt
    rw [integral_add (hint x) (hρint.mul_const (s * ‖v‖)), integral_mul_const,
      φ.integral_normed, one_mul] at h1
    rw [hψx, hψx]
    exact h1
  refine ⟨ψ, hψ, fun x v hv => ?_⟩
  have hv0 : 0 < ‖v‖ := norm_pos_iff.2 hv.ne_zero
  have hdiff : DifferentiableAt ℝ ψ x := hψ.differentiable (by simp) x
  have hline : HasDerivAt (fun s : ℝ => x + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hx0 : x + (0 : ℝ) • v = x := by simp
  have hfd : HasFDerivAt ψ (fderiv ℝ ψ x) (x + (0 : ℝ) • v) := by
    rw [hx0]
    exact hdiff.hasFDerivAt
  have hd := hfd.comp_hasDerivAt (0 : ℝ) hline
  have hslope := (hasDerivAt_iff_tendsto_slope.1 hd).mono_left
    (nhdsWithin_mono (0 : ℝ) (show Ioi (0 : ℝ) ⊆ {0}ᶜ from fun s hs => ne_of_gt hs))
  refine ge_of_tendsto hslope ?_
  have hpos : 0 < ε / ‖v‖ := by positivity
  filter_upwards [Ioo_mem_nhdsGT hpos] with s hs
  have hsv : s * ‖v‖ < ε := by
    have := hs.2
    rwa [lt_div_iff₀ hv0] at this
  have := hmono x v hv s hs.1 hsv
  rw [slope_def_field]
  simp only [Function.comp_apply, hx0, sub_zero]
  rw [le_div_iff₀ hs.1]
  linarith

/-- A causal spacetime (`≤` antisymmetric) has a temporal function: the mollified fuzzy time. -/
theorem exists_temporal_of_antisymm (hg : IsSpacetime g Y)
    (hanti : ∀ p q, CausalLE g Y p q → CausalLE g Y q p → p = q) :
    ∃ ψ : E n → ℝ, ContDiff ℝ ∞ ψ ∧ ∀ x, IsFutureTimelike g Y x (-grad g ψ x) := by
  obtain ⟨σ, hσ, ε, hε, C, hB⟩ := exists_fuzzy_value_bound hg hanti
  have hbd : ∀ p, |fuzzyTime g Y σ ε p| ≤ 3 * ‖p‖ + |C| := fun p => by
    obtain ⟨h1, h2⟩ := fuzzyTime_bounds hB p
    have h3 := abs_mul_apply_zero_le hσ p
    rw [abs_le] at h3 ⊢
    constructor <;> linarith [le_abs_self C, neg_abs_le C]
  obtain ⟨ψ, hψ, hd⟩ := exists_smooth_steep hε (lowerSemicontinuous_fuzzyTime hB) hbd
    fun z z' h => fuzzyTime_add_le hB h
  exact ⟨ψ, hψ, fun x => isFutureTimelike_neg_grad_of_fderiv_pos (hg.lorentzian x)
    (hg.globallyHyperbolic.timeOrientation.timelike x) fun v hv =>
      (norm_pos_iff.2 hv.ne_zero).trans_le (hd x v hv)⟩

end

end LorentzianCalderon
