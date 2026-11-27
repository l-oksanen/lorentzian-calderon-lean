module

public import LorentzianCalderon.Causal.SmoothMax
public import LorentzianCalderon.Setting.BoxGreen
public import LorentzianCalderon.Facts.Temporal
public import LorentzianCalderon.Setting.Escape

public section

/-!
# Standard time functions

A standard time function is a temporal function equal to `σ x⁰ + A` outside a compact set
(`IsStandardTime`). Every spacetime has one (`exists_standardTime`), built from any temporal
function `ψ₀` (`Facts.exists_temporal`) and the Minkowski exterior: with
`h = σ x⁰ + ½⟨x⟩ - D`, where `⟨x⟩ = (1 + ‖x‖²)^{1/2}` and `D` is so large that `ψ₀ ≥ h + 1` on
the box, `ψ₁ = smax ψ₀ h` is temporal and grows like `½⟨x⟩` relative to `σ x⁰`; then
`ψ = smin ψ₁ (σ x⁰ + A)`, for `A` so large that `ψ₁ ≤ σ x⁰ + A - 1` on the box, is temporal and
equals `σ x⁰ + A` where `½⟨x⟩ ≥ A + D + 1`.
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff RealInnerProductSpace
open Set Filter Metric

variable {n : ℕ}

/-- A standard time function: a smooth temporal function equal to `σ x⁰ + A` outside a compact
set, for a sign `σ`. -/
structure IsStandardTime (g : MatrixField n) (Y : E n → E n) (ψ : E n → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ ψ
  past_gradient : ∀ x, IsFutureTimelike g Y x (-grad g ψ x)
  exterior : ∃ (C : Set (E n)) (σ A : ℝ), IsCompact C ∧ (σ = 1 ∨ σ = -1) ∧
    ∀ x ∉ C, ψ x = σ * x 0 + A

variable {g : MatrixField n} {Y : E n → E n}

/-- Outside the box, a future-directed causal vector `v` has `σ v⁰ > 0` and lies in the cone
`‖v‖² ≤ 2 (v⁰)²`. -/
theorem isFutureCausal_exterior {x : E n} (hL : IsLorentzian (g x))
    (hY : form (g x) (Y x) (Y x) < 0) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hx : g x = minkowski n ∧ form (g x) (σ • EuclideanSpace.single 0 1) (Y x) < 0) {v : E n}
    (hv : IsFutureCausal g Y x v) : 0 < σ * v 0 ∧ ‖v‖ ^ 2 ≤ 2 * v 0 ^ 2 := by
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hu : IsFutureTimelike g Y x (σ • EuclideanSpace.single 0 1) := by
    refine ⟨?_, hx.2⟩
    rw [form_smul_left, form_smul_right, hx.1, form_minkowski_single_zero]
    simp [hσ2]
  have h1 := hu.form_neg hL hY hv
  have h2 := hv.causal
  rw [form_smul_left, hx.1, form_minkowski_single_zero] at h1
  rw [hx.1, form_minkowski_self] at h2
  rw [norm_sq_eq_time_sq_add]
  constructor <;> linarith

/-- `⟨x⟩ = (1 + ‖x‖²)^{1/2}`. -/
def japaneseBracket (x : E n) : ℝ := √(1 + ‖x‖ ^ 2)

theorem contDiff_japaneseBracket : ContDiff ℝ ∞ (japaneseBracket (n := n)) :=
  (contDiff_const.add (contDiff_norm_sq ℝ)).sqrt fun x => by positivity

theorem norm_le_japaneseBracket (x : E n) : ‖x‖ ≤ japaneseBracket x :=
  Real.le_sqrt_of_sq_le (by linarith)

theorem abs_fderiv_japaneseBracket_le (x v : E n) : |fderiv ℝ japaneseBracket x v| ≤ ‖v‖ := by
  have hpos : 0 < japaneseBracket x := Real.sqrt_pos.2 (by positivity)
  have hd : HasFDerivAt (japaneseBracket (n := n))
      ((1 / (2 * japaneseBracket x)) • (2 • innerSL ℝ x)) x :=
    ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_add 1).sqrt (by positivity)
  rw [hd.fderiv]
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
  change |1 / (2 * japaneseBracket x) * (2 * ⟪x, v⟫)| ≤ ‖v‖
  rw [show 1 / (2 * japaneseBracket x) * (2 * ⟪x, v⟫) = ⟪x, v⟫ / japaneseBracket x by
    field_simp, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  calc |⟪x, v⟫| ≤ ‖x‖ * ‖v‖ := abs_real_inner_le_norm x v
    _ ≤ ‖v‖ * japaneseBracket x := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_left (norm_le_japaneseBracket x) (norm_nonneg v)

theorem hasFDerivAt_coord (x : E n) :
    HasFDerivAt (fun y : E n => y 0) (EuclideanSpace.proj (0 : Fin (n + 1)) : E n →L[ℝ] ℝ) x :=
  (EuclideanSpace.proj (0 : Fin (n + 1)) : E n →L[ℝ] ℝ).hasFDerivAt

theorem contDiff_coord : ContDiff ℝ ∞ fun y : E n => y 0 :=
  (EuclideanSpace.proj (0 : Fin (n + 1)) : E n →L[ℝ] ℝ).contDiff

/-- A standard time function exists. -/
theorem exists_standardTime (hg : IsSpacetime g Y) : ∃ ψ, IsStandardTime g Y ψ := by
  obtain ⟨ψ₀, hψ₀s, hψ₀⟩ := Facts.exists_temporal hg
  obtain ⟨T, σ, hσ, hext⟩ := hg.exterior
  have hY := hg.globallyHyperbolic.timeOrientation
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hM := isCompact_M0 (n := n) T
  set φ : E n → ℝ := japaneseBracket
  have hφs : ContDiff ℝ ∞ φ := contDiff_japaneseBracket
  have hlin : ∀ c : ℝ, ContDiff ℝ ∞ fun y : E n => σ * y 0 + c :=
    fun c => (contDiff_const.mul contDiff_coord).add contDiff_const
  have hlinv : ∀ (c : ℝ) (x v : E n), fderiv ℝ (fun y : E n => σ * y 0 + c) x v = σ * v 0 := by
    intro c x v
    rw [(((hasFDerivAt_coord x).const_mul σ).add_const c).fderiv]
    simp
  have hc0 : Continuous fun y : E n => y 0 := contDiff_coord.continuous
  have hφc := hφs.continuous
  have hψ₀c := hψ₀s.continuous
  obtain ⟨D, hD⟩ := hM.bddAbove_image (f := fun x => σ * x 0 + 2⁻¹ * φ x - ψ₀ x + 1)
    (Continuous.continuousOn (by fun_prop))
  set b : E n → ℝ := fun x => σ * x 0 + 2⁻¹ * φ x - D
  have hcd0 : ContDiff ℝ ∞ fun y : E n => y 0 := contDiff_coord
  have hbs : ContDiff ℝ ∞ b := by simp only [b]; fun_prop
  have hbM : ∀ x ∈ M0 n T, b x + 1 ≤ ψ₀ x := fun x hx => by
    have := hD ⟨x, hx, rfl⟩
    simp only [b]
    linarith
  set ψ₁ := smax ψ₀ b
  have hψ₁s : ContDiff ℝ ∞ ψ₁ := contDiff_smax hψ₀s hbs
  have hψ₁c := hψ₁s.continuous
  obtain ⟨A, hA⟩ := hM.bddAbove_image (f := fun x => ψ₁ x - σ * x 0 + 1)
    (Continuous.continuousOn (by fun_prop))
  set ℓ : E n → ℝ := fun y => σ * y 0 + A
  have hℓM : ∀ x ∈ M0 n T, ψ₁ x + 1 ≤ ℓ x := fun x hx => by
    have := hA ⟨x, hx, rfl⟩
    simp only [ℓ]
    linarith
  set ψ := smin ψ₁ ℓ
  have hd : ∀ {f : E n → ℝ}, ContDiff ℝ ∞ f → ∀ x, HasFDerivAt f (fderiv ℝ f x) x :=
    fun hf x => (hf.differentiable (by simp) x).hasFDerivAt
  have hpos₀ : ∀ x v, IsFutureCausal g Y x v → 0 < fderiv ℝ ψ₀ x v := fun x v hv =>
    fderiv_pos_of_isFutureCausal (hg.lorentzian x) (hY.timelike x) (hψ₀ x) hv
  have hposb : ∀ x ∉ M0 n T, ∀ v, IsFutureCausal g Y x v → 0 < fderiv ℝ b x v := by
    intro x hx v hv
    obtain ⟨h1, h2⟩ := isFutureCausal_exterior (hg.lorentzian x) (hY.timelike x) hσ
      (hext x hx) hv
    have hb : fderiv ℝ b x v = σ * v 0 + 2⁻¹ * fderiv ℝ φ x v := by
      have hbd : HasFDerivAt b ((σ • (EuclideanSpace.proj 0 : E n →L[ℝ] ℝ)) +
          (2⁻¹ : ℝ) • fderiv ℝ φ x) x :=
        (((hasFDerivAt_coord x).const_mul σ).add ((hd hφs x).const_mul 2⁻¹)).sub_const D
      rw [hbd.fderiv]
      simp
    have hφv := abs_le.1 (abs_fderiv_japaneseBracket_le x v)
    have hsq : (‖v‖ / 2) ^ 2 < (σ * v 0) ^ 2 := by
      have : (σ * v 0) ^ 2 = v 0 ^ 2 := by rw [mul_pow, sq σ, hσ2, one_mul]
      nlinarith
    have := lt_of_pow_lt_pow_left₀ 2 h1.le hsq
    rw [hb]
    linarith
  have hposℓ : ∀ x ∉ M0 n T, ∀ v, IsFutureCausal g Y x v → 0 < fderiv ℝ ℓ x v := by
    intro x hx v hv
    rw [hlinv]
    exact (isFutureCausal_exterior (hg.lorentzian x) (hY.timelike x) hσ (hext x hx) hv).1
  have hpos₁ : ∀ x v, IsFutureCausal g Y x v → 0 < fderiv ℝ ψ₁ x v := by
    intro x v hv
    rw [(hasFDerivAt_smax (hd hψ₀s x) (hd hbs x)).fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul]
    by_cases hx : x ∈ M0 n T
    · rw [rampSlope_of_ge (by linarith [hbM x hx])]
      simpa using hpos₀ x v hv
    · exact convex_comb_pos (rampSlope_nonneg _) (rampSlope_le_one _) (hpos₀ x v hv)
        (hposb x hx v hv)
  have hpos : ∀ x v, IsFutureCausal g Y x v → 0 < fderiv ℝ ψ x v := by
    intro x v hv
    rw [(hasFDerivAt_smin (hd hψ₁s x) (hd (hlin A) x)).fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul]
    by_cases hx : x ∈ M0 n T
    · rw [rampSlope_of_ge (by linarith [hℓM x hx])]
      simpa using hpos₁ x v hv
    · exact convex_comb_pos (rampSlope_nonneg _) (rampSlope_le_one _) (hpos₁ x v hv)
        (hposℓ x hx v hv)
  refine ⟨ψ, contDiff_smin hψ₁s (hlin A), fun x =>
    isFutureTimelike_neg_grad_of_fderiv_pos (hg.lorentzian x) (hY.timelike x) (hpos x),
    closedBall 0 (2 * (A + D + 1)), σ, A, isCompact_closedBall _ _, hσ, fun x hx => ?_⟩
  have hx' : 2 * (A + D + 1) < ‖x‖ := by simpa using hx
  have h1 : b x ≤ ψ₁ x := le_smax_right x
  have h2 : ‖x‖ ≤ φ x := norm_le_japaneseBracket x
  exact smin_eq_right (show ℓ x + 1 ≤ ψ₁ x by simp only [ℓ, b] at h1 ⊢; linarith)

end

end LorentzianCalderon
