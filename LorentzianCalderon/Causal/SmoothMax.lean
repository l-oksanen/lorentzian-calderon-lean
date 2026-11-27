module

public import LorentzianCalderon.Green.Temporal

public section

/-!
# Smooth maxima and the future timelike cone

A smooth ramp `smoothRamp`, equal to `0` on `(-∞, -1]` and to `s` plus a constant on `[1, ∞)`,
with derivative `rampSlope ∈ [0, 1]`, gives a smooth maximum `smax a b = b + ramp (a - b)` and
minimum `smin a b = b - ramp (b - a)` of two functions. Their derivatives are convex
combinations of those of `a` and `b`, and they equal one argument (up to a constant) where it
exceeds (falls below) the other by `1`.

A vector `w` is future-directed timelike if and only if `g(w, v) < 0` for every future-directed
causal `v` (`isFutureTimelike_of_form_neg`); so `-grad ψ` is future timelike when `dψ` is
positive on future causal vectors, and the future timelike cone is convex.
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Set Filter

/-- The slope of `smoothRamp`: a smooth step from `0` on `(-∞, -1]` to `1` on `[1, ∞)`. -/
def rampSlope (s : ℝ) : ℝ := Real.smoothTransition ((s + 1) / 2)

/-- A smooth convex ramp: `0` on `(-∞, -1]`, slope `1` on `[1, ∞)`. -/
def smoothRamp (s : ℝ) : ℝ := ∫ t in (-1 : ℝ)..s, rampSlope t

theorem contDiff_rampSlope : ContDiff ℝ ∞ rampSlope :=
  Real.smoothTransition.contDiff.comp (by fun_prop)

theorem continuous_rampSlope : Continuous rampSlope := contDiff_rampSlope.continuous

theorem rampSlope_nonneg (s : ℝ) : 0 ≤ rampSlope s := Real.smoothTransition.nonneg _

theorem rampSlope_le_one (s : ℝ) : rampSlope s ≤ 1 := Real.smoothTransition.le_one _

theorem rampSlope_of_le {s : ℝ} (hs : s ≤ -1) : rampSlope s = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem rampSlope_of_ge {s : ℝ} (hs : 1 ≤ s) : rampSlope s = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem hasDerivAt_smoothRamp (s : ℝ) : HasDerivAt smoothRamp (rampSlope s) s :=
  (continuous_rampSlope.integral_hasStrictDerivAt (-1) s).hasDerivAt

theorem contDiff_smoothRamp : ContDiff ℝ ∞ smoothRamp := by
  have hd : deriv smoothRamp = rampSlope := funext fun s => (hasDerivAt_smoothRamp s).deriv
  exact contDiff_infty_iff_deriv.2 ⟨fun s => (hasDerivAt_smoothRamp s).differentiableAt,
    hd ▸ contDiff_rampSlope⟩

theorem smoothRamp_of_le {s : ℝ} (hs : s ≤ -1) : smoothRamp s = 0 := by
  rw [smoothRamp, intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)),
    intervalIntegral.integral_zero]
  intro t ht
  rw [uIcc_of_ge hs] at ht
  exact rampSlope_of_le ht.2

theorem smoothRamp_nonneg (s : ℝ) : 0 ≤ smoothRamp s := by
  rcases le_total s (-1) with hs | hs
  · rw [smoothRamp_of_le hs]
  · exact intervalIntegral.integral_nonneg hs fun t _ => rampSlope_nonneg t

theorem smoothRamp_of_ge {s : ℝ} (hs : 1 ≤ s) : smoothRamp s = s + (smoothRamp 1 - 1) := by
  have hi : ∀ a b : ℝ, IntervalIntegrable rampSlope MeasureTheory.volume a b :=
    fun a b => continuous_rampSlope.intervalIntegrable a b
  have h := intervalIntegral.integral_add_adjacent_intervals (hi (-1) 1) (hi 1 s)
  have h1 : ∫ t in (1 : ℝ)..s, rampSlope t = s - 1 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ))]
    · simp
    · intro t ht
      rw [uIcc_of_le hs] at ht
      exact rampSlope_of_ge ht.1
  simp only [smoothRamp] at h ⊢
  rw [← h, h1]
  ring

section Max

variable {V : Type*}

/-- The smooth maximum `b + ramp (a - b)`: equal to `b` where `a ≤ b - 1`, and to `a` plus a
constant where `a ≥ b + 1`. -/
def smax (a b : V → ℝ) (x : V) : ℝ := b x + smoothRamp (a x - b x)

/-- The smooth minimum `b - ramp (b - a)`: equal to `b` where `b ≤ a - 1`, and to `a` minus a
constant where `b ≥ a + 1`. -/
def smin (a b : V → ℝ) (x : V) : ℝ := b x - smoothRamp (b x - a x)

variable {a b : V → ℝ} {x : V}

section Calculus

variable [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem contDiff_smax (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) : ContDiff ℝ ∞ (smax a b) :=
  hb.add (contDiff_smoothRamp.comp (ha.sub hb))

theorem contDiff_smin (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) : ContDiff ℝ ∞ (smin a b) :=
  hb.sub (contDiff_smoothRamp.comp (hb.sub ha))

theorem hasFDerivAt_smax {a' b' : V →L[ℝ] ℝ} (ha : HasFDerivAt a a' x) (hb : HasFDerivAt b b' x) :
    HasFDerivAt (smax a b) (rampSlope (a x - b x) • a' + (1 - rampSlope (a x - b x)) • b') x := by
  have h : HasFDerivAt (fun y => b y + smoothRamp (a y - b y)) _ x :=
    hb.add ((hasDerivAt_smoothRamp (a x - b x)).comp_hasFDerivAt (f := fun y => a y - b y) x
      (ha.sub hb))
  exact h.congr_fderiv (by ext v; simp; ring)

theorem hasFDerivAt_smin {a' b' : V →L[ℝ] ℝ} (ha : HasFDerivAt a a' x) (hb : HasFDerivAt b b' x) :
    HasFDerivAt (smin a b) (rampSlope (b x - a x) • a' + (1 - rampSlope (b x - a x)) • b') x := by
  have h : HasFDerivAt (fun y => b y - smoothRamp (b y - a y)) _ x :=
    hb.sub ((hasDerivAt_smoothRamp (b x - a x)).comp_hasFDerivAt (f := fun y => b y - a y) x
      (hb.sub ha))
  exact h.congr_fderiv (by ext v; simp; ring)

end Calculus

theorem le_smax_right (x : V) : b x ≤ smax a b x :=
  le_add_of_nonneg_right (smoothRamp_nonneg _)

theorem smax_eq_left (h : b x + 1 ≤ a x) : smax a b x = a x + (smoothRamp 1 - 1) := by
  rw [smax, smoothRamp_of_ge (by linarith)]
  ring

theorem smin_eq_right (h : b x + 1 ≤ a x) : smin a b x = b x := by
  rw [smin, smoothRamp_of_le (by linarith), sub_zero]

theorem smin_eq_left (h : a x + 1 ≤ b x) : smin a b x = a x - (smoothRamp 1 - 1) := by
  rw [smin, smoothRamp_of_ge (by linarith)]
  ring

/-- A convex combination of two positive numbers is positive. -/
theorem convex_comb_pos {θ p q : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hp : 0 < p) (hq : 0 < q) :
    0 < θ * p + (1 - θ) * q := by
  rcases h0.lt_or_eq with h0 | rfl
  · nlinarith
  · simpa using hq

end Max

/-! ### The future timelike cone -/

variable {n : ℕ} {g : MatrixField n} {Y : E n → E n} {x w : E n}

/-- A vector with negative product with every future-directed causal vector is future-directed
timelike. -/
theorem isFutureTimelike_of_form_neg (hL : IsLorentzian (g x)) (hY : form (g x) (Y x) (Y x) < 0)
    (h : ∀ v, IsFutureCausal g Y x v → form (g x) w v < 0) : IsFutureTimelike g Y x w := by
  have hY0 : Y x ≠ 0 := fun h0 => by simp [h0] at hY
  have hfut := h _ ⟨hY0, hY.le, hY⟩
  refine ⟨?_, hfut⟩
  by_contra hc
  push Not at hc
  have hsymm : form (g x) (Y x) w = form (g x) w (Y x) := form_comm hL.symm _ _
  rcases hc.eq_or_lt with hc | hc
  · have hw0 : w ≠ 0 := fun h0 => by simp [h0] at hfut
    exact (h w ⟨hw0, hc.symm.le, hfut⟩).ne hc.symm
  · set s := -form (g x) w (Y x) / form (g x) w w
    have hs : 0 < s := div_pos (by linarith) hc
    have hss : s * form (g x) w w = -form (g x) w (Y x) := by
      simp only [s]; field_simp
    set v := Y x + s • w
    have hvY : form (g x) v (Y x) < 0 := by
      simp only [v, form_add_left, form_smul_left]
      nlinarith
    have hvv : form (g x) v v < 0 := by
      have : form (g x) v v =
          form (g x) v (Y x) + s * (form (g x) w (Y x) + s * form (g x) w w) := by
        simp only [v, form_add_left, form_add_right, form_smul_left, form_smul_right, hsymm]
      rw [this, hss]
      linarith
    have hwv : form (g x) w v = 0 := by
      simp only [v, form_add_right, form_smul_right]
      linarith
    have hv0 : v ≠ 0 := fun h0 => by simp [h0] at hvY
    exact (h v ⟨hv0, hvv.le, hvY⟩).ne hwv

/-- `-grad ψ` is future-directed timelike when `dψ` is positive on future-directed causal
vectors; the converse of `fderiv_pos_of_isFutureCausal`. -/
theorem isFutureTimelike_neg_grad_of_fderiv_pos {ψ : E n → ℝ} (hL : IsLorentzian (g x))
    (hY : form (g x) (Y x) (Y x) < 0) (h : ∀ v, IsFutureCausal g Y x v → 0 < fderiv ℝ ψ x v) :
    IsFutureTimelike g Y x (-grad g ψ x) :=
  isFutureTimelike_of_form_neg hL hY fun v hv => by
    rw [form_neg_left, ← fderiv_eq_form_grad hL]
    linarith [h v hv]

/-- The future timelike cone is convex. -/
theorem IsFutureTimelike.convex_comb {w₁ w₂ : E n} (hL : IsLorentzian (g x))
    (hY : form (g x) (Y x) (Y x) < 0) (h₁ : IsFutureTimelike g Y x w₁)
    (h₂ : IsFutureTimelike g Y x w₂) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    IsFutureTimelike g Y x (θ • w₁ + (1 - θ) • w₂) :=
  isFutureTimelike_of_form_neg hL hY fun v hv => by
    have := convex_comb_pos h0 h1 (neg_pos.2 (h₁.form_neg hL hY hv))
      (neg_pos.2 (h₂.form_neg hL hY hv))
    rw [form_add_left, form_smul_left, form_smul_left]
    linarith

end

end LorentzianCalderon
