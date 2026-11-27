module

public import LorentzianCalderon.Local.Energy.Cutoff

public section

/-!
# The mollifier `H'_ε(a - s)` in the parameter `s`

`moll ε a s = H'((a - s) / ε) / ε` is a nonnegative bump of integral one supported in
`[a - ε, a]`; integrated against a continuous function of `s ∈ [s₁, s₂]` it converges, as
`ε → 0`, to the value at `a` when `s₁ < a ≤ s₂`, and to `0` otherwise.
-/

namespace LorentzianCalderon

noncomputable section
open Set MeasureTheory Filter Topology intervalIntegral

/-- The mollifier `H'_ε(a - s) = H'((a - s) / ε) / ε`. -/
def moll (ε a s : ℝ) : ℝ := cutoffDeriv ((a - s) / ε) * (1 / ε)

theorem moll_def (ε a s : ℝ) :
    moll ε a s =
      cutoffDeriv ((a - s) / ε) * (1 / ε) := by rfl

theorem continuous_moll (ε a : ℝ) : Continuous (moll ε a) := by
  unfold moll
  exact (continuous_cutoffDeriv.comp ((continuous_const.sub continuous_id).div_const _)).mul
    continuous_const

theorem moll_nonneg {ε : ℝ} (hε : 0 < ε) (a s : ℝ) : 0 ≤ moll ε a s :=
  mul_nonneg (cutoffDeriv_nonneg _) (by positivity)

theorem moll_eq_zero_of_le {ε a s : ℝ} (hε : 0 < ε) (hs : a ≤ s) : moll ε a s = 0 := by
  rw [moll, cutoffDeriv_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le),
    zero_mul]

theorem moll_eq_zero_of_le' {ε a s : ℝ} (hε : 0 < ε) (hs : s ≤ a - ε) : moll ε a s = 0 := by
  rw [moll, cutoffDeriv_of_one_le ((one_le_div hε).2 (by linarith)), zero_mul]

theorem hasDerivAt_neg_cutoff (ε a s : ℝ) :
    HasDerivAt (fun s => -cutoff ((a - s) / ε)) (moll ε a s) s := by
  have := ((hasDerivAt_cutoff ((a - s) / ε)).comp s
    (((hasDerivAt_id s).const_sub a).div_const ε)).neg
  refine this.congr_deriv ?_
  simp only [moll]
  ring

theorem integral_moll (ε a s₁ s₂ : ℝ) :
    ∫ s in s₁..s₂, moll ε a s = cutoff ((a - s₁) / ε) - cutoff ((a - s₂) / ε) := by
  rw [integral_eq_sub_of_hasDerivAt (fun s _ => hasDerivAt_neg_cutoff ε a s)
    ((continuous_moll ε a).intervalIntegrable _ _)]
  ring

theorem integral_moll_le_one (ε a s₁ s₂ : ℝ) :
    ∫ s in s₁..s₂, moll ε a s ≤ 1 := by
  rw [integral_moll]
  linarith [cutoff_le_one ((a - s₁) / ε), cutoff_nonneg ((a - s₂) / ε)]

/-- Bound for the mollified integral of a bounded nonnegative function. -/
theorem integral_moll_mul_le {ε : ℝ} (hε : 0 < ε) (a : ℝ) {s₁ s₂ : ℝ} (hs : s₁ ≤ s₂)
    {F : ℝ → ℝ} (hF : ContinuousOn F (Icc s₁ s₂)) {M : ℝ} (hM : ∀ s ∈ Icc s₁ s₂, |F s| ≤ M) :
    |∫ s in s₁..s₂, moll ε a s * F s| ≤ M := by
  have hint : IntervalIntegrable (fun s => moll ε a s * F s) volume s₁ s₂ :=
    ((continuous_moll ε a).continuousOn.mul (by rwa [uIcc_of_le hs])).intervalIntegrable
  have hM0 : 0 ≤ M := by
    have := hM s₁ ⟨le_rfl, hs⟩; linarith [abs_nonneg (F s₁)]
  calc |∫ s in s₁..s₂, moll ε a s * F s| ≤ ∫ s in s₁..s₂, |moll ε a s * F s| :=
        abs_integral_le_integral_abs hs
    _ ≤ ∫ s in s₁..s₂, moll ε a s * M := by
        refine integral_mono_on hs hint.abs
          (((continuous_moll ε a).mul continuous_const).intervalIntegrable _ _) fun s hs' => ?_
        rw [abs_mul, abs_of_nonneg (moll_nonneg hε a s)]
        exact mul_le_mul_of_nonneg_left (hM s hs') (moll_nonneg hε a s)
    _ = M * ∫ s in s₁..s₂, moll ε a s := by rw [intervalIntegral.integral_mul_const, mul_comm]
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left (integral_moll_le_one ε a s₁ s₂) hM0
    _ = M := mul_one M

theorem exists_nat_one_div_lt {r : ℝ} (hr : 0 < r) :
    ∃ N : ℕ, ∀ k ≥ N, 1 / ((k : ℝ) + 1) < r := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / r)
  refine ⟨N, fun k hk => ?_⟩
  rw [div_lt_iff₀ (by positivity)]
  have : (N : ℝ) ≤ k := by exact_mod_cast hk
  rw [div_lt_iff₀ hr] at hN
  nlinarith

/-- Convergence of the mollified integrals along `ε_k = 1 / (k + 1)`. -/
theorem tendsto_integral_moll {s₁ s₂ : ℝ} (hs : s₁ ≤ s₂) {F : ℝ → ℝ}
    (hF : ContinuousOn F (Icc s₁ s₂)) (a : ℝ) :
    Tendsto (fun k : ℕ => ∫ s in s₁..s₂, moll (1 / ((k : ℝ) + 1)) a s * F s) atTop
      (𝓝 (if s₁ < a ∧ a ≤ s₂ then F a else 0)) := by
  have hε : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => by positivity
  by_cases ha₁ : a ≤ s₁
  · rw [show (if s₁ < a ∧ a ≤ s₂ then F a else 0) = 0 from
      ite_eq_right_iff.2 fun h' => by linarith [h'.1]]
    refine tendsto_const_nhds.congr fun k => ?_
    symm
    rw [integral_congr (g := fun _ => 0) fun s hs' => ?_]
    · simp
    · rw [uIcc_of_le hs] at hs'
      dsimp only
      rw [moll_eq_zero_of_le (hε k) (ha₁.trans hs'.1), zero_mul]
  push Not at ha₁
  by_cases ha₂ : s₂ < a
  · rw [show (if s₁ < a ∧ a ≤ s₂ then F a else 0) = 0 from
      ite_eq_right_iff.2 fun h' => by linarith [h'.2]]
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt (sub_pos.2 ha₂)
    refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun k hk => ?_⟩)
    symm
    dsimp only
    rw [integral_congr (g := fun _ => 0) fun s hs' => ?_]
    · simp
    · rw [uIcc_of_le hs] at hs'
      have := hN k hk
      dsimp only
      rw [moll_eq_zero_of_le' (hε k) (show s ≤ a - 1 / ((k : ℝ) + 1) by linarith [hs'.2]),
        zero_mul]
  push Not at ha₂
  rw [show (if s₁ < a ∧ a ≤ s₂ then F a else 0) = F a from
    ite_eq_left_iff.2 fun h' => absurd ⟨ha₁, ha₂⟩ h', Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨r, hr, hcont⟩ := Metric.continuousWithinAt_iff.1 (hF a ⟨ha₁.le, ha₂⟩) (δ / 2)
    (half_pos hδ)
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (lt_min hr (sub_pos.2 ha₁))
  refine ⟨N, fun k hk => ?_⟩
  set ε := 1 / ((k : ℝ) + 1)
  have hεk : ε < min r (a - s₁) := hN k hk
  have hεr : ε < r := lt_of_lt_of_le hεk (min_le_left _ _)
  have hεa : ε < a - s₁ := lt_of_lt_of_le hεk (min_le_right _ _)
  have hint1 : IntervalIntegrable (fun s => moll ε a s * (F s - F a)) volume s₁ s₂ :=
    ((continuous_moll ε a).continuousOn.mul ((hF.sub continuousOn_const).mono
      (by rw [uIcc_of_le hs]))).intervalIntegrable
  have hint2 : IntervalIntegrable (fun s => moll ε a s * F a) volume s₁ s₂ :=
    ((continuous_moll ε a).mul continuous_const).intervalIntegrable _ _
  have hsplit : ∫ s in s₁..s₂, moll ε a s * F s =
      (∫ s in s₁..s₂, moll ε a s * (F s - F a)) + F a := by
    have h1 : ∫ s in s₁..s₂, moll ε a s * F a = F a := by
      rw [intervalIntegral.integral_mul_const, integral_moll,
        cutoff_of_one_le ((one_le_div (hε k)).2 hεa.le),
        cutoff_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) (hε k).le)]
      ring
    have h2 : ∫ s in s₁..s₂, moll ε a s * F s = (∫ s in s₁..s₂, moll ε a s * (F s - F a)) +
        ∫ s in s₁..s₂, moll ε a s * F a := by
      rw [← integral_add hint1 hint2]
      exact integral_congr fun s _ => by ring
    rw [h2, h1]
  rw [Real.dist_eq, hsplit, add_sub_cancel_right]
  calc |∫ s in s₁..s₂, moll ε a s * (F s - F a)|
      ≤ ∫ s in s₁..s₂, |moll ε a s * (F s - F a)| := abs_integral_le_integral_abs hs
    _ ≤ ∫ s in s₁..s₂, moll ε a s * (δ / 2) := by
        refine integral_mono_on hs hint1.abs
          (((continuous_moll ε a).mul continuous_const).intervalIntegrable _ _) fun s hs' => ?_
        rw [abs_mul, abs_of_nonneg (moll_nonneg (hε k) a s)]
        by_cases h0 : moll ε a s = 0
        · rw [h0]; simp
        refine mul_le_mul_of_nonneg_left ?_ (moll_nonneg (hε k) a s)
        have h1 : s < a := by
          by_contra h'; exact h0 (moll_eq_zero_of_le (hε k) (not_lt.1 h'))
        have h2 : a - ε < s := by
          by_contra h'; exact h0 (moll_eq_zero_of_le' (hε k) (not_lt.1 h'))
        have := hcont hs' (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
        rw [Real.dist_eq] at this
        exact this.le
    _ = δ / 2 * ∫ s in s₁..s₂, moll ε a s := by
        rw [intervalIntegral.integral_mul_const, mul_comm]
    _ ≤ δ / 2 * 1 := mul_le_mul_of_nonneg_left (integral_moll_le_one ε a s₁ s₂)
        (by positivity)
    _ < δ := by linarith

end

end LorentzianCalderon
