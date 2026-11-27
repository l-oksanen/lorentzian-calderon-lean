module

public import Mathlib

public section

/-!
# A `C¹` cut-off function

`cutoff` is a `C¹` nondecreasing function equal to `0` on `(-∞, 0]` and to `1` on `[1, ∞)`,
the primitive of `cutoffDeriv r = 6 c (1 - c)` with `c = max 0 (min r 1)` (the smoothstep
`3r² - 2r³` on `[0, 1]`). Smooth cut-offs equal to `1` near a compact set: `exists_cutoff`.
-/

namespace LorentzianCalderon

noncomputable section
open Set Filter intervalIntegral
open scoped ContDiff Topology

/-- The derivative of the cut-off function. -/
def cutoffDeriv (r : ℝ) : ℝ := 6 * max 0 (min r 1) * (1 - max 0 (min r 1))

/-- The cut-off function. -/
def cutoff (r : ℝ) : ℝ := ∫ t in (0 : ℝ)..r, cutoffDeriv t

theorem continuous_cutoffDeriv : Continuous cutoffDeriv := by
  unfold cutoffDeriv; fun_prop

theorem cutoffDeriv_nonneg (r : ℝ) : 0 ≤ cutoffDeriv r := by
  unfold cutoffDeriv
  have h1 : 0 ≤ max 0 (min r 1) := le_max_left _ _
  have h2 : max 0 (min r 1) ≤ 1 := max_le zero_le_one (min_le_right _ _)
  have := mul_nonneg h1 (sub_nonneg.2 h2)
  nlinarith

theorem cutoffDeriv_le (r : ℝ) : cutoffDeriv r ≤ 2 := by
  unfold cutoffDeriv
  nlinarith [sq_nonneg (max 0 (min r 1) - 1 / 2)]

theorem cutoffDeriv_of_nonpos {r : ℝ} (hr : r ≤ 0) : cutoffDeriv r = 0 := by
  simp [cutoffDeriv, max_eq_left (min_le_of_left_le hr)]

theorem cutoffDeriv_of_one_le {r : ℝ} (hr : 1 ≤ r) : cutoffDeriv r = 0 := by
  simp [cutoffDeriv, min_eq_right hr]

theorem cutoffDeriv_eq {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) : cutoffDeriv r = 6 * r * (1 - r) := by
  simp [cutoffDeriv, min_eq_left h1, max_eq_right h0]

theorem one_le_cutoffDeriv {r : ℝ} (h0 : 1 / 4 ≤ r) (h1 : r ≤ 3 / 4) : 1 ≤ cutoffDeriv r := by
  rw [cutoffDeriv_eq (by linarith) (by linarith)]
  nlinarith

theorem hasDerivAt_cutoff (r : ℝ) : HasDerivAt cutoff (cutoffDeriv r) r :=
  (continuous_cutoffDeriv.integral_hasStrictDerivAt 0 r).hasDerivAt

theorem deriv_cutoff : deriv cutoff = cutoffDeriv :=
  funext fun r => (hasDerivAt_cutoff r).deriv

theorem differentiable_cutoff : Differentiable ℝ cutoff :=
  fun r => (hasDerivAt_cutoff r).differentiableAt

theorem contDiff_cutoff : ContDiff ℝ 1 cutoff := by
  rw [contDiff_one_iff_deriv, deriv_cutoff]
  exact ⟨differentiable_cutoff, continuous_cutoffDeriv⟩

theorem cutoff_of_nonpos {r : ℝ} (hr : r ≤ 0) : cutoff r = 0 := by
  unfold cutoff
  rw [integral_congr (g := fun _ => 0) fun t ht => ?_]
  · simp
  · rw [uIcc_of_ge hr] at ht
    exact cutoffDeriv_of_nonpos ht.2

theorem cutoff_one : cutoff 1 = 1 := by
  unfold cutoff
  rw [integral_congr (g := fun t => 6 * t - 6 * t ^ 2) fun t ht => ?_]
  · rw [integral_sub, integral_const_mul, integral_const_mul]
    · norm_num
    all_goals exact (by fun_prop : Continuous fun t : ℝ => _).intervalIntegrable _ _
  · rw [uIcc_of_le zero_le_one] at ht
    rw [cutoffDeriv_eq ht.1 ht.2]; ring

theorem cutoff_of_one_le {r : ℝ} (hr : 1 ≤ r) : cutoff r = 1 := by
  have hint : ∀ a b : ℝ, IntervalIntegrable cutoffDeriv MeasureTheory.volume a b :=
    fun a b => continuous_cutoffDeriv.intervalIntegrable a b
  unfold cutoff
  rw [← integral_add_adjacent_intervals (hint 0 1) (hint 1 r)]
  rw [integral_congr (a := 1) (g := fun _ => 0) fun t ht => ?_]
  · simpa [cutoff] using cutoff_one
  · rw [uIcc_of_le hr] at ht
    exact cutoffDeriv_of_one_le ht.1

theorem monotone_cutoff : Monotone cutoff :=
  monotone_of_deriv_nonneg differentiable_cutoff fun r => by
    rw [deriv_cutoff]; exact cutoffDeriv_nonneg r

theorem cutoff_nonneg (r : ℝ) : 0 ≤ cutoff r := by
  rcases le_total r 0 with h | h
  · rw [cutoff_of_nonpos h]
  · rw [← cutoff_of_nonpos le_rfl]; exact monotone_cutoff h

theorem cutoff_le_one (r : ℝ) : cutoff r ≤ 1 := by
  rcases le_total r 1 with h | h
  · rw [← cutoff_one]; exact monotone_cutoff h
  · rw [cutoff_of_one_le h]

/-- A smooth cut-off with values in `[0, 1]` and compact support in the open set `U`, equal to `1`
near the compact set `K ⊆ U`. -/
theorem exists_cutoff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {K U : Set V} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : V → ℝ, ContDiff ℝ ∞ χ ∧ (∀ x, χ x ∈ Icc 0 1) ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ U ∧ ∀ x ∈ K, χ =ᶠ[𝓝 x] 1 := by
  obtain ⟨U₁, hU₁, hKU₁, hU₁U, hU₁c⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨U₂, hU₂, hU₁U₂, hU₂U, hU₂c⟩ :=
    exists_open_between_and_isCompact_closure hU₁c hU hU₁U
  obtain ⟨χ, hχ, hχr, hχs, hχ1⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hU₂ isClosed_closure hU₁U₂
  have hts : tsupport χ = closure U₂ := by rw [tsupport, hχs]
  refine ⟨χ, hχ, fun x => hχr ⟨x, rfl⟩, ?_, hts ▸ hU₂U, fun x hx => ?_⟩
  · rw [HasCompactSupport, hts]
    exact hU₂c
  · filter_upwards [hU₁.mem_nhds (hKU₁ hx)] with y hy
    exact (hχ1 y).1 (subset_closure hy)

end

end LorentzianCalderon
