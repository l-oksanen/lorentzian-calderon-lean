module

public import LorentzianCalderon.Causal.Fuzzy
public import LorentzianCalderon.Setting.Escape

public section

/-!
# The fuzzy time function

`fuzzyTime g Y σ ε p` is the supremum, over the fuzzy chains `c 0, …, c m = p` of size `ε`, of
`length + 3 σ (c 0)⁰`. By construction it increases by at least
`‖z' - z‖` along every fuzzy step `z → z'` (`fuzzyTime_add_le`), and it is lower semicontinuous
since fuzzy steps are open conditions on their end point (`lowerSemicontinuous_fuzzyTime`).

It is finite, with `3 σ p⁰ ≤ fuzzyTime p ≤ 3 σ p⁰ + C`, once the fuzzy chains satisfy
`length + 3 σ (c 0)⁰ ≤ 3 σ (c m)⁰ + C` (`exists_fuzzy_value_bound`). Outside a ball containing
the box `M₀` the metric is Minkowskian and `σ ∂ₜ` is future-directed (`IsSpacetime.exterior`),
so a fuzzy step `Δ` from there has `‖Δ‖ ≤ 3 σ Δ⁰`: time increases. A chain leaving the ball
`‖x‖ ≤ R` can therefore come back only after a bounded excursion, so the part of the chain from
its first to its last step in that ball stays in a fixed compact set, where its length is
bounded by `exists_fuzzy_length_bound`; the other steps have `‖Δ‖ ≤ 3 σ Δ⁰`.
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Set Filter Metric

variable {n : ℕ} {g : MatrixField n} {Y : E n → E n}

/-- `|x⁰| ≤ ‖x‖`. -/
theorem abs_apply_zero_le (x : E n) : |x 0| ≤ ‖x‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x 0

/-- `|σ x⁰| ≤ ‖x‖` for `|σ| ≤ 1`. -/
theorem abs_mul_apply_zero_le {σ : ℝ} (hσ : |σ| ≤ 1) (x : E n) : |σ * x 0| ≤ ‖x‖ := by
  rw [abs_mul]
  calc |σ| * |x 0| ≤ 1 * |x 0| := by gcongr
    _ ≤ ‖x‖ := by rw [one_mul]; exact abs_apply_zero_le x

/-! ### Chains with time gains -/

section Runs

variable {c : ℕ → E n} {σ : ℝ}

/-- Along steps with `‖Δ‖ ≤ 3 σ Δ⁰`, the distance covered is at most `3 σ` times the gain in
time. -/
theorem norm_sub_le_of_run {a b : ℕ}
    (hP : ∀ i, a ≤ i → i < b → ‖c (i + 1) - c i‖ ≤ 3 * (σ * c (i + 1) 0 - σ * c i 0)) :
    ∀ j, a ≤ j → j ≤ b → ‖c j - c a‖ ≤ 3 * (σ * c j 0 - σ * c a 0) := by
  intro j haj hjb
  induction j, haj using Nat.le_induction with
  | base => simp
  | succ j haj ih =>
    have h1 := ih (by omega)
    have h2 := hP j haj (by omega)
    calc ‖c (j + 1) - c a‖ = ‖(c j - c a) + (c (j + 1) - c j)‖ := by congr 1; abel
      _ ≤ ‖c j - c a‖ + ‖c (j + 1) - c j‖ := norm_add_le _ _
      _ ≤ _ := by linarith

/-- A polygon `c 0, …, c m` with steps of length `≤ 1`, and `‖Δ‖ ≤ 3 σ Δ⁰` for the steps
starting outside the ball `‖x‖ ≤ R`, has `length + 3 σ (c 0)⁰ ≤ 3 σ (c m)⁰ + 4 Λ`, if the
pieces in the ball `‖x‖ ≤ 7 R + 4` have length `≤ Λ`. -/
theorem chainLength_add_le {m : ℕ} {R Λ : ℝ} (hσ : |σ| ≤ 1)
    (hstep : ∀ i < m, ‖c (i + 1) - c i‖ ≤ 1)
    (hext : ∀ i < m, R < ‖c i‖ → ‖c (i + 1) - c i‖ ≤ 3 * (σ * c (i + 1) 0 - σ * c i 0))
    (hsub : ∀ a b, a ≤ b → b ≤ m → (∀ j, a ≤ j → j ≤ b → ‖c j‖ ≤ 7 * R + 4) →
      chainLength (b - a) (fun j => c (a + j)) ≤ Λ) :
    chainLength m c + 3 * (σ * c 0 0) ≤ 3 * (σ * c m 0) + 4 * max Λ 0 := by
  classical
  have htel : ∑ i ∈ Finset.range m, 3 * (σ * c (i + 1) 0 - σ * c i 0) =
      3 * (σ * c m 0) - 3 * (σ * c 0 0) := by
    rw [← Finset.mul_sum, Finset.sum_range_sub (fun i => σ * c i 0)]
    ring
  have hd : ∀ i, ‖c (i + 1) - c i‖ - 3 * (σ * c (i + 1) 0 - σ * c i 0) ≤
      4 * ‖c (i + 1) - c i‖ := by
    intro i
    have h1 := abs_mul_apply_zero_le hσ (c (i + 1) - c i)
    rw [PiLp.sub_apply, mul_sub] at h1
    linarith [neg_abs_le (σ * c (i + 1) 0 - σ * c i 0)]
  suffices hs : ∑ i ∈ Finset.range m,
      (‖c (i + 1) - c i‖ - 3 * (σ * c (i + 1) 0 - σ * c i 0)) ≤ 4 * max Λ 0 by
    rw [Finset.sum_sub_distrib, htel] at hs
    simp only [chainLength_def]
    linarith
  have hmax : 0 ≤ 4 * max Λ 0 := by positivity
  by_cases hI : ∃ i, i < m ∧ ‖c i‖ ≤ R
  swap
  · push Not at hI
    calc _ ≤ ∑ i ∈ Finset.range m, (0 : ℝ) := Finset.sum_le_sum fun i hi => by
            have := hext i (Finset.mem_range.1 hi) (hI i (Finset.mem_range.1 hi))
            linarith
      _ ≤ _ := by simp
  obtain ⟨hi₁m, hi₁R⟩ := Nat.find_spec hI
  set i₁ := Nat.find hI
  set i₂ := Nat.findGreatest (fun i => ‖c i‖ ≤ R) (m - 1)
  have hi₂R : ‖c i₂‖ ≤ R :=
    Nat.findGreatest_spec (P := fun i => ‖c i‖ ≤ R) (show i₁ ≤ m - 1 by omega) hi₁R
  have hi₂m : i₂ < m := by
    have := Nat.findGreatest_le (P := fun i => ‖c i‖ ≤ R) (m - 1)
    omega
  have hi₁₂ : i₁ ≤ i₂ :=
    Nat.le_findGreatest (P := fun i => ‖c i‖ ≤ R) (show i₁ ≤ m - 1 by omega) hi₁R
  have hmem : ∀ i < m, ‖c i‖ ≤ R → i₁ ≤ i ∧ i ≤ i₂ := fun i hi hR' =>
    ⟨Nat.find_min' hI ⟨hi, hR'⟩,
      Nat.le_findGreatest (P := fun i => ‖c i‖ ≤ R) (show i ≤ m - 1 by omega) hR'⟩
  have hconf : ∀ j, i₁ ≤ j → j ≤ i₂ + 1 → ‖c j‖ ≤ 7 * R + 4 := by
    intro j hj1 hj2
    have hR0 : 0 ≤ R := (norm_nonneg _).trans hi₁R
    rcases (show j = i₂ + 1 ∨ j ≤ i₂ by omega) with rfl | hj
    · have := hstep i₂ hi₂m
      have := norm_le_norm_add_norm_sub' (c (i₂ + 1)) (c i₂)
      linarith
    by_cases hjR : ‖c j‖ ≤ R
    · linarith
    set a := Nat.findGreatest (fun i => ‖c i‖ ≤ R) j
    have haR : ‖c a‖ ≤ R := Nat.findGreatest_spec (P := fun i => ‖c i‖ ≤ R) hj1 hi₁R
    have haj : a ≤ j := Nat.findGreatest_le j
    have haj' : a < j := lt_of_le_of_ne haj fun h => hjR (h ▸ haR)
    have hJ : ∃ b, j ≤ b ∧ b < m ∧ ‖c b‖ ≤ R := ⟨i₂, hj, hi₂m, hi₂R⟩
    obtain ⟨hjb, hbm, hbR⟩ := Nat.find_spec hJ
    set b := Nat.find hJ
    have hout : ∀ i, a < i → i < b → R < ‖c i‖ := by
      intro i hai hib
      by_contra h
      push Not at h
      rcases le_total i j with hij | hji
      · exact Nat.findGreatest_is_greatest hai hij h
      · exact Nat.find_min hJ hib ⟨hji, by omega, h⟩
    have hP : ∀ i, a + 1 ≤ i → i < b →
        ‖c (i + 1) - c i‖ ≤ 3 * (σ * c (i + 1) 0 - σ * c i 0) := fun i h1 h2 =>
      hext i (by omega) (hout i (by omega) h2)
    have h1 := norm_sub_le_of_run hP j (by omega) hjb
    have h2 := norm_sub_le_of_run (a := j) (fun i h1 h2 => hP i (by omega) h2) b hjb le_rfl
    have h3 := (le_abs_self _).trans ((abs_mul_apply_zero_le hσ (c b)).trans hbR)
    have h4 : ‖c (a + 1)‖ ≤ R + 1 := by
      have := hstep a (by omega)
      have := norm_le_norm_add_norm_sub' (c (a + 1)) (c a)
      linarith
    have h5 := neg_abs_le (σ * c (a + 1) 0)
    have h6 := abs_mul_apply_zero_le hσ (c (a + 1))
    have h7 := norm_le_norm_add_norm_sub' (c j) (c (a + 1))
    have h8 := norm_nonneg (c b - c j)
    linarith
  have hlenb := hsub i₁ (i₂ + 1) (by omega) (by omega) hconf
  rw [chainLength_shift (by omega)] at hlenb
  calc _ ≤ ∑ i ∈ Finset.range m,
        (if i ∈ Finset.Ico i₁ (i₂ + 1) then 4 * ‖c (i + 1) - c i‖ else 0) :=
        Finset.sum_le_sum fun i hi => by
          have hi' := Finset.mem_range.1 hi
          split_ifs with h
          · exact hd i
          · have : R < ‖c i‖ := by
              by_contra h'
              push Not at h'
              obtain ⟨a1, a2⟩ := hmem i hi' h'
              exact h (Finset.mem_Ico.2 ⟨a1, by omega⟩)
            linarith [hext i hi' this]
    _ = ∑ i ∈ Finset.Ico i₁ (i₂ + 1), 4 * ‖c (i + 1) - c i‖ := by
        rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 fun i hi => Finset.mem_range.2 (by
          rw [Finset.mem_Ico] at hi
          omega)]
    _ = 4 * (chainLength (i₂ + 1) c - chainLength i₁ c) := by
        rw [← Finset.mul_sum, Finset.sum_Ico_eq_sub _ (by omega), chainLength_def, chainLength_def]
    _ ≤ 4 * max Λ 0 := by linarith [le_max_left Λ 0]

end Runs

/-! ### The fuzzy time function -/

/-- The values `length + 3 σ (c 0)⁰` of the fuzzy chains `c 0, …, c m = p` of size `ε`. -/
def fuzzyValues (g : MatrixField n) (Y : E n → E n) (σ ε : ℝ) (p : E n) : Set ℝ :=
  {s | ∃ (m : ℕ) (c : ℕ → E n), IsFuzzyChain g Y ε m c ∧ c m = p ∧
    s = chainLength m c + 3 * (σ * c 0 0)}

/-- The fuzzy time function: the supremum of `length + 3 σ (c 0)⁰` over the fuzzy chains
`c 0, …, c m = p` of size `ε`. -/
def fuzzyTime (g : MatrixField n) (Y : E n → E n) (σ ε : ℝ) (p : E n) : ℝ :=
  sSup (fuzzyValues g Y σ ε p)

/-- Appending a fuzzy step to a fuzzy chain. -/
theorem IsFuzzyChain.append {ε : ℝ} {m : ℕ} {c : ℕ → E n} (hc : IsFuzzyChain g Y ε m c)
    {z' : E n} (hs : IsFuzzyStep g Y ε (c m) z') :
    ∃ c' : ℕ → E n, IsFuzzyChain g Y ε (m + 1) c' ∧ c' (m + 1) = z' ∧ c' 0 = c 0 ∧
      chainLength (m + 1) c' = chainLength m c + ‖z' - c m‖ := by
  classical
  refine ⟨fun i => if i ≤ m then c i else z', isFuzzyChain_iff.2 fun i hi => ?_, by simp, by simp,
    ?_⟩
  · rcases (show i < m ∨ i = m by omega) with h | rfl
    · simpa [h.le, show i + 1 ≤ m by omega] using (isFuzzyChain_iff.1 hc) i h
    · simpa using hs
  · rw [chainLength_succ]
    simp only [le_refl, ite_true, show ¬ m + 1 ≤ m by omega, ite_false]
    congr 1
    rw [chainLength_def, chainLength_def]
    refine Finset.sum_congr rfl fun i hi => ?_
    have := Finset.mem_range.1 hi
    simp [this.le, show i + 1 ≤ m by omega]

section Bounded

variable {σ ε C : ℝ}

/-- The chain of one point gives the value `3 σ p⁰`. -/
theorem mem_fuzzyValues_self (p : E n) : 3 * (σ * p 0) ∈ fuzzyValues g Y σ ε p :=
  ⟨0, fun _ => p, isFuzzyChain_iff.2 fun i hi => absurd hi (Nat.not_lt_zero _), rfl,
    by simp [chainLength_zero]⟩

variable (hB : ∀ (m : ℕ) (c : ℕ → E n), IsFuzzyChain g Y ε m c →
  chainLength m c + 3 * (σ * c 0 0) ≤ 3 * (σ * c m 0) + C)
include hB

/-- The values at `p` are bounded by `3 σ p⁰ + C`. -/
theorem bddAbove_fuzzyValues (p : E n) : BddAbove (fuzzyValues g Y σ ε p) :=
  ⟨3 * (σ * p 0) + C, by
    rintro s ⟨m, c, hc, rfl, rfl⟩
    exact hB m c hc⟩

/-- Every value at `p` is at most `fuzzyTime p`. -/
theorem le_fuzzyTime {p : E n} {s : ℝ} (hs : s ∈ fuzzyValues g Y σ ε p) :
    s ≤ fuzzyTime g Y σ ε p :=
  le_csSup (bddAbove_fuzzyValues hB p) hs

/-- `3 σ p⁰ ≤ fuzzyTime p ≤ 3 σ p⁰ + C`. -/
theorem fuzzyTime_bounds (p : E n) :
    3 * (σ * p 0) ≤ fuzzyTime g Y σ ε p ∧ fuzzyTime g Y σ ε p ≤ 3 * (σ * p 0) + C :=
  ⟨le_fuzzyTime hB (mem_fuzzyValues_self p), csSup_le ⟨_, mem_fuzzyValues_self p⟩ (by
    rintro s ⟨m, c, hc, rfl, rfl⟩
    exact hB m c hc)⟩

/-- The fuzzy time increases by at least `‖z' - z‖` along a fuzzy step `z → z'`. -/
theorem fuzzyTime_add_le {z z' : E n} (hs : IsFuzzyStep g Y ε z z') :
    fuzzyTime g Y σ ε z + ‖z' - z‖ ≤ fuzzyTime g Y σ ε z' := by
  have : fuzzyTime g Y σ ε z ≤ fuzzyTime g Y σ ε z' - ‖z' - z‖ := by
    refine csSup_le ⟨_, mem_fuzzyValues_self z⟩ ?_
    rintro s ⟨m, c, hc, hcm, rfl⟩
    rw [← hcm] at hs
    obtain ⟨c', hc', hc'm, hc'0, hc'len⟩ := hc.append hs
    have := le_fuzzyTime hB ⟨m + 1, c', hc', hc'm, rfl⟩
    rw [hc'len, hc'0, hcm] at this
    linarith
  linarith

/-- The fuzzy time is lower semicontinuous. -/
theorem lowerSemicontinuous_fuzzyTime : LowerSemicontinuous (fuzzyTime g Y σ ε) := by
  intro p s' hs'
  obtain ⟨s, ⟨m, c, hc, hcm, rfl⟩, hlt⟩ :=
    exists_lt_of_lt_csSup ⟨_, mem_fuzzyValues_self p⟩ hs'
  rcases m with _ | k
  · have hcont : Continuous fun y : E n => 3 * (σ * y 0) := by fun_prop
    rw [chainLength_zero, zero_add, show c 0 = p from hcm] at hlt
    filter_upwards [hcont.continuousAt.eventually (lt_mem_nhds hlt)] with y hy
    exact hy.trans_le (le_fuzzyTime hB (mem_fuzzyValues_self y))
  have hsk := (isFuzzyChain_iff.1 hc) k (Nat.lt_succ_self k)
  obtain ⟨x, w, hx, hw, hd⟩ := hsk.near
  have hck : IsFuzzyChain g Y ε k c :=
    isFuzzyChain_iff.2 fun i hi => (isFuzzyChain_iff.1 hc) i (by omega)
  have h1 : Continuous fun y : E n => ‖y - c k‖ := (continuous_id.sub continuous_const).norm
  have h2 : Continuous fun y : E n => ‖(y - c k) - w‖ :=
    ((continuous_id.sub continuous_const).sub continuous_const).norm
  have hO : IsOpen {y : E n | ‖y - c k‖ < ε ∧ ‖(y - c k) - w‖ < ε * ‖y - c k‖} :=
    (isOpen_lt h1 continuous_const).inter (isOpen_lt h2 (continuous_const.mul h1))
  have hpO : p ∈ {y : E n | ‖y - c k‖ < ε ∧ ‖(y - c k) - w‖ < ε * ‖y - c k‖} := by
    rw [← hcm]
    exact ⟨hsk.lt, hd⟩
  have hv : Continuous fun y : E n => chainLength k c + ‖y - c k‖ + 3 * (σ * c 0 0) :=
    (continuous_const.add h1).add continuous_const
  have hvp : s' < chainLength k c + ‖p - c k‖ + 3 * (σ * c 0 0) := by
    rw [← hcm, ← chainLength_succ]
    exact hlt
  filter_upwards [hO.mem_nhds hpO, hv.continuousAt.eventually (lt_mem_nhds hvp)] with y hy hvy
  obtain ⟨c', hc', hc'm, hc'0, hc'len⟩ := hck.append (z' := y) ⟨hy.1, x, w, hx, hw, hy.2⟩
  have := le_fuzzyTime hB ⟨k + 1, c', hc', hc'm, rfl⟩
  rw [hc'len, hc'0] at this
  linarith

end Bounded

/-! ### The bound in a spacetime -/

/-- The box `M₀` lies in the ball `‖x‖ ≤ |T| + n + 1`. -/
theorem norm_le_of_mem_M0 {T : ℝ} {x : E n} (hx : x ∈ M0 n T) : ‖x‖ ≤ |T| + n + 1 := by
  have h1 := norm_spatial_le_of_mem_M0 hx
  have h2 : |x 0| ≤ |T| := (mem_M0.1 hx).1.trans (le_abs_self T)
  have h3 : √(n : ℝ) ≤ n + 1 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have hsq := norm_sq_eq_time_sq_add x
  have : ‖x‖ ≤ |x 0| + ‖spatial x‖ := by
    have h4 := abs_nonneg (x 0)
    have h5 := norm_nonneg (spatial x)
    nlinarith [sq_abs (x 0), norm_nonneg x]
  linarith

/-- Outside `M₀`, a future causal vector `w` has `‖w‖ ≤ 2 σ w⁰`. -/
theorem norm_le_of_not_mem_M0 (hg : IsSpacetime g Y) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {x w : E n} (hgx : g x = minkowski n)
    (hfx : form (g x) (σ • EuclideanSpace.single 0 1) (Y x) < 0)
    (hw : IsFutureCausal g Y x w) : ‖w‖ ≤ 2 * (σ * w 0) := by
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have he : IsFutureCausal g Y x (σ • EuclideanSpace.single 0 1) := by
    refine ⟨smul_ne_zero (by rcases hσ with rfl | rfl <;> norm_num) (by simp), ?_, hfx⟩
    rw [hgx, form_minkowski_self]
    simp [sq_nonneg]
  have h1 := hw.form_nonpos hg he
  rw [hgx, form_minkowski] at h1
  simp only [PiLp.smul_apply, smul_eq_mul, map_smul, spatial_single_zero, smul_zero,
    inner_zero_right, add_zero, single_zero_apply_zero, mul_one] at h1
  have h2 := hw.causal
  rw [hgx, form_minkowski_self] at h2
  have hsq := norm_sq_eq_time_sq_add w
  have hσw : 0 ≤ σ * w 0 := by nlinarith
  have hw0 : w 0 ^ 2 = (σ * w 0) ^ 2 := by rw [mul_pow, ← sq σ] at *; nlinarith
  nlinarith [norm_nonneg w]

/-- A fuzzy step from far away has `‖Δ‖ ≤ 3 σ Δ⁰`. -/
theorem norm_sub_le_of_far (hg : IsSpacetime g Y) {T σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hext : ∀ x ∉ M0 n T, g x = minkowski n ∧
      form (g x) (σ • EuclideanSpace.single 0 1) (Y x) < 0)
    {ε : ℝ} (hε : ε ≤ 1 / 10) {z z' : E n} (hz : |T| + n + 2 < ‖z‖)
    (hs : IsFuzzyStep g Y ε z z') : ‖z' - z‖ ≤ 3 * (σ * z' 0 - σ * z 0) := by
  obtain ⟨x, w, hx, hw, hd⟩ := hs.near
  have hxM : x ∉ M0 n T := fun hxM => by
    have := norm_le_of_mem_M0 hxM
    have := norm_le_norm_add_norm_sub' z x
    rw [← dist_eq_norm, dist_comm] at this
    linarith
  obtain ⟨hgx, hfx⟩ := hext x hxM
  have h1 := norm_le_of_not_mem_M0 hg hσ hgx hfx hw
  have hσ1 : |σ| ≤ 1 := by rcases hσ with rfl | rfl <;> norm_num
  have h2 := abs_mul_apply_zero_le hσ1 ((z' - z) - w)
  simp only [PiLp.sub_apply, mul_sub] at h2
  have h3 : ‖z' - z‖ - ‖(z' - z) - w‖ ≤ ‖w‖ := by
    have := norm_sub_norm_le (z' - z) ((z' - z) - w)
    simpa using this
  have h4 := neg_abs_le (σ * z' 0 - σ * z 0 - σ * w 0)
  have h5 := norm_nonneg (z' - z)
  have h6 : ε * ‖z' - z‖ ≤ 1 / 10 * ‖z' - z‖ := by gcongr
  linarith

/-- In a causal spacetime, `length + 3 σ (c 0)⁰ ≤ 3 σ (c m)⁰ + C` for all fuzzy chains of some
size `ε`, where `σ ∂ₜ` is future-directed outside `M₀`. -/
theorem exists_fuzzy_value_bound (hg : IsSpacetime g Y)
    (hanti : ∀ p q, CausalLE g Y p q → CausalLE g Y q p → p = q) :
    ∃ σ : ℝ, |σ| ≤ 1 ∧ ∃ ε > 0, ∃ C, ∀ (m : ℕ) (c : ℕ → E n), IsFuzzyChain g Y ε m c →
      chainLength m c + 3 * (σ * c 0 0) ≤ 3 * (σ * c m 0) + C := by
  obtain ⟨T, σ, hσ, hext⟩ := hg.exterior
  set R := |T| + n + 2
  obtain ⟨ε₂, hε₂, Λ, hΛ⟩ :=
    exists_fuzzy_length_bound hg hanti (isCompact_closedBall (0 : E n) (7 * R + 4))
  refine ⟨σ, by rcases hσ with rfl | rfl <;> norm_num, min (1 / 10) ε₂, by positivity,
    4 * max Λ 0, fun m c hc => ?_⟩
  refine chainLength_add_le (by rcases hσ with rfl | rfl <;> norm_num)
    (fun i hi => (((isFuzzyChain_iff.1 hc) i hi).lt.trans_le ((min_le_left _ _).trans
      (by norm_num))).le)
    (fun i hi hR => norm_sub_le_of_far hg hσ hext (min_le_left _ _) hR
      ((isFuzzyChain_iff.1 hc) i hi))
    fun a b hab hbm hK => hΛ _ _ ((hc.mono (min_le_right _ _)).shift (by omega)) fun j hj => ?_
  rw [mem_closedBall_zero_iff]
  exact hK (a + j) (by omega) (by omega)

end

end LorentzianCalderon
