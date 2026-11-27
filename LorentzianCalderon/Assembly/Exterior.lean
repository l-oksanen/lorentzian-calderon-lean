module

public import LorentzianCalderon.Setting.Escape

public section

/-!
# The exterior of the box

The complement `O₀` of `M₀` is connected for `n ≥ 1`, and an admissible metric has a time
orientation for which `∂ₜ` is future-directed on `O₀` (blueprint, `thm_main`, Step 1).
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Set Metric

variable {n : ℕ} {T : ℝ}

lemma smul_mem_M0 {x : E n} (hx : x ∈ M0 n T) {c : ℝ} (hc : |c| ≤ 1) : c • x ∈ M0 n T := by
  rw [mem_M0] at hx ⊢
  refine ⟨?_, fun i => ?_⟩
  · simp only [PiLp.smul_apply, smul_eq_mul, abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) hc).trans hx.1
  · simp only [PiLp.smul_apply, smul_eq_mul, abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) hc).trans (hx.2 i)

lemma norm_lt_of_mem_M0 {x : E n} (hx : x ∈ M0 n T) : ‖x‖ < |T| + n + 1 := by
  have h0 : |x 0| ≤ |T| := (mem_M0.1 hx).1.trans (le_abs_self T)
  have hs := norm_spatial_le_of_mem_M0 hx
  have hsq : √(n : ℝ) < n + 1 := by
    rw [Real.sqrt_lt' (by positivity)]
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hnorm : ‖x‖ ≤ |x 0| + ‖spatial x‖ := by
    have h := norm_sq_eq_time_sq_add x
    have : ‖x‖ ^ 2 ≤ (|x 0| + ‖spatial x‖) ^ 2 := by
      rw [h, add_sq, sq_abs]
      nlinarith [abs_nonneg (x 0), norm_nonneg (spatial x)]
    exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) this
  linarith [Real.sqrt_nonneg (n : ℝ)]

/-- `O₀ = ℝ^{1+n} \ M₀` is connected. -/
theorem isConnected_compl_M0 (hn : 1 ≤ n) (hT : 0 ≤ T) : IsConnected (M0 n T)ᶜ := by
  set R : ℝ := |T| + n + 1
  have hR : 0 < R := by positivity
  have hrank : 1 < Module.rank ℝ (E n) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace, Fintype.card_fin]
    exact_mod_cast Nat.succ_lt_succ (Nat.succ_le_iff.1 hn)
  have hsph : sphere (0 : E n) R ⊆ (M0 n T)ᶜ := fun x hx hM => by
    have := norm_lt_of_mem_M0 hM
    rw [mem_sphere_zero_iff_norm] at hx
    linarith
  obtain ⟨x₀, hx₀⟩ : (sphere (0 : E n) R).Nonempty := NormedSpace.sphere_nonempty.2 hR.le
  refine ⟨⟨x₀, hsph hx₀⟩, isPreconnected_of_forall x₀ fun y hy => ?_⟩
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hy (mem_M0.2 ⟨by simpa using hT, fun i => by simp⟩)
  have hny : 0 < ‖y‖ := norm_pos_iff.2 hy0
  set c₁ := R / ‖y‖
  set ray := (fun c : ℝ => c • y) '' Icc (min 1 c₁) (max 1 c₁)
  have hray : IsPreconnected ray :=
    isPreconnected_Icc.image _ (by fun_prop : Continuous fun c : ℝ => c • y).continuousOn
  have hc₁ : c₁ • y ∈ sphere (0 : E n) R := by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_of_nonneg (by positivity),
      div_mul_cancel₀ _ hny.ne']
  have hc₁ray : c₁ • y ∈ ray := ⟨c₁, ⟨min_le_right _ _, le_max_right _ _⟩, rfl⟩
  refine ⟨sphere 0 R ∪ ray, union_subset hsph ?_, Or.inl hx₀,
    Or.inr ⟨1, ⟨min_le_left _ _, le_max_left _ _⟩, one_smul _ _⟩,
    (isConnected_sphere hrank 0 hR.le).isPreconnected.union _ hc₁ hc₁ray hray⟩
  rintro _ ⟨c, ⟨hc1, hc2⟩, rfl⟩ hM
  rcases le_or_gt 1 c with h1 | h1
  · refine hy ?_
    have := smul_mem_M0 hM (c := c⁻¹) (by
      rw [abs_inv, abs_of_pos (by linarith)]
      exact inv_le_one_of_one_le₀ h1)
    rwa [smul_smul, inv_mul_cancel₀ (by linarith), one_smul] at this
  · have hcc : c₁ ≤ c := by
      rcases min_choice 1 c₁ with h | h <;> rw [h] at hc1
      · linarith
      · exact hc1
    have := norm_lt_of_mem_M0 hM
    have hc0 : 0 ≤ c := (by positivity : (0 : ℝ) ≤ c₁).trans hcc
    rw [norm_smul, Real.norm_of_nonneg hc0] at this
    have : R ≤ c * ‖y‖ := by
      calc R = c₁ * ‖y‖ := (div_mul_cancel₀ _ hny.ne').symm
        _ ≤ c * ‖y‖ := by gcongr
    linarith

/-- Step 1 of `thm_main`: an admissible metric has a time orientation, for which it is globally
hyperbolic, such that `∂ₜ` is future-directed outside `M₀`. -/
theorem IsAdmissibleMetric.exists_future_dt (hn : 1 ≤ n) (hT : 0 ≤ T) {g : MatrixField n}
    (hg : IsAdmissibleMetric n T g) :
    ∃ Y, IsGloballyHyperbolic g Y ∧
      ∀ x ∉ M0 n T, form (g x) (EuclideanSpace.single 0 1) (Y x) < 0 := by
  obtain ⟨Y, hY⟩ := hg.globallyHyperbolic
  have hform : ∀ (Z : E n → E n) x, x ∉ M0 n T →
      form (g x) (EuclideanSpace.single 0 1) (Z x) = -Z x 0 := fun Z x hx => by
    rw [hg.minkowski_exterior x hx, form_minkowski_single_zero]
  have hne : ∀ x ∈ (M0 n T)ᶜ, Y x 0 ≠ 0 := fun x hx => by
    have := hY.timeOrientation.timelike x
    rw [hg.minkowski_exterior x hx] at this
    exact ne_zero_time_of_form_minkowski this.le fun h => by simp [h] at this
  have hc : Continuous fun x => Y x 0 := by
    have := hY.timeOrientation.continuous
    fun_prop
  have hconn := ((isConnected_compl_M0 hn hT).isPreconnected.image _ hc.continuousOn).ordConnected
  have hsign : ∀ x ∈ (M0 n T)ᶜ, ∀ y ∈ (M0 n T)ᶜ, 0 < Y x 0 → 0 < Y y 0 := by
    intro x hx y hy hxp
    by_contra hyp
    have hyn : Y y 0 < 0 := lt_of_le_of_ne (not_lt.1 hyp) (hne y hy)
    obtain ⟨z, hz, hz0⟩ := hconn.out ⟨y, hy, rfl⟩ ⟨x, hx, rfl⟩ ⟨hyn.le, hxp.le⟩
    exact hne z hz hz0
  by_cases hpos : ∃ x ∈ (M0 n T)ᶜ, 0 < Y x 0
  · obtain ⟨x, hx, hxp⟩ := hpos
    refine ⟨Y, hY, fun y hy => ?_⟩
    rw [hform Y y hy]
    linarith [hsign x hx y hy hxp]
  · push Not at hpos
    refine ⟨-Y, hY.neg, fun y hy => ?_⟩
    rw [hform _ y hy]
    have := lt_of_le_of_ne (hpos y hy) (hne y hy)
    simp only [Pi.neg_apply, PiLp.neg_apply, neg_neg]
    exact this

end

end LorentzianCalderon
