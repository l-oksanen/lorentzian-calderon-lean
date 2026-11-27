module

public import LorentzianCalderon.Local.Step.Core

public section

/-!
# The local continuation step: unique continuation across the top

The additional property of `prop_local_step`: a function of class `C^∞` on `V°` with `□_g w = 0`
on `V°` and `w = 0` on `V° ∩ {ψ > τ}` vanishes on `V°`. The proof applies the energy inequality
`eq_energy2` on the lenses `L_ρ ⊆ V°`, `ρ < R / 2`.
-/

namespace LorentzianCalderon

noncomputable section
open Set Matrix Filter MeasureTheory Metric
open scoped ContDiff Topology

variable {n : ℕ} {ι : Type*}

namespace StepData

variable {S : StepData n ι} (hS : S.Hyp)
include hS

namespace Ball

variable {R : ℝ} (hB : S.Ball R)
include hB

/-- A point of `V°` on the top is a limit of points of `V° ∩ {ψ > τ}`. -/
theorem mem_closure_Vo_top {x : E n} (hx : x ∈ S.Vo R) (hψ : S.ψ x = S.τ) :
    x ∈ closure {y | y ∈ S.Vo R ∧ S.τ < S.ψ y} := by
  have hxV := hB.subset (Vo_subset hB hx)
  refine closure_mono (fun y (hy : y ∈ {y | y ∈ S.Vo R ∧ S.ψ x < S.ψ y ∧ S.ψ x < S.ψ y}) =>
    (⟨hy.1, hψ ▸ hy.2.1⟩ : y ∈ {y | y ∈ S.Vo R ∧ S.τ < S.ψ y})) (hS.mem_closure_top hxV (f := S.ψ)
    (hS.differentiableAt_of_contDiffOn hS.smooth_ψ hxV) (hS.coform_ψ_neg hxV)
    ((isOpen_Vo hS hB).mem_nhds hx))

theorem isOpen_Vo_top : IsOpen {y | y ∈ S.Vo R ∧ S.τ < S.ψ y} :=
  ((continuousOn_ψ hS hB).mono (Vo_subset hB)).isOpen_inter_preimage (isOpen_Vo hS hB)
    isOpen_Ioi

/-- **Unique continuation** across the top of the lens. -/
theorem unique_continuation {w : E n → ℝ} (hw : ContDiffOn ℝ ∞ w (S.Vo R))
    (hbox : ∀ x ∈ S.Vo R, box S.g w x = 0) (htop : ∀ x ∈ S.Vo R, S.τ < S.ψ x → w x = 0) :
    ∀ x ∈ S.Vo R, w x = 0 := by
  have hVo := isOpen_Vo hS hB
  have hw2 : ContDiffOn ℝ 2 w (S.Vo R) := hw.of_le (by simp)
  have hcl : ∀ x ∈ S.Vo R, S.ψ x = S.τ → w x = 0 ∧ fderiv ℝ w x = 0 := fun x hx hψ =>
    eq_zero_and_fderiv_of_mem_closure hVo (hw.of_le (by simp)) (isOpen_Vo_top hS hB)
      (fun y hy => htop y hy.1 hy.2) hx (mem_closure_Vo_top hS hB hx hψ)
  intro x hx
  rcases lt_trichotomy (S.ψ x) S.τ with hlt | heq | hgt
  swap
  · exact (hcl x hx heq).1
  swap
  · exact htop x hx hgt
  set m := max (S.τ - S.ψt x) (‖x - S.q₀‖ ^ 2)
  have hr := half_pos hB
  have hm0 : 0 ≤ m := le_max_of_le_right (sq_nonneg _)
  have hmr : m < (R / 2) ^ 2 := by
    refine max_lt (by linarith [(mem_Vo_iff.1 hx).2]) ?_
    have := mem_ball.1 (mem_Vo_iff.1 hx).1
    rw [dist_eq_norm] at this
    exact pow_lt_pow_left₀ this (norm_nonneg _) two_ne_zero
  have hsm : √m < R / 2 := by
    rw [Real.sqrt_lt' hr]; exact hmr
  set ρ := (√m + R / 2) / 2 with hρdef
  have hρ0 : 0 ≤ ρ := by positivity
  have hρr : ρ < R / 2 := by rw [hρdef]; linarith
  have hmρ : m < ρ ^ 2 := by
    have h1 : √m < ρ := by rw [hρdef]; linarith
    have h2 := pow_lt_pow_left₀ h1 (Real.sqrt_nonneg m) two_ne_zero
    rwa [Real.sq_sqrt hm0] at h2
  have hset := setting hS hB hρ0 (hρr.trans (half_lt hB))
  have hLVo := L_subset_Vo (S := S) (R := R) hρ0 hρr
  obtain ⟨C, σ₀, H⟩ := hset.energy_volume
  set σ := max σ₀ 1
  have hσ : σ₀ ≤ σ := le_max_left _ _
  have hσ1 : 1 ≤ σ := le_max_right _ _
  have h := H σ hσ (S.Vo R) w hVo (by simpa only [L_def] using hLVo) hw2 fun y hy hψ => by
    obtain ⟨h1, h2⟩ := hcl y (hLVo (mem_L.2 hy)) hψ
    exact ⟨h1, d_eq_zero_of_fderiv h2⟩
  rw [← L_def] at h
  have hLc := isCompact_L hS hB hρ0 (hρr.trans (half_lt hB))
  have hLm := hLc.measurableSet
  have hz : ∫ y in S.L R ρ, Real.exp (2 * σ * S.ψ y) * box S.g w y ^ 2 = 0 := by
    rw [setIntegral_congr_fun hLm (g := fun _ => 0) fun y hy => by simp [hbox y (hLVo hy)]]
    simp
  rw [hz, mul_zero] at h
  have hψc : ContinuousOn S.ψ (S.Vo R) := (continuousOn_ψ hS hB).mono (Vo_subset hB)
  have hf : ContinuousOn (fun y => Real.exp (2 * σ * S.ψ y) * (‖d w y‖ ^ 2 + σ ^ 2 * w y ^ 2))
      (S.Vo R) :=
    (Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hψc)).mul
      (((continuousOn_pi.2 fun k => (contDiffOn_d hVo hw k).continuousOn).norm.pow
        2).add (continuousOn_const.mul (hw.continuousOn.pow 2)))
  have hf0 : ∀ y, 0 ≤ Real.exp (2 * σ * S.ψ y) * (‖d w y‖ ^ 2 + σ ^ 2 * w y ^ 2) := fun y =>
    by positivity
  have hI0 : ∫ y in S.L R ρ, Real.exp (2 * σ * S.ψ y) * (‖d w y‖ ^ 2 + σ ^ 2 * w y ^ 2) = 0 := by
    have hnn := setIntegral_nonneg (μ := volume) hLm fun y _ => hf0 y
    have : 0 < σ ^ 2 := by positivity
    nlinarith
  have hae := (setIntegral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall hf0)
    ((hf.mono hLVo).integrableOn_compact hLc)).1 hI0
  set O := (ball S.q₀ ρ ∩ S.ψt ⁻¹' Ioi (S.τ - ρ ^ 2)) ∩ S.ψ ⁻¹' Iio S.τ
  have hOL : O ⊆ S.L R ρ := fun y hy =>
    mem_L.2 ⟨ball_subset_ball (hρr.trans (half_lt hB)).le hy.1.1, (le_of_lt hy.2 : S.ψ y ≤ S.τ),
      (le_of_lt hy.1.2 : S.τ - ρ ^ 2 ≤ S.ψt y)⟩
  have hOopen : IsOpen O := by
    have hc := (hS.contDiffOn_ψt.continuousOn.mono (hB.subset)).mono
      (ball_subset_ball (hρr.trans (half_lt hB)).le)
    have h1 := hc.isOpen_inter_preimage isOpen_ball (isOpen_Ioi (a := S.τ - ρ ^ 2))
    exact (((continuousOn_ψ hS hB).mono (ball_subset_ball (hρr.trans (half_lt hB)).le)).mono
      (inter_subset_left (t := S.ψt ⁻¹' Ioi (S.τ - ρ ^ 2)))).isOpen_inter_preimage h1
      (isOpen_Iio (a := S.τ))
  have hxO : x ∈ O := by
    refine ⟨⟨?_, ?_⟩, (hlt : S.ψ x < S.τ)⟩
    · rw [mem_ball, dist_eq_norm]
      have : ‖x - S.q₀‖ ^ 2 < ρ ^ 2 := lt_of_le_of_lt (le_max_right _ _) hmρ
      exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hρ0 two_ne_zero).1 this
    · have : S.τ - S.ψt x < ρ ^ 2 := lt_of_le_of_lt (le_max_left _ _) hmρ
      show S.τ - ρ ^ 2 < S.ψt x
      linarith
  have heq := Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset hOL hae) hOopen
    (hf.mono (hOL.trans hLVo)) continuousOn_const hxO
  simp only [Pi.zero_apply] at heq
  have h2 := (mul_eq_zero.1 heq).resolve_left (Real.exp_pos _).ne'
  have h3 : σ ^ 2 * w x ^ 2 = 0 := by
    have := sq_nonneg ‖d w x‖; have := mul_nonneg (sq_nonneg σ) (sq_nonneg (w x)); linarith
  have hσ0 : σ ^ 2 ≠ 0 := by positivity
  exact pow_eq_zero_iff two_ne_zero |>.1 ((mul_eq_zero.1 h3).resolve_left hσ0)

end Ball

end StepData

end

end LorentzianCalderon
