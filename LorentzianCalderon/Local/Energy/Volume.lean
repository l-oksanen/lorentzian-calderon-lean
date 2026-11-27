module

public import LorentzianCalderon.Local.Energy.Limits

public section

/-!
# The volume estimate on `L ∩ {φ > s}`

For a function `φ` whose `-grad φ` is past causal or zero relative to `-grad ψ` (eikonal of
future type, or constant), the flux through the level sets of `φ` is nonnegative and can be
dropped, which gives the volume part of the weighted energy inequality.
-/

namespace LorentzianCalderon

noncomputable section
open Set MeasureTheory Filter Topology
open scoped ContDiff

variable {n : ℕ}

namespace EnergySetting

variable {V : Set (E n)} {g : MatrixField n} {Y : E n → E n} {ψ ψ' : E n → ℝ} {τ c : ℝ}
  (h : EnergySetting V g Y ψ ψ' τ c)
include h

omit h in
theorem continuousOn_norm_d (_ : EnergySetting V g Y ψ ψ' τ c) {U : Set (E n)} (hU : IsOpen U)
    {w : E n → ℝ}
    (hw : ContDiffOn ℝ 2 w U) : ContinuousOn (fun x => ‖d w x‖) U :=
  (continuousOn_d hU (hw.of_le one_le_two)).norm

theorem integral_fluxG_nonneg {φ : E n → ℝ}
    (hφc : ∀ x ∈ V, bil (g x)⁻¹ (d φ x) (d φ x) ≤ 0 ∧ bil (g x)⁻¹ (d φ x) (d ψ x) ≤ 0)
    {w : E n → ℝ} {σ lam : ℝ} (hlam : 0 ≤ lam) (s ε : ℝ) (hε : 0 < ε) :
    0 ≤ ∫ x in lens V ψ ψ' τ c, fluxG g ψ ψ' φ w τ c σ lam s ε x := by
  refine setIntegral_nonneg h.measurableSet_lens fun x hx => ?_
  have hxV := h.lens_subset hx
  have hT : 0 ≤ wT g ψ w σ lam φ x := by
    simp only [wT_def]
    refine mul_nonneg (mul_nonneg (Real.exp_pos _).le (vol_pos (h.det_ne_zero hxV)).le) ?_
    exact (h.isLorentzForm hxV).emTensor_nonneg (h.psi_timelike hxV) (hφc x hxV).1
      (hφc x hxV).2 hlam _ _
  have := cutoff_nonneg ((τ - ψ x) / ε)
  have := cutoff_nonneg ((ψ' x - c) / ε)
  have := cutoffDeriv_nonneg ((φ x - s) / ε)
  simp only [fluxG_def]
  positivity

/-- The volume estimate on `L ∩ {φ > s}`, with the sup norm of `dw`. -/
theorem volume_estimate_superlevel {φ : E n → ℝ} (hφ : ContDiffOn ℝ ∞ φ V)
    (hφc : ∀ x ∈ V, bil (g x)⁻¹ (d φ x) (d φ x) ≤ 0 ∧ bil (g x)⁻¹ (d φ x) (d ψ x) ≤ 0) :
    ∃ C σ₀ : ℝ, ∀ σ ≥ σ₀, ∀ (s : ℝ) (U : Set (E n)) (w : E n → ℝ), IsOpen U →
      lens V ψ ψ' τ c ⊆ U → ContDiffOn ℝ 2 w U →
      (∀ x ∈ lens V ψ ψ' τ c, ψ x = τ → s ≤ φ x → w x = 0 ∧ d w x = 0) →
      σ ^ 2 * ∫ x in lens V ψ ψ' τ c ∩ {x | s < φ x},
          Real.exp (2 * σ * ψ x) * (‖d w x‖ ^ 2 + σ ^ 2 * w x ^ 2) ≤
        C * ∫ x in lens V ψ ψ' τ c ∩ {x | s < φ x}, Real.exp (2 * σ * ψ x) * box g w x ^ 2 := by
  obtain ⟨ε₀, hε₀, a, ha, b, hb, σ₀, hσ₀, hstep⟩ := h.step1
  refine ⟨b / a, σ₀, fun σ hσ s U w hU hLU hw hvan => ?_⟩
  have hσ0 : 0 < σ := lt_of_lt_of_le hσ₀ hσ
  have hLV := h.lens_subset (ψ := ψ) (ψ' := ψ') (τ := τ) (c := c)
  have hLUV : lens V ψ ψ' τ c ⊆ U ∩ V := subset_inter hLU hLV
  set lam := ε₀ ^ 2 * σ ^ 2 with hlam_def
  have hlam : 0 ≤ lam := by positivity
  have hψc : ContinuousOn ψ (lens V ψ ψ' τ c) := h.smooth_ψ.continuousOn.mono hLV
  have hE : ContinuousOn (fun x => Real.exp (2 * σ * ψ x)) (lens V ψ ψ' τ c) :=
    Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hψc)
  have hF1 : ContinuousOn (fun x => Real.exp (2 * σ * ψ x) * (‖d w x‖ ^ 2 + σ ^ 2 * w x ^ 2))
      (lens V ψ ψ' τ c) :=
    hE.mul ((((h.continuousOn_norm_d hU hw).mono hLU).pow 2).add
      (continuousOn_const.mul ((hw.continuousOn.mono hLU).pow 2)))
  have hF2 : ContinuousOn (fun x => Real.exp (2 * σ * ψ x) * box g w x ^ 2) (lens V ψ ψ' τ c) :=
    hE.mul (((h.continuousOn_box hU hw).mono hLUV).pow 2)
  set N : E n → ℝ := fun x => a * σ * (Real.exp (2 * σ * ψ x) * (‖d w x‖ ^ 2 + σ ^ 2 * w x ^ 2))
  set B : E n → ℝ := fun x => b / σ * (Real.exp (2 * σ * ψ x) * box g w x ^ 2)
  have hN : ContinuousOn N (lens V ψ ψ' τ c) := continuousOn_const.mul hF1
  have hB : ContinuousOn B (lens V ψ ψ' τ c) := continuousOn_const.mul hF2
  have hB0 : ∀ x ∈ lens V ψ ψ' τ c, 0 ≤ B x := fun x _ => by
    simp only [B]; have := Real.exp_pos (2 * σ * ψ x); positivity
  have hdiv : ∀ x ∈ lens V ψ ψ' τ c, ∑ j, d (current g ψ w σ lam j) x j ≤ B x - N x := by
    intro x hx
    have := hstep σ hσ w x hx (hw.contDiffAt (hU.mem_nhds (hLU hx)))
    simp only [B, N]
    linarith
  -- the inequality for each cut-off
  have hcut : ∀ k : ℕ, ∫ x in lens V ψ ψ' τ c, chi ψ ψ' φ τ c s (1 / ((k : ℝ) + 1)) x * N x ≤
      (∫ x in lens V ψ ψ' τ c, fluxA g ψ ψ' φ w τ c σ lam s (1 / ((k : ℝ) + 1)) x) +
        ∫ x in lens V ψ ψ' τ c ∩ {x | s < φ x}, B x := by
    intro k
    have hε : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have h1 := h.core_eps hφ hU hLU hw hlam hN hB hB0 hdiv s hε
    have h2 := h.integral_fluxG_nonneg hφc (w := w) (σ := σ) hlam s _ hε
    linarith
  have hlim := h.tendsto_integral_chi hφ.continuousOn hN s
  have hmain : ∫ x in lens V ψ ψ' τ c ∩ {x | s < φ x}, N x ≤
      ∫ x in lens V ψ ψ' τ c ∩ {x | s < φ x}, B x := by
    refine le_of_forall_pos_le_add fun η hη => ?_
    obtain ⟨ε₁, hε₁, hA⟩ := h.exists_fluxA_small hφ hU hLU hw hlam s hvan hη
    obtain ⟨k₀, hk₀⟩ := exists_nat_gt (1 / ε₁)
    refine le_of_tendsto hlim (eventually_atTop.2 ⟨k₀, fun k hk => ?_⟩)
    have hεk : 1 / ((k : ℝ) + 1) ≤ ε₁ := by
      rw [div_le_iff₀ (by positivity)]
      have : (k₀ : ℝ) ≤ k := by exact_mod_cast hk
      rw [div_lt_iff₀ hε₁] at hk₀
      nlinarith
    have := hA _ (by positivity) hεk
    have := hcut k
    linarith
  simp only [N, B] at hmain
  rw [integral_const_mul, integral_const_mul] at hmain
  have e : σ ^ 2 * ∫ x in lens V ψ ψ' τ c ∩ {x | s < φ x},
      Real.exp (2 * σ * ψ x) * (‖d w x‖ ^ 2 + σ ^ 2 * w x ^ 2) =
      σ / a * (a * σ * ∫ x in lens V ψ ψ' τ c ∩ {x | s < φ x},
        Real.exp (2 * σ * ψ x) * (‖d w x‖ ^ 2 + σ ^ 2 * w x ^ 2)) := by
    field_simp
  have e2 : b / a * ∫ x in lens V ψ ψ' τ c ∩ {x | s < φ x}, Real.exp (2 * σ * ψ x) *
      box g w x ^ 2 = σ / a * (b / σ * ∫ x in lens V ψ ψ' τ c ∩ {x | s < φ x},
        Real.exp (2 * σ * ψ x) * box g w x ^ 2) := by
    field_simp
  rw [e, e2]
  exact mul_le_mul_of_nonneg_left hmain (by positivity)

end EnergySetting

end

end LorentzianCalderon
