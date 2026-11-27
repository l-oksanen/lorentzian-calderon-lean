module

public import LorentzianCalderon.Local.Energy.Surface
public import LorentzianCalderon.Local.Energy.Volume

public section

/-!
# The weighted energy inequality

Lemma `lem_energy` of the blueprint, in a form without surface measures. In the setting
`EnergySetting V g Y ψ ψ' τ c` (a smooth Lorentzian metric `g` on the open set `V`, time oriented
by `Y`, temporal functions `ψ, ψ'` on `V`, and the compact lens
`L = {x ∈ V | ψ x ≤ τ, c ≤ ψ' x}`), with Lebesgue measure and the Euclidean norm of `dw`:

* `energy_volume` (eq. `eq_energy2`): for `w` of class `C²` near `L` with `w = 0`, `dw = 0` on
  `{ψ = τ} ∩ L`,
  `σ² ∫_L e^{2σψ} (|dw|² + σ² w²) ≤ C ∫_L e^{2σψ} |□_g w|²`;
* `energy_superlevel` (eq. `eq_energy` without the surface term): for `φ` eikonal of future type
  and `w = 0`, `dw = 0` on `{ψ = τ} ∩ {φ ≥ s} ∩ L`, the same on `L ∩ {φ > s}`;
* `energy_surface` (in `Energy/Surface.lean`; the surface term of `eq_energy` integrated over
  `s ∈ [s₁, s₂]`): for a family `w s` jointly `C²` in `(s, x)`, with `Z = -grad φ`,
  `σ ∫_{L ∩ {s₁ ≤ φ ≤ s₂}} e^{2σψ} ((Z w_{φ(x)})² + σ² w_{φ(x)}²) ≤
    C ∫_{s₁}^{s₂} ∫_{L ∩ {φ > s}} e^{2σψ} |□_g w_s|²`.

The proof follows the blueprint: the divergence identity for the current
`J = e^{2σψ} T(·, X)`, `X = -grad ψ`, of the energy-momentum tensor with mass term `λ = ε₀² σ²`
(`Energy/Identity.lean`, `Energy/Step1.lean`), the positivity of the fluxes
(`Energy/Algebra.lean`), and the integration against the cut-offs `χ_ε`
(`Energy/Core.lean`, `Energy/Limits.lean`).
-/

namespace LorentzianCalderon

noncomputable section
open Set MeasureTheory
open scoped ContDiff

variable {n : ℕ}

/-- The Euclidean norm of a covector is bounded by `n + 1` times the sup norm of its
components. -/
theorem norm_fderiv_le (w : E n → ℝ) (x : E n) : ‖fderiv ℝ w x‖ ≤ (n + 1) * ‖d w x‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  have hv := (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).sum_repr v
  simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] at hv
  conv_lhs => rw [← hv]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  calc ‖∑ i, v i * fderiv ℝ w x (EuclideanSpace.single i 1)‖
      ≤ ∑ i, ‖v i * fderiv ℝ w x (EuclideanSpace.single i 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin (n + 1), ‖d w x‖ * ‖v‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_mul, mul_comm, ← d_def]
        exact mul_le_mul (norm_le_pi_norm (d w x) i) (PiLp.norm_apply_le v i) (norm_nonneg _)
          (norm_nonneg _)
    _ = (n + 1) * ‖d w x‖ * ‖v‖ := by simp; ring

namespace EnergySetting

variable {V : Set (E n)} {g : MatrixField n} {Y : E n → E n} {ψ ψ' : E n → ℝ} {τ c : ℝ}
  (h : EnergySetting V g Y ψ ψ' τ c)
include h

/-- Passing from the sup norm of the components of `dw` to the Euclidean norm of `dw`. -/
theorem volume_estimate_fderiv {φ : E n → ℝ} (hφ : ContDiffOn ℝ ∞ φ V)
    (hφc : ∀ x ∈ V, bil (g x)⁻¹ (d φ x) (d φ x) ≤ 0 ∧ bil (g x)⁻¹ (d φ x) (d ψ x) ≤ 0) :
    ∃ C σ₀ : ℝ, ∀ σ ≥ σ₀, ∀ (s : ℝ) (U : Set (E n)) (w : E n → ℝ), IsOpen U →
      lens V ψ ψ' τ c ⊆ U → ContDiffOn ℝ 2 w U →
      (∀ x ∈ lens V ψ ψ' τ c, ψ x = τ → s ≤ φ x → w x = 0 ∧ fderiv ℝ w x = 0) →
      σ ^ 2 * ∫ x in lens V ψ ψ' τ c ∩ {x | s < φ x},
          Real.exp (2 * σ * ψ x) * (‖fderiv ℝ w x‖ ^ 2 + σ ^ 2 * w x ^ 2) ≤
        C * ∫ x in lens V ψ ψ' τ c ∩ {x | s < φ x}, Real.exp (2 * σ * ψ x) * box g w x ^ 2 := by
  obtain ⟨C, σ₀, hC⟩ := h.volume_estimate_superlevel hφ hφc
  refine ⟨((n : ℝ) + 1) ^ 2 * C, σ₀, fun σ hσ s U w hU hLU hw hvan => ?_⟩
  have hmain := hC σ hσ s U w hU hLU hw fun x hx h1 h2 => by
    obtain ⟨h3, h4⟩ := hvan x hx h1 h2
    exact ⟨h3, d_eq_zero_of_fderiv h4⟩
  have hLV := h.lens_subset (ψ := ψ) (ψ' := ψ') (τ := τ) (c := c)
  set S := lens V ψ ψ' τ c ∩ {x | s < φ x}
  have hSm : MeasurableSet S := h.measurableSet_lens_superlevel hφ.continuousOn s
  have hψc : ContinuousOn ψ (lens V ψ ψ' τ c) := h.smooth_ψ.continuousOn.mono hLV
  have hE : ContinuousOn (fun x => Real.exp (2 * σ * ψ x)) (lens V ψ ψ' τ c) :=
    Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hψc)
  have hw0 : ContinuousOn w (lens V ψ ψ' τ c) := hw.continuousOn.mono hLU
  have hfd : ContinuousOn (fun x => ‖fderiv ℝ w x‖) (lens V ψ ψ' τ c) :=
    ((hw.continuousOn_fderiv_of_isOpen hU one_le_two).norm).mono hLU
  have hdd : ContinuousOn (fun x => ‖d w x‖) (lens V ψ ψ' τ c) :=
    (h.continuousOn_norm_d hU hw).mono hLU
  have hi1 : IntegrableOn (fun x => Real.exp (2 * σ * ψ x) *
      (‖fderiv ℝ w x‖ ^ 2 + σ ^ 2 * w x ^ 2)) S :=
    ((hE.mul ((hfd.pow 2).add (continuousOn_const.mul (hw0.pow 2)))).integrableOn_compact
      h.isCompact).mono_set inter_subset_left
  have hi2 : IntegrableOn (fun x => Real.exp (2 * σ * ψ x) *
      (‖d w x‖ ^ 2 + σ ^ 2 * w x ^ 2)) S :=
    ((hE.mul ((hdd.pow 2).add (continuousOn_const.mul (hw0.pow 2)))).integrableOn_compact
      h.isCompact).mono_set inter_subset_left
  have hle : ∫ x in S, Real.exp (2 * σ * ψ x) * (‖fderiv ℝ w x‖ ^ 2 + σ ^ 2 * w x ^ 2) ≤
      ((n : ℝ) + 1) ^ 2 * ∫ x in S, Real.exp (2 * σ * ψ x) * (‖d w x‖ ^ 2 + σ ^ 2 * w x ^ 2) := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on hi1 (hi2.const_mul _) hSm fun x _ => ?_
    have h1 : ‖fderiv ℝ w x‖ ^ 2 ≤ ((n : ℝ) + 1) ^ 2 * ‖d w x‖ ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le w x) 2
    have h2 : σ ^ 2 * w x ^ 2 ≤ ((n : ℝ) + 1) ^ 2 * (σ ^ 2 * w x ^ 2) :=
      le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by linarith [n.cast_nonneg (α := ℝ)]))
    have := Real.exp_pos (2 * σ * ψ x)
    calc Real.exp (2 * σ * ψ x) * (‖fderiv ℝ w x‖ ^ 2 + σ ^ 2 * w x ^ 2)
        ≤ Real.exp (2 * σ * ψ x) * (((n : ℝ) + 1) ^ 2 * ‖d w x‖ ^ 2 +
          ((n : ℝ) + 1) ^ 2 * (σ ^ 2 * w x ^ 2)) := by gcongr
      _ = ((n : ℝ) + 1) ^ 2 * (Real.exp (2 * σ * ψ x) * (‖d w x‖ ^ 2 + σ ^ 2 * w x ^ 2)) := by
        ring
  calc σ ^ 2 * ∫ x in S, Real.exp (2 * σ * ψ x) * (‖fderiv ℝ w x‖ ^ 2 + σ ^ 2 * w x ^ 2)
      ≤ σ ^ 2 * (((n : ℝ) + 1) ^ 2 *
          ∫ x in S, Real.exp (2 * σ * ψ x) * (‖d w x‖ ^ 2 + σ ^ 2 * w x ^ 2)) := by gcongr
    _ = ((n : ℝ) + 1) ^ 2 * (σ ^ 2 *
          ∫ x in S, Real.exp (2 * σ * ψ x) * (‖d w x‖ ^ 2 + σ ^ 2 * w x ^ 2)) := by ring
    _ ≤ ((n : ℝ) + 1) ^ 2 * (C * ∫ x in S, Real.exp (2 * σ * ψ x) * box g w x ^ 2) := by gcongr
    _ = ((n : ℝ) + 1) ^ 2 * C * ∫ x in S, Real.exp (2 * σ * ψ x) * box g w x ^ 2 := by ring

/-- **Weighted energy inequality, volume form** (blueprint `eq_energy2`): for `w` of class `C²`
on a neighbourhood `U` of the lens `L` with `w = 0` and `dw = 0` on `{ψ = τ} ∩ L`,
`σ² ∫_L e^{2σψ} (|dw|² + σ² w²) ≤ C ∫_L e^{2σψ} |□_g w|²` for `σ ≥ σ₀`. -/
theorem energy_volume :
    ∃ C σ₀ : ℝ, ∀ σ ≥ σ₀, ∀ (U : Set (E n)) (w : E n → ℝ), IsOpen U →
      lens V ψ ψ' τ c ⊆ U → ContDiffOn ℝ 2 w U →
      (∀ x ∈ lens V ψ ψ' τ c, ψ x = τ → w x = 0 ∧ fderiv ℝ w x = 0) →
      σ ^ 2 * ∫ x in lens V ψ ψ' τ c,
          Real.exp (2 * σ * ψ x) * (‖fderiv ℝ w x‖ ^ 2 + σ ^ 2 * w x ^ 2) ≤
        C * ∫ x in lens V ψ ψ' τ c, Real.exp (2 * σ * ψ x) * box g w x ^ 2 := by
  have hd0 : ∀ x, d (fun _ : E n => (0 : ℝ)) x = 0 := fun x => by ext i; simp [d_def]
  obtain ⟨C, σ₀, hC⟩ := h.volume_estimate_fderiv (φ := fun _ => 0) contDiffOn_const
    fun x _ => by simp [hd0]
  refine ⟨C, σ₀, fun σ hσ U w hU hLU hw hvan => ?_⟩
  have hS : lens V ψ ψ' τ c ∩ {x | (-1 : ℝ) < (fun _ : E n => (0 : ℝ)) x} = lens V ψ ψ' τ c := by
    ext x; simp
  have := hC σ hσ (-1) U w hU hLU hw fun x hx h1 _ => hvan x hx h1
  rwa [hS] at this

/-- **Weighted energy inequality on `{φ > s}`** (blueprint `eq_energy` without the surface
term): for `φ` eikonal of future type and `w` of class `C²` on a neighbourhood `U` of the lens
`L` with `w = 0` and `dw = 0` on `{ψ = τ} ∩ {φ ≥ s} ∩ L`,
`σ² ∫_{L ∩ {φ > s}} e^{2σψ} (|dw|² + σ² w²) ≤ C ∫_{L ∩ {φ > s}} e^{2σψ} |□_g w|²` for
`σ ≥ σ₀`, with `C` and `σ₀` independent of `s`. -/
theorem energy_superlevel {φ : E n → ℝ} (hφ : IsEikonal V g Y φ) :
    ∃ C σ₀ : ℝ, ∀ σ ≥ σ₀, ∀ (s : ℝ) (U : Set (E n)) (w : E n → ℝ), IsOpen U →
      lens V ψ ψ' τ c ⊆ U → ContDiffOn ℝ 2 w U →
      (∀ x ∈ lens V ψ ψ' τ c, ψ x = τ → s ≤ φ x → w x = 0 ∧ fderiv ℝ w x = 0) →
      σ ^ 2 * ∫ x in lens V ψ ψ' τ c ∩ {x | s < φ x},
          Real.exp (2 * σ * ψ x) * (‖fderiv ℝ w x‖ ^ 2 + σ ^ 2 * w x ^ 2) ≤
        C * ∫ x in lens V ψ ψ' τ c ∩ {x | s < φ x}, Real.exp (2 * σ * ψ x) * box g w x ^ 2 :=
  h.volume_estimate_fderiv hφ.smooth fun x hx =>
    ⟨by rw [← coform_eq_bil, hφ.null x hx], (h.eikonal_psi_neg hφ hx).le⟩

end EnergySetting

end

end LorentzianCalderon
