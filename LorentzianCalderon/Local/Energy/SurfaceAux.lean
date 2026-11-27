module

public import LorentzianCalderon.Local.Energy.Family
public import LorentzianCalderon.Local.Energy.Mollifier
public import LorentzianCalderon.Local.Energy.Volume

public section

/-!
# Auxiliary results for the integrated surface estimate

The flux `A_ε` is small uniformly in the parameter `s`, the flux density through the null
hypersurfaces `{φ = s}` controls `(Zw)² + σ² w²`, and `Zw = -G(dφ, dw)`.
-/

namespace LorentzianCalderon

noncomputable section
open Set MeasureTheory Filter Topology Matrix
open scoped ContDiff

variable {n : ℕ}

/-- `Zw` for `Z = -grad φ`, up to sign. -/
theorem fderiv_grad_eq {g : MatrixField n} {x : E n} (hx : IsLorentzian (g x))
    (u φ : E n → ℝ) : fderiv ℝ u x (grad g φ x) = bil (g x)⁻¹ (d φ x) (d u x) := by
  have hv := (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).sum_repr (grad g φ x)
  simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] at hv
  conv_lhs => rw [← hv]
  rw [map_sum, bil_symm hx.inv_symm, bil_apply]
  simp only [map_smul, smul_eq_mul, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (grad g φ x) i = ((g x)⁻¹ *ᵥ d φ x) i := by
    rw [← ofLp_grad]
  rw [this, mul_comm, d_def]

theorem sq_fderiv_neg_grad {g : MatrixField n} {x : E n} (hx : IsLorentzian (g x))
    (u φ : E n → ℝ) :
    fderiv ℝ u x (-grad g φ x) ^ 2 = bil (g x)⁻¹ (d φ x) (d u x) ^ 2 := by
  rw [map_neg, fderiv_grad_eq hx, neg_sq]

namespace EnergySetting

variable {V : Set (E n)} {g : MatrixField n} {Y : E n → E n} {ψ ψ' : E n → ℝ} {τ c : ℝ}
  (h : EnergySetting V g Y ψ ψ' τ c)
include h

/-- `A_ε → 0` uniformly in `s ∈ [s₁, s₂]`. -/
theorem exists_fluxA_small_uniform {φ : E n → ℝ} (hφ : ContDiffOn ℝ ∞ φ V) {U : Set (E n)}
    (hU : IsOpen U) (hLU : lens V ψ ψ' τ c ⊆ U) {w : ℝ → E n → ℝ}
    (hW : ContDiffOn ℝ 2 (fun p : ℝ × E n => w p.1 p.2) (univ ×ˢ U)) {σ lam : ℝ}
    (hlam : 0 ≤ lam) (s₁ s₂ : ℝ)
    (hvan : ∀ s ∈ Icc s₁ s₂, ∀ x ∈ lens V ψ ψ' τ c, ψ x = τ → s ≤ φ x →
      w s x = 0 ∧ d (w s) x = 0)
    {η : ℝ} (hη : 0 < η) :
    ∃ ε₁ > 0, ∀ ε, 0 < ε → ε ≤ ε₁ → ∀ s ∈ Icc s₁ s₂,
      ∫ x in lens V ψ ψ' τ c, fluxA g ψ ψ' φ (w s) τ c σ lam s ε x ≤ η := by
  have hLV := h.lens_subset (ψ := ψ) (ψ' := ψ') (τ := τ) (c := c)
  obtain ⟨Cs, hCs⟩ := slab_volume_le h.isOpen h.isCompact hLV (h.smooth_ψ.of_le (by simp))
    fun x hx => h.d_ne_zero_psi hx
  set Cs' := max Cs 1
  have hCs' : 0 < Cs' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set K : Set (ℝ × E n) := (Icc s₁ s₂ ×ˢ lens V ψ ψ' τ c) ∩ {p | p.1 ≤ φ p.2}
  have hKsub : K ⊆ univ ×ˢ (U ∩ V) := fun p hp => ⟨mem_univ _, hLU hp.1.2, hLV hp.1.2⟩
  have hφc : ContinuousOn (fun p : ℝ × E n => φ p.2 - p.1) (Icc s₁ s₂ ×ˢ lens V ψ ψ' τ c) :=
    ((hφ.continuousOn.mono hLV).comp continuousOn_snd fun p hp => hp.2).sub continuousOn_fst
  have hK : IsCompact K := by
    refine (isCompact_Icc.prod h.isCompact).of_isClosed_subset ?_ inter_subset_left
    have := hφc.preimage_isClosed_of_isClosed (isCompact_Icc.prod h.isCompact).isClosed
      (isClosed_Ici (a := (0 : ℝ)))
    convert this using 1
    ext p; simp [K, and_comm]
  have hwT := (h.family_continuousOn_wT hU hW σ lam h.smooth_ψ).mono hKsub
  obtain ⟨ε₁, hε₁, hsmall⟩ := exists_small_near_top hK hwT
    ((h.smooth_ψ.continuousOn.comp continuousOn_snd fun p hp => hLV hp.1.2).mono subset_rfl)
    (fun p hp => (mem_lens.1 hp.1.2).2.1)
    (fun p hp hψp => by
      obtain ⟨h1, h2⟩ := hvan p.1 hp.1.1 p.2 hp.1.2 hψp hp.2
      exact wT_eq_zero h1 h2)
    (δ := η / (2 * Cs')) (by positivity)
  refine ⟨ε₁, hε₁, fun ε hε hεε₁ s hs => ?_⟩
  have hb := h.integral_fluxA_le hφ hU hLU (family_contDiffOn hW s) hlam s hε
    (δ := η / (2 * Cs')) (by positivity)
    fun x hx hφx hψx => (hsmall (s, x) ⟨⟨hs, hx⟩, hφx⟩ (by show τ - ε₁ ≤ ψ x; linarith)).le
  have hvol : volume.real (lens V ψ ψ' τ c ∩ ψ ⁻¹' Icc (τ - ε) τ) ≤ Cs' * ε := by
    have := hCs (τ - ε) ε hε
    rw [sub_add_cancel] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hε.le)
  calc _ ≤ 2 * (η / (2 * Cs')) / ε * volume.real (lens V ψ ψ' τ c ∩ ψ ⁻¹' Icc (τ - ε) τ) := hb
    _ ≤ 2 * (η / (2 * Cs')) / ε * (Cs' * ε) := by gcongr
    _ = η := by field_simp

/-- The flux density through the null hypersurfaces controls `G(dφ, dw)² + σ² w²`. -/
theorem exists_null_flux_lower {φ : E n → ℝ} (hφ : IsEikonal V g Y φ) {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ c₃ > 0, ∀ (σ : ℝ) (u : E n → ℝ), ∀ x ∈ lens V ψ ψ' τ c,
      c₃ * (Real.exp (2 * σ * ψ x) * (bil (g x)⁻¹ (d φ x) (d u x) ^ 2 + σ ^ 2 * u x ^ 2)) ≤
        wT g ψ u σ (ε₀ ^ 2 * σ ^ 2) φ x := by
  have hLV := h.lens_subset (ψ := ψ) (ψ' := ψ') (τ := τ) (c := c)
  have hbilc : ∀ {α β : E n → ℝ}, ContDiffOn ℝ ∞ α V → ContDiffOn ℝ ∞ β V →
      ContinuousOn (fun x => bil (g x)⁻¹ (d α x) (d β x)) (lens V ψ ψ' τ c) := by
    intro α β hα hβ
    have hc : Continuous fun q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ × (Fin (n + 1) → ℝ) ×
        (Fin (n + 1) → ℝ) => bil q.1 q.2.1 q.2.2 := by
      simp only [bil, Matrix.toLinearMap₂'_apply, smul_eq_mul]
      fun_prop
    have := hc.comp_continuousOn (h.continuousOn_ginv.prodMk
      ((continuousOn_d h.isOpen (hα.of_le (by simp))).prodMk
        (continuousOn_d h.isOpen (hβ.of_le (by simp)))))
    exact this.mono hLV
  -- `m = -G(dψ, dψ)`, `k = -G(dφ, dψ)` and `ρ` are bounded above and below on the lens
  obtain ⟨m₀, hm₀, hm⟩ := exists_pos_le_of_continuousOn
    (f := fun x => -bil (g x)⁻¹ (d ψ x) (d ψ x)) h.isCompact
    (hbilc h.smooth_ψ h.smooth_ψ).neg fun x hx => by
      have := h.psi_timelike (hLV hx); linarith
  obtain ⟨k₀, hk₀, hk⟩ := exists_pos_le_of_continuousOn
    (f := fun x => -bil (g x)⁻¹ (d φ x) (d ψ x)) h.isCompact
    (hbilc hφ.smooth h.smooth_ψ).neg fun x hx => by
      have := h.eikonal_psi_neg hφ (hLV hx); linarith
  obtain ⟨k₁, hk₁, hk'⟩ := exists_abs_le_of_continuousOn
    (f := fun x => -bil (g x)⁻¹ (d φ x) (d ψ x)) h.isCompact
    (hbilc hφ.smooth h.smooth_ψ).neg
  obtain ⟨ρ₀, hρ₀, ρ₁, hρ₁, hρ⟩ := h.exists_vol_bounds
  set c₃ := ρ₀ * min (m₀ / (2 * k₁)) (k₀ * ε₀ ^ 2 / 2)
  refine ⟨c₃, by positivity, fun σ u x hx => ?_⟩
  have hxV := hLV hx
  set B := bil (g x)⁻¹
  have hβ : B (d ψ x) (d ψ x) < 0 := h.psi_timelike hxV
  have hα : B (d φ x) (d φ x) = 0 := by rw [← coform_eq_bil]; exact hφ.null x hxV
  have hαβ : B (d φ x) (d ψ x) < 0 := h.eikonal_psi_neg hφ hxV
  have hT := (h.isLorentzForm hxV).emTensor_null_ge hβ hα hαβ (ε₀ ^ 2 * σ ^ 2) (u x) (d u x)
  have hmx : m₀ ≤ -B (d ψ x) (d ψ x) := hm x hx
  have hkx : k₀ ≤ -B (d φ x) (d ψ x) := hk x hx
  have hkx' : -B (d φ x) (d ψ x) ≤ k₁ := (le_abs_self _).trans (hk' x hx)
  have hkpos : 0 < -B (d φ x) (d ψ x) := by linarith
  set q := B (d φ x) (d u x) ^ 2
  have hq : 0 ≤ q := sq_nonneg _
  have h1 : m₀ / (2 * k₁) ≤ -B (d ψ x) (d ψ x) / (2 * -B (d φ x) (d ψ x)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have h2 : k₀ * ε₀ ^ 2 / 2 * (σ ^ 2 * u x ^ 2) ≤
      -B (d φ x) (d ψ x) / 2 * (ε₀ ^ 2 * σ ^ 2 * u x ^ 2) := by
    have : 0 ≤ ε₀ ^ 2 * σ ^ 2 * u x ^ 2 := by positivity
    nlinarith
  have hmin1 := min_le_left (m₀ / (2 * k₁)) (k₀ * ε₀ ^ 2 / 2)
  have hmin2 := min_le_right (m₀ / (2 * k₁)) (k₀ * ε₀ ^ 2 / 2)
  have hT' : min (m₀ / (2 * k₁)) (k₀ * ε₀ ^ 2 / 2) * (q + σ ^ 2 * u x ^ 2) ≤
      emTensor B (ε₀ ^ 2 * σ ^ 2) (u x) (d u x) (d φ x) (d ψ x) := by
    have e1 : min (m₀ / (2 * k₁)) (k₀ * ε₀ ^ 2 / 2) * q ≤
        -B (d ψ x) (d ψ x) / (2 * -B (d φ x) (d ψ x)) * q :=
      mul_le_mul_of_nonneg_right (hmin1.trans h1) hq
    have e2 : min (m₀ / (2 * k₁)) (k₀ * ε₀ ^ 2 / 2) * (σ ^ 2 * u x ^ 2) ≤
        k₀ * ε₀ ^ 2 / 2 * (σ ^ 2 * u x ^ 2) :=
      mul_le_mul_of_nonneg_right hmin2 (by positivity)
    have e3 : ε₀ ^ 2 * σ ^ 2 * u x ^ 2 = (ε₀ ^ 2 * σ ^ 2) * u x ^ 2 := rfl
    nlinarith
  have hE := Real.exp_pos (2 * σ * ψ x)
  have hvol := hρ x hx |>.1
  have hmin0 : 0 ≤ min (m₀ / (2 * k₁)) (k₀ * ε₀ ^ 2 / 2) := by positivity
  simp only [wT_def]
  calc c₃ * (Real.exp (2 * σ * ψ x) * (q + σ ^ 2 * u x ^ 2))
      = Real.exp (2 * σ * ψ x) * ρ₀ *
          (min (m₀ / (2 * k₁)) (k₀ * ε₀ ^ 2 / 2) * (q + σ ^ 2 * u x ^ 2)) := by ring
    _ ≤ Real.exp (2 * σ * ψ x) * vol g x *
          emTensor B (ε₀ ^ 2 * σ ^ 2) (u x) (d u x) (d φ x) (d ψ x) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hvol hE.le) hT' (by positivity)
          (mul_pos hE (vol_pos (h.det_ne_zero hxV))).le

end EnergySetting

end

end LorentzianCalderon
