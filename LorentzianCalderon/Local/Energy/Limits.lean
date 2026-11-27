module

public import LorentzianCalderon.Local.Energy.Core

public section

/-!
# Limits as `ε → 0`

The flux `A_ε` near `{ψ = τ}` tends to zero when `w` and `dw` vanish there, and
`∫_L χ_ε N → ∫_{L ∩ {φ > s}} N`, the level sets `{ψ = τ}`, `{ψ' = c}` being null.
-/

namespace LorentzianCalderon

noncomputable section
open Set MeasureTheory Filter Topology
open scoped ContDiff

variable {n : ℕ}

theorem cutoffDeriv_div_eq_zero {r ε : ℝ} (hε : 0 < ε) (hr : ε ≤ r) : cutoffDeriv (r / ε) = 0 :=
  cutoffDeriv_of_one_le ((one_le_div hε).2 hr)

theorem cutoff_div_eq_one {r ε : ℝ} (hε : 0 < ε) (hr : ε ≤ r) : cutoff (r / ε) = 1 :=
  cutoff_of_one_le ((one_le_div hε).2 hr)

/-- `H(r / ε_k) → 1_{r > 0}` along `ε_k = 1 / (k + 1)`. -/
theorem tendsto_cutoff_div (r : ℝ) :
    Tendsto (fun k : ℕ => cutoff (r / (1 / ((k : ℝ) + 1)))) atTop
      (𝓝 (if 0 < r then 1 else 0)) := by
  split_ifs with hr
  · obtain ⟨k₀, hk₀⟩ := exists_nat_gt (1 / r)
    refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨k₀, fun k hk => ?_⟩)
    symm
    apply cutoff_div_eq_one (by positivity)
    rw [div_le_iff₀ (by positivity)]
    have : (k₀ : ℝ) ≤ k := by exact_mod_cast hk
    rw [div_lt_iff₀ hr] at hk₀
    nlinarith
  · exact tendsto_const_nhds.congr fun k =>
      (cutoff_div_of_nonpos (by positivity) (not_lt.1 hr)).symm

namespace EnergySetting

variable {V : Set (E n)} {g : MatrixField n} {Y : E n → E n} {ψ ψ' : E n → ℝ} {τ c : ℝ}
  (h : EnergySetting V g Y ψ ψ' τ c)
include h

theorem d_ne_zero_psi {x : E n} (hx : x ∈ V) : d ψ x ≠ 0 :=
  h.d_ne_zero_of_timelike hx (h.psi_timelike hx)

theorem d_ne_zero_psi' {x : E n} (hx : x ∈ V) : d ψ' x ≠ 0 :=
  h.d_ne_zero_of_timelike hx (h.psi'_timelike hx)

theorem measurableSet_lens : MeasurableSet (lens V ψ ψ' τ c) := h.isCompact.measurableSet

/-- The bound for `A_ε` by the size of the flux density near `{ψ = τ}`. -/
theorem integral_fluxA_le {φ : E n → ℝ} (hφ : ContDiffOn ℝ ∞ φ V) {U : Set (E n)}
    (hU : IsOpen U) (hLU : lens V ψ ψ' τ c ⊆ U) {w : E n → ℝ} (hw : ContDiffOn ℝ 2 w U)
    {σ lam : ℝ} (hlam : 0 ≤ lam) (s : ℝ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ)
    (hsmall : ∀ x ∈ lens V ψ ψ' τ c, s ≤ φ x → τ - ε ≤ ψ x → wT g ψ w σ lam ψ x ≤ δ) :
    ∫ x in lens V ψ ψ' τ c, fluxA g ψ ψ' φ w τ c σ lam s ε x ≤
      2 * δ / ε * volume.real (lens V ψ ψ' τ c ∩ ψ ⁻¹' Icc (τ - ε) τ) := by
  have hLV := h.lens_subset (ψ := ψ) (ψ' := ψ') (τ := τ) (c := c)
  have hLm := h.measurableSet_lens
  set S := lens V ψ ψ' τ c ∩ ψ ⁻¹' Icc (τ - ε) τ
  have hSm : MeasurableSet S :=
    ((h.smooth_ψ.continuousOn.mono hLV).preimage_isClosed_of_isClosed h.isCompact.isClosed
      isClosed_Icc).measurableSet
  have hint : IntegrableOn (fun x => fluxA g ψ ψ' φ w τ c σ lam s ε x) (lens V ψ ψ' τ c) := by
    have hwT := (h.continuousOn_wT hU hw σ lam h.smooth_ψ).mono (subset_inter hLU hLV)
    have hψc : ContinuousOn ψ (lens V ψ ψ' τ c) := h.smooth_ψ.continuousOn.mono hLV
    have hψ'c : ContinuousOn ψ' (lens V ψ ψ' τ c) := h.smooth_ψ'.continuousOn.mono hLV
    have hφc : ContinuousOn φ (lens V ψ ψ' τ c) := hφ.continuousOn.mono hLV
    refine ContinuousOn.integrableOn_compact h.isCompact ?_
    simp only [fluxA_def]
    exact ((((continuous_cutoffDeriv.comp_continuousOn ((continuousOn_const.sub hψc).div_const
      _)).mul continuousOn_const).mul (continuous_cutoff.comp_continuousOn
        ((hψ'c.sub continuousOn_const).div_const _))).mul (continuous_cutoff.comp_continuousOn
          ((hφc.sub continuousOn_const).div_const _))).mul hwT
  calc ∫ x in lens V ψ ψ' τ c, fluxA g ψ ψ' φ w τ c σ lam s ε x
      ≤ ∫ x in lens V ψ ψ' τ c, S.indicator (fun _ => 2 * δ / ε) x := by
        refine setIntegral_mono_on hint ((integrableOn_const (by
          exact (h.isCompact.measure_lt_top).ne)).indicator hSm) hLm fun x hx => ?_
        have hx0 := h.wT_psi_nonneg (hLV hx) (w := w) (σ := σ) hlam
        have hc2 := cutoff_nonneg ((ψ' x - c) / ε)
        have hc2' := cutoff_le_one ((ψ' x - c) / ε)
        have hc3 := cutoff_nonneg ((φ x - s) / ε)
        have hc3' := cutoff_le_one ((φ x - s) / ε)
        have hD := cutoffDeriv_nonneg ((τ - ψ x) / ε)
        have hD' := cutoffDeriv_le ((τ - ψ x) / ε)
        have hrhs : 0 ≤ S.indicator (fun _ => 2 * δ / ε) x :=
          indicator_nonneg (fun _ _ => by positivity) _
        simp only [fluxA_def]
        by_cases hφs : φ x ≤ s
        · rw [cutoff_div_of_nonpos (r := φ x - s) hε (by linarith)]; simpa using hrhs
        by_cases hψs : ψ x < τ - ε
        · rw [cutoffDeriv_div_eq_zero hε (by linarith)]; simpa using hrhs
        push Not at hφs hψs
        rw [indicator_of_mem (show x ∈ S from ⟨hx, hψs, (mem_lens.1 hx).2.1⟩)]
        have hwδ := hsmall x hx hφs.le hψs
        have h1 : cutoffDeriv ((τ - ψ x) / ε) * (1 / ε) * cutoff ((ψ' x - c) / ε) *
            cutoff ((φ x - s) / ε) ≤ 2 * (1 / ε) * 1 * 1 := by gcongr
        calc cutoffDeriv ((τ - ψ x) / ε) * (1 / ε) * cutoff ((ψ' x - c) / ε) *
              cutoff ((φ x - s) / ε) * wT g ψ w σ lam ψ x
            ≤ 2 * (1 / ε) * 1 * 1 * δ := by
              apply mul_le_mul h1 hwδ hx0 (by positivity)
          _ = 2 * δ / ε := by ring
    _ = 2 * δ / ε * volume.real S := by
        rw [integral_indicator_const _ hSm, measureReal_restrict_apply hSm, smul_eq_mul,
          inter_eq_left.2 inter_subset_left, mul_comm]

omit h in
/-- The flux density through `{ψ = τ}` vanishes where `w` and `dw` vanish. -/
theorem wT_eq_zero {w : E n → ℝ} {σ lam : ℝ} {α : E n → ℝ} {x : E n} (hw : w x = 0)
    (hdw : d w x = 0) : wT g ψ w σ lam α x = 0 := by
  simp [wT_def, emTensor_def, hw, hdw]

/-- `A_ε → 0`: for every `η > 0`, `A_ε ≤ η` for small `ε`, uniformly in the data described by
a compact set of pairs `(s, x)`. -/
theorem exists_fluxA_small {φ : E n → ℝ} (hφ : ContDiffOn ℝ ∞ φ V) {U : Set (E n)}
    (hU : IsOpen U) (hLU : lens V ψ ψ' τ c ⊆ U) {w : E n → ℝ} (hw : ContDiffOn ℝ 2 w U)
    {σ lam : ℝ} (hlam : 0 ≤ lam) (s : ℝ)
    (hvanish : ∀ x ∈ lens V ψ ψ' τ c, ψ x = τ → s ≤ φ x → w x = 0 ∧ d w x = 0) {η : ℝ}
    (hη : 0 < η) :
    ∃ ε₁ > 0, ∀ ε, 0 < ε → ε ≤ ε₁ →
      ∫ x in lens V ψ ψ' τ c, fluxA g ψ ψ' φ w τ c σ lam s ε x ≤ η := by
  have hLV := h.lens_subset (ψ := ψ) (ψ' := ψ') (τ := τ) (c := c)
  obtain ⟨Cs, hCs⟩ := slab_volume_le h.isOpen h.isCompact hLV (h.smooth_ψ.of_le (by simp))
    fun x hx => h.d_ne_zero_psi hx
  set Cs' := max Cs 1
  have hCs' : 0 < Cs' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set K := lens V ψ ψ' τ c ∩ φ ⁻¹' Ici s
  have hK : IsCompact K := h.isCompact.of_isClosed_subset
    ((hφ.continuousOn.mono hLV).preimage_isClosed_of_isClosed h.isCompact.isClosed isClosed_Ici)
    inter_subset_left
  have hwT := (h.continuousOn_wT hU hw σ lam h.smooth_ψ).mono (subset_inter hLU hLV)
  obtain ⟨ε₁, hε₁, hsmall⟩ := exists_small_near_top hK (hwT.mono inter_subset_left)
    ((h.smooth_ψ.continuousOn.mono hLV).mono inter_subset_left) (fun x hx => (mem_lens.1 hx.1).2.1)
    (fun x hx hψx => by
      obtain ⟨h1, h2⟩ := hvanish x hx.1 hψx hx.2
      exact wT_eq_zero h1 h2)
    (δ := η / (2 * Cs')) (by positivity)
  refine ⟨ε₁, hε₁, fun ε hε hεε₁ => ?_⟩
  have hb := h.integral_fluxA_le hφ hU hLU hw hlam s hε (δ := η / (2 * Cs')) (by positivity)
    fun x hx hφx hψx => (hsmall x ⟨hx, hφx⟩ (by linarith)).le
  have hvol : volume.real (lens V ψ ψ' τ c ∩ ψ ⁻¹' Icc (τ - ε) τ) ≤ Cs' * ε := by
    have := hCs (τ - ε) ε hε
    rw [sub_add_cancel] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hε.le)
  calc _ ≤ 2 * (η / (2 * Cs')) / ε * volume.real (lens V ψ ψ' τ c ∩ ψ ⁻¹' Icc (τ - ε) τ) := hb
    _ ≤ 2 * (η / (2 * Cs')) / ε * (Cs' * ε) := by gcongr
    _ = η := by field_simp

/-- The level set `{ψ = τ}` and `{ψ' = c}` are null in the lens. -/
theorem ae_lens_ne :
    ∀ᵐ x ∂(volume.restrict (lens V ψ ψ' τ c)), ψ x ≠ τ ∧ ψ' x ≠ c := by
  have hLV := h.lens_subset (ψ := ψ) (ψ' := ψ') (τ := τ) (c := c)
  have h1 := volume_levelSet_eq_zero h.isOpen hLV (h.smooth_ψ.of_le (by simp))
    (fun x hx => h.d_ne_zero_psi hx) τ
  have h2 := volume_levelSet_eq_zero h.isOpen hLV (h.smooth_ψ'.of_le (by simp))
    (fun x hx => h.d_ne_zero_psi' hx) c
  rw [ae_iff, Measure.restrict_apply' h.measurableSet_lens]
  refine measure_mono_null (fun x hx => ?_) (measure_union_null h1 h2)
  simp only [mem_inter_iff, mem_ofPred_eq, not_and_or, not_not] at hx
  rcases hx.1 with h' | h'
  · exact Or.inl ⟨hx.2, h'⟩
  · exact Or.inr ⟨hx.2, h'⟩

/-- `∫_L χ_ε N → ∫_{L ∩ {φ > s}} N` along `ε_k = 1 / (k + 1)`. -/
theorem tendsto_integral_chi {φ : E n → ℝ} (hφ : ContinuousOn φ V) {N : E n → ℝ}
    (hN : ContinuousOn N (lens V ψ ψ' τ c)) (s : ℝ) :
    Tendsto (fun k : ℕ => ∫ x in lens V ψ ψ' τ c,
        chi ψ ψ' φ τ c s (1 / ((k : ℝ) + 1)) x * N x) atTop
      (𝓝 (∫ x in lens V ψ ψ' τ c ∩ {x | s < φ x}, N x)) := by
  have hLV := h.lens_subset (ψ := ψ) (ψ' := ψ') (τ := τ) (c := c)
  have hLm := h.measurableSet_lens
  rw [← h.setIntegral_indicator_superlevel hφ]
  refine tendsto_integral_of_dominated_convergence (fun x => |N x|) (fun k => ?_)
    (hN.abs.integrableOn_compact h.isCompact) (fun k => ?_) ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ hLm
    have hψc : ContinuousOn ψ (lens V ψ ψ' τ c) := h.smooth_ψ.continuousOn.mono hLV
    have hψ'c : ContinuousOn ψ' (lens V ψ ψ' τ c) := h.smooth_ψ'.continuousOn.mono hLV
    have hφc : ContinuousOn φ (lens V ψ ψ' τ c) := hφ.mono hLV
    simp only [chi_def]
    exact (((continuous_cutoff.comp_continuousOn ((continuousOn_const.sub hψc).div_const _)).mul
      (continuous_cutoff.comp_continuousOn ((hψ'c.sub continuousOn_const).div_const _))).mul
      (continuous_cutoff.comp_continuousOn ((hφc.sub continuousOn_const).div_const _))).mul hN
  · refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (by
      rw [abs_of_nonneg (chi_nonneg _ _ _ _ _ _ _ _)]; exact chi_le_one _ _ _ _ _ _ _ _)
  · filter_upwards [h.ae_lens_ne, ae_restrict_mem hLm] with x hx hxL
    have hlim := ((tendsto_cutoff_div (τ - ψ x)).mul (tendsto_cutoff_div (ψ' x - c))).mul
      (tendsto_cutoff_div (φ x - s))
    have hτ : 0 < τ - ψ x := sub_pos.2 (lt_of_le_of_ne (mem_lens.1 hxL).2.1 hx.1)
    have hc : 0 < ψ' x - c := sub_pos.2 (lt_of_le_of_ne (mem_lens.1 hxL).2.2 (Ne.symm hx.2))
    simp only [hτ, hc, ↓reduceIte, one_mul] at hlim
    have hlim' := hlim.mul_const (N x)
    simp only [chi_def]
    by_cases hs : s < φ x
    · rw [indicator_of_mem (show x ∈ V ∩ φ ⁻¹' Ioi s from ⟨hLV hxL, hs⟩)]
      simp only [sub_pos.2 hs, ↓reduceIte, one_mul] at hlim'
      exact hlim'
    · rw [indicator_of_notMem (fun h' => hs h'.2)]
      simp only [show ¬ 0 < φ x - s by linarith, ↓reduceIte, zero_mul] at hlim'
      exact hlim'

end EnergySetting

end

end LorentzianCalderon
