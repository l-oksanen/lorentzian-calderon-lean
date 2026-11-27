module

public import LorentzianCalderon.Local.Energy.Step3

public section

/-!
# The integrated inequality for a fixed cut-off

For `χ_ε` as in Step 3 and a pointwise bound `div P ≤ B - N` on the lens,
`G_ε + ∫_L χ_ε N ≤ A_ε + ∫_{L ∩ {φ > s}} B`, where `G_ε ≥ 0` is the flux through the level sets of
`φ` and `A_ε` the one through the level sets of `ψ` near `{ψ = τ}`; the flux `B_ε ≥ 0` through
the level sets of `ψ'` has been dropped.
-/

namespace LorentzianCalderon

noncomputable section
open Set MeasureTheory Filter Topology
open scoped ContDiff

variable {n : ℕ}

attribute [local fun_prop] continuous_cutoff continuous_cutoffDeriv

/-- The density of the flux `A_ε` through the level sets of `ψ`. -/
def fluxA (g : MatrixField n) (ψ ψ' φ w : E n → ℝ) (τ c σ lam s ε : ℝ) (x : E n) : ℝ :=
  cutoffDeriv ((τ - ψ x) / ε) * (1 / ε) * cutoff ((ψ' x - c) / ε) * cutoff ((φ x - s) / ε) *
    wT g ψ w σ lam ψ x

theorem fluxA_def (g : MatrixField n) (ψ ψ' φ w : E n → ℝ) (τ c σ lam s ε : ℝ) (x : E n) :
    fluxA g ψ ψ' φ w τ c σ lam s ε x =
      cutoffDeriv ((τ - ψ x) / ε) * (1 / ε) * cutoff ((ψ' x - c) / ε) * cutoff ((φ x - s) / ε) *
        wT g ψ w σ lam ψ x := by rfl

/-- The density of the flux `G_ε` through the level sets of `φ`. -/
def fluxG (g : MatrixField n) (ψ ψ' φ w : E n → ℝ) (τ c σ lam s ε : ℝ) (x : E n) : ℝ :=
  cutoff ((τ - ψ x) / ε) * cutoff ((ψ' x - c) / ε) * (cutoffDeriv ((φ x - s) / ε) * (1 / ε)) *
    wT g ψ w σ lam φ x

theorem fluxG_def (g : MatrixField n) (ψ ψ' φ w : E n → ℝ) (τ c σ lam s ε : ℝ) (x : E n) :
    fluxG g ψ ψ' φ w τ c σ lam s ε x =
      cutoff ((τ - ψ x) / ε) * cutoff ((ψ' x - c) / ε) * (cutoffDeriv ((φ x - s) / ε) * (1 / ε)) *
        wT g ψ w σ lam φ x := by rfl

namespace EnergySetting

variable {V : Set (E n)} {g : MatrixField n} {Y : E n → E n} {ψ ψ' : E n → ℝ} {τ c : ℝ}
  (h : EnergySetting V g Y ψ ψ' τ c)
include h

theorem isOpen_superlevel {φ : E n → ℝ} (hφ : ContinuousOn φ V) (s : ℝ) :
    IsOpen (V ∩ φ ⁻¹' Ioi s) :=
  hφ.isOpen_inter_preimage h.isOpen isOpen_Ioi

theorem lens_inter_superlevel {φ : E n → ℝ} (s : ℝ) :
    lens V ψ ψ' τ c ∩ (V ∩ φ ⁻¹' Ioi s) = lens V ψ ψ' τ c ∩ {x | s < φ x} := by
  ext x
  simp only [mem_inter_iff, mem_preimage, mem_Ioi, mem_ofPred_eq]
  exact ⟨fun hx => ⟨hx.1, hx.2.2⟩, fun hx => ⟨hx.1, h.lens_subset hx.1, hx.2⟩⟩

theorem measurableSet_lens_superlevel {φ : E n → ℝ} (hφ : ContinuousOn φ V) (s : ℝ) :
    MeasurableSet (lens V ψ ψ' τ c ∩ {x | s < φ x}) := by
  rw [← h.lens_inter_superlevel]
  exact h.isCompact.measurableSet.inter (h.isOpen_superlevel hφ s).measurableSet

theorem setIntegral_indicator_superlevel {φ : E n → ℝ} (hφ : ContinuousOn φ V) (s : ℝ)
    (f : E n → ℝ) :
    ∫ x in lens V ψ ψ' τ c, (V ∩ φ ⁻¹' Ioi s).indicator f x =
      ∫ x in lens V ψ ψ' τ c ∩ {x | s < φ x}, f x := by
  rw [setIntegral_indicator (h.isOpen_superlevel hφ s).measurableSet, h.lens_inter_superlevel]

theorem wT_psi'_nonneg {x : E n} (hx : x ∈ V) {w : E n → ℝ} {σ lam : ℝ} (hlam : 0 ≤ lam) :
    0 ≤ wT g ψ w σ lam ψ' x := by
  simp only [wT_def]
  refine mul_nonneg (mul_nonneg (Real.exp_pos _).le (vol_pos (h.det_ne_zero hx)).le) ?_
  exact (h.isLorentzForm hx).emTensor_nonneg (h.psi_timelike hx) (h.psi'_timelike hx).le
    (h.psi'_psi_neg hx).le hlam _ _

theorem wT_psi_nonneg {x : E n} (hx : x ∈ V) {w : E n → ℝ} {σ lam : ℝ} (hlam : 0 ≤ lam) :
    0 ≤ wT g ψ w σ lam ψ x := by
  simp only [wT_def]
  refine mul_nonneg (mul_nonneg (Real.exp_pos _).le (vol_pos (h.det_ne_zero hx)).le) ?_
  exact (h.isLorentzForm hx).emTensor_nonneg (h.psi_timelike hx) (h.psi_timelike hx).le
    (h.psi_timelike hx).le hlam _ _

/-- The density of the flux `B_ε` through the level sets of `ψ'`. -/
def fluxB (g : MatrixField n) (ψ ψ' φ w : E n → ℝ) (τ c σ lam s ε : ℝ) (x : E n) : ℝ :=
  cutoff ((τ - ψ x) / ε) * (cutoffDeriv ((ψ' x - c) / ε) * (1 / ε)) * cutoff ((φ x - s) / ε) *
    wT g ψ w σ lam ψ' x

/-- The integrated inequality for a fixed cut-off. -/
theorem core_eps {φ : E n → ℝ} (hφ : ContDiffOn ℝ ∞ φ V) {U : Set (E n)} (hU : IsOpen U)
    (hLU : lens V ψ ψ' τ c ⊆ U) {w : E n → ℝ} (hw : ContDiffOn ℝ 2 w U) {σ lam : ℝ}
    (hlam : 0 ≤ lam) {N B : E n → ℝ} (hN : ContinuousOn N (lens V ψ ψ' τ c))
    (hB : ContinuousOn B (lens V ψ ψ' τ c)) (hB0 : ∀ x ∈ lens V ψ ψ' τ c, 0 ≤ B x)
    (hdiv : ∀ x ∈ lens V ψ ψ' τ c, ∑ j, d (current g ψ w σ lam j) x j ≤ B x - N x)
    (s : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (∫ x in lens V ψ ψ' τ c, fluxG g ψ ψ' φ w τ c σ lam s ε x) +
        ∫ x in lens V ψ ψ' τ c, chi ψ ψ' φ τ c s ε x * N x ≤
      (∫ x in lens V ψ ψ' τ c, fluxA g ψ ψ' φ w τ c σ lam s ε x) +
        ∫ x in lens V ψ ψ' τ c ∩ {x | s < φ x}, B x := by
  have hLV : lens V ψ ψ' τ c ⊆ V := h.lens_subset
  have hLUV : lens V ψ ψ' τ c ⊆ U ∩ V := subset_inter hLU hLV
  have hLc : IsCompact (lens V ψ ψ' τ c) := h.isCompact
  have hLm : MeasurableSet (lens V ψ ψ' τ c) := hLc.measurableSet
  have hψc : ContinuousOn ψ (lens V ψ ψ' τ c) := h.smooth_ψ.continuousOn.mono hLV
  have hψ'c : ContinuousOn ψ' (lens V ψ ψ' τ c) := h.smooth_ψ'.continuousOn.mono hLV
  have hφc : ContinuousOn φ (lens V ψ ψ' τ c) := hφ.continuousOn.mono hLV
  have hwTψ : ContinuousOn (wT g ψ w σ lam ψ) (lens V ψ ψ' τ c) :=
    (h.continuousOn_wT hU hw σ lam h.smooth_ψ).mono hLUV
  have hwTψ' : ContinuousOn (wT g ψ w σ lam ψ') (lens V ψ ψ' τ c) :=
    (h.continuousOn_wT hU hw σ lam h.smooth_ψ').mono hLUV
  have hwTφ : ContinuousOn (wT g ψ w σ lam φ) (lens V ψ ψ' τ c) :=
    (h.continuousOn_wT hU hw σ lam hφ).mono hLUV
  have hdivc : ContinuousOn (fun x => ∑ j, d (current g ψ w σ lam j) x j) (lens V ψ ψ' τ c) :=
    (h.continuousOn_div_current hU hw σ lam).mono hLUV
  have hchic : ContinuousOn (fun x => chi ψ ψ' φ τ c s ε x) (lens V ψ ψ' τ c) := by
    simp only [chi_def]; fun_prop
  have hac : ContinuousOn (fun x => fluxA g ψ ψ' φ w τ c σ lam s ε x) (lens V ψ ψ' τ c) := by
    simp only [fluxA]; fun_prop
  have hgc : ContinuousOn (fun x => fluxG g ψ ψ' φ w τ c σ lam s ε x) (lens V ψ ψ' τ c) := by
    simp only [fluxG]; fun_prop
  have hbc : ContinuousOn (fun x => fluxB g ψ ψ' φ w τ c σ lam s ε x) (lens V ψ ψ' τ c) := by
    simp only [fluxB]; fun_prop
  have hint : ∀ {f : E n → ℝ}, ContinuousOn f (lens V ψ ψ' τ c) →
      IntegrableOn f (lens V ψ ψ' τ c) := fun hf => hf.integrableOn_compact hLc
  -- the divergence theorem
  have key := integral_div_eq_zero (hU.inter h.isOpen) hLc hLUV
    (f := chi ψ ψ' φ τ c s ε) (V := fun j => current g ψ w σ lam j)
    ((contDiffOn_chi (h.smooth_ψ.of_le (by simp)) (h.smooth_ψ'.of_le (by simp))
      (hφ.of_le (by simp)) τ c s ε).mono inter_subset_right)
    (fun j => h.contDiffOn_current hU hw σ lam j)
    (fun j x hx => by
      rw [chi_eq_zero_of_not_mem hε hx.1.2 hx.2, zero_mul])
  have hpt : ∀ x ∈ lens V ψ ψ' τ c, ∑ j, (d (chi ψ ψ' φ τ c s ε) x j * current g ψ w σ lam j x +
      chi ψ ψ' φ τ c s ε x * d (current g ψ w σ lam j) x j) =
      fluxA g ψ ψ' φ w τ c σ lam s ε x - fluxB g ψ ψ' φ w τ c σ lam s ε x -
        fluxG g ψ ψ' φ w τ c σ lam s ε x +
        chi ψ ψ' φ τ c s ε x * ∑ j, d (current g ψ w σ lam j) x j := by
    intro x hx
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, h.sum_d_chi_mul_current hφ (hLV hx)]
    rfl
  rw [setIntegral_congr_fun hLm hpt] at key
  rw [integral_add (f := fun x => fluxA g ψ ψ' φ w τ c σ lam s ε x -
      fluxB g ψ ψ' φ w τ c σ lam s ε x - fluxG g ψ ψ' φ w τ c σ lam s ε x)
      (g := fun x => chi ψ ψ' φ τ c s ε x * ∑ j, d (current g ψ w σ lam j) x j)
      (((hint hac).sub (hint hbc)).sub (hint hgc)) (hint (hchic.mul hdivc)),
    integral_sub (f := fun x => fluxA g ψ ψ' φ w τ c σ lam s ε x -
      fluxB g ψ ψ' φ w τ c σ lam s ε x) (g := fun x => fluxG g ψ ψ' φ w τ c σ lam s ε x)
      ((hint hac).sub (hint hbc)) (hint hgc),
    integral_sub (f := fun x => fluxA g ψ ψ' φ w τ c σ lam s ε x)
      (g := fun x => fluxB g ψ ψ' φ w τ c σ lam s ε x) (hint hac) (hint hbc)] at key
  -- the signs
  have hb0 : 0 ≤ ∫ x in lens V ψ ψ' τ c, fluxB g ψ ψ' φ w τ c σ lam s ε x := by
    refine setIntegral_nonneg hLm fun x hx => ?_
    have := cutoffDeriv_nonneg ((ψ' x - c) / ε)
    have := h.wT_psi'_nonneg (hLV hx) (w := w) (σ := σ) hlam
    have := cutoff_nonneg ((τ - ψ x) / ε)
    have := cutoff_nonneg ((φ x - s) / ε)
    simp only [fluxB]
    positivity
  have hdivle : ∫ x in lens V ψ ψ' τ c,
        chi ψ ψ' φ τ c s ε x * ∑ j, d (current g ψ w σ lam j) x j ≤
      ∫ x in lens V ψ ψ' τ c, (chi ψ ψ' φ τ c s ε x * B x - chi ψ ψ' φ τ c s ε x * N x) := by
    refine setIntegral_mono_on (hint (hchic.mul hdivc))
      ((hint (hchic.mul hB)).sub (hint (hchic.mul hN))) hLm fun x hx => ?_
    rw [← mul_sub]
    exact mul_le_mul_of_nonneg_left (hdiv x hx) (chi_nonneg _ _ _ _ _ _ _ _)
  rw [integral_sub (f := fun x => chi ψ ψ' φ τ c s ε x * B x)
    (g := fun x => chi ψ ψ' φ τ c s ε x * N x) (hint (hchic.mul hB)) (hint (hchic.mul hN))]
    at hdivle
  have hχB : ∫ x in lens V ψ ψ' τ c, chi ψ ψ' φ τ c s ε x * B x ≤
      ∫ x in lens V ψ ψ' τ c ∩ {x | s < φ x}, B x := by
    rw [← h.setIntegral_indicator_superlevel hφ.continuousOn]
    have hmeas := (h.isOpen_superlevel hφ.continuousOn s).measurableSet
    refine setIntegral_mono_on (hint (hchic.mul hB)) ?_ hLm fun x hx => ?_
    · exact ((hint hB).indicator hmeas)
    · by_cases hs : s < φ x
      · rw [indicator_of_mem (show x ∈ V ∩ φ ⁻¹' Ioi s from ⟨hLV hx, hs⟩)]
        calc chi ψ ψ' φ τ c s ε x * B x ≤ 1 * B x :=
              mul_le_mul_of_nonneg_right (chi_le_one _ _ _ _ _ _ _ _) (hB0 x hx)
          _ = B x := one_mul _
      · rw [indicator_of_notMem (fun h' => hs h'.2), chi_eq_zero_of_le hε (not_lt.1 hs),
          zero_mul]
  linarith

end EnergySetting

end

end LorentzianCalderon
