module

public import LorentzianCalderon.Local.Energy.Cutoffs

public section

/-!
# Step 3: integration of the divergence identity against the cut-off

`∫_L χ_ε div P = A_ε - B_ε - G_ε` (with the signs of this file: all three are integrals of
nonnegative functions when `w` is real), where the flux terms come from the derivatives of the
three factors of `χ_ε`.
-/

namespace LorentzianCalderon

noncomputable section
open Set MeasureTheory Filter Topology
open scoped ContDiff

variable {n : ℕ}

theorem continuous_emTensor_bil :
    Continuous fun q : (Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ × ℝ × ℝ) ×
        (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) =>
      emTensor (bil q.1.1) q.1.2.1 q.1.2.2 q.2.1 q.2.2.1 q.2.2.2 := by
  simp only [emTensor_def, bil, Matrix.toLinearMap₂'_apply, smul_eq_mul]
  fun_prop

theorem ContinuousOn.emTensor_bil {Z : Type*} [TopologicalSpace Z] {S : Set Z}
    {A : Z → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam w₀ : Z → ℝ}
    {ξ α β : Z → Fin (n + 1) → ℝ} (hA : ContinuousOn A S) (hl : ContinuousOn lam S)
    (hw : ContinuousOn w₀ S) (hξ : ContinuousOn ξ S) (hα : ContinuousOn α S)
    (hβ : ContinuousOn β S) :
    ContinuousOn (fun z => emTensor (bil (A z)) (lam z) (w₀ z) (ξ z) (α z) (β z)) S := by
  have := continuous_emTensor_bil.comp_continuousOn
    ((hA.prodMk (hl.prodMk hw)).prodMk (hξ.prodMk (hα.prodMk hβ)))
  exact this

/-- `e^{2σψ} √|det g| T(α, dψ)`, the flux density through the level sets of `α`. -/
def wT (g : MatrixField n) (ψ w : E n → ℝ) (σ lam : ℝ) (α : E n → ℝ) (x : E n) : ℝ :=
  Real.exp (2 * σ * ψ x) * vol g x * emTensor (bil (g x)⁻¹) lam (w x) (d w x) (d α x) (d ψ x)

theorem wT_def (g : MatrixField n) (ψ w : E n → ℝ) (σ lam : ℝ) (α : E n → ℝ) (x : E n) :
    wT g ψ w σ lam α x =
      Real.exp (2 * σ * ψ x) * vol g x * emTensor (bil (g x)⁻¹) lam (w x) (d w x) (d α x)
        (d ψ x) := by
  rfl

namespace EnergySetting

variable {V : Set (E n)} {g : MatrixField n} {Y : E n → E n} {ψ ψ' : E n → ℝ} {τ c : ℝ}
  (h : EnergySetting V g Y ψ ψ' τ c)
include h

theorem continuousOn_ginv : ContinuousOn (fun x => (g x)⁻¹) V :=
  continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => h.continuousOn_inv i j

theorem contDiffOn_current {U : Set (E n)} (hU : IsOpen U) {w : E n → ℝ}
    (hw : ContDiffOn ℝ 2 w U) (σ lam : ℝ) (j : Fin (n + 1)) :
    ContDiffOn ℝ 1 (current g ψ w σ lam j) (U ∩ V) := by
  have hρ : ContDiffOn ℝ 1 (vol g) (U ∩ V) :=
    (h.contDiffOn_vol.of_le (by simp)).mono inter_subset_right
  have hG : ∀ c e, ContDiffOn ℝ 1 (ginv g c e) (U ∩ V) := fun c e => by
    rw [ginv_eq]
    exact ((h.contDiffOn_inv c e).of_le (by simp)).mono inter_subset_right
  have hξ : ∀ k, ContDiffOn ℝ 1 (dc w k) (U ∩ V) := fun k => by
    rw [dc_eq]
    exact (contDiffOn_d_of_le hU hw (by norm_num) k).mono inter_subset_left
  have hX : ∀ b, ContDiffOn ℝ 1 (Current.X (ginv g) (dc ψ) b) (U ∩ V) := fun b =>
    ((h.contDiffOn_X b).of_le (by simp)).mono inter_subset_right
  have hψ1 : ContDiffOn ℝ 1 ψ (U ∩ V) := (h.smooth_ψ.of_le (by simp)).mono inter_subset_right
  have hw1 : ContDiffOn ℝ 1 w (U ∩ V) := (hw.of_le one_le_two).mono inter_subset_left
  show ContDiffOn ℝ 1 (fun y => current g ψ w σ lam j y) (U ∩ V)
  simp only [current_def, Current.P_def, Current.flux_def, Current.Xw_def, Current.q_def,
    Current.qf_def]
  fun_prop

theorem continuousOn_div_current {U : Set (E n)} (hU : IsOpen U) {w : E n → ℝ}
    (hw : ContDiffOn ℝ 2 w U) (σ lam : ℝ) :
    ContinuousOn (fun x => ∑ j, d (current g ψ w σ lam j) x j) (U ∩ V) :=
  continuousOn_finsetSum _ fun j _ =>
    continuousOn_d_of_contDiffOn (hU.inter h.isOpen) (h.contDiffOn_current hU hw σ lam j) j

theorem continuousOn_box {U : Set (E n)} (hU : IsOpen U) {w : E n → ℝ}
    (hw : ContDiffOn ℝ 2 w U) : ContinuousOn (box g w) (U ∩ V) := by
  have hρ : ContDiffOn ℝ 1 (vol g) (U ∩ V) :=
    (h.contDiffOn_vol.of_le (by simp)).mono inter_subset_right
  have hG : ∀ c e, ContDiffOn ℝ 1 (ginv g c e) (U ∩ V) := fun c e => by
    rw [ginv_eq]
    exact ((h.contDiffOn_inv c e).of_le (by simp)).mono inter_subset_right
  have hξ : ∀ k, ContDiffOn ℝ 1 (dc w k) (U ∩ V) := fun k => by
    rw [dc_eq]
    exact (contDiffOn_d_of_le hU hw (by norm_num) k).mono inter_subset_left
  have hfl : ∀ j, ContDiffOn ℝ 1 (Current.flux (vol g) (ginv g) (dc w) j) (U ∩ V) := by
    intro j
    show ContDiffOn ℝ 1 (fun y => Current.flux (vol g) (ginv g) (dc w) j y) (U ∩ V)
    simp only [Current.flux_def]
    fun_prop
  have hsum : ContinuousOn (fun x => ∑ j, d (Current.flux (vol g) (ginv g) (dc w) j) x j)
      (U ∩ V) := continuousOn_finsetSum _ fun j _ =>
    continuousOn_d_of_contDiffOn (hU.inter h.isOpen) (hfl j) j
  have hinv : ContinuousOn (fun x => (vol g x)⁻¹) (U ∩ V) :=
    hρ.continuousOn.inv₀ fun x hx => (vol_pos (h.det_ne_zero hx.2)).ne'
  refine (hinv.neg.mul hsum).congr fun x _ => ?_
  simp only [Pi.mul_apply, Pi.neg_apply, flux_vol_ginv_dc, vol_def]
  exact box_eq_flux g w x

theorem continuousOn_wT {U : Set (E n)} (hU : IsOpen U) {w : E n → ℝ}
    (hw : ContDiffOn ℝ 2 w U) (σ lam : ℝ) {α : E n → ℝ} (hα : ContDiffOn ℝ ∞ α V) :
    ContinuousOn (wT g ψ w σ lam α) (U ∩ V) := by
  have hψc : ContinuousOn ψ (U ∩ V) := h.smooth_ψ.continuousOn.mono inter_subset_right
  refine (((Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hψc)).mul
    (h.contDiffOn_vol.continuousOn.mono inter_subset_right)).mul ?_)
  refine ContinuousOn.emTensor_bil (h.continuousOn_ginv.mono inter_subset_right)
    continuousOn_const (hw.continuousOn.mono inter_subset_left)
    ((continuousOn_d hU (hw.of_le one_le_two)).mono inter_subset_left)
    ((continuousOn_d h.isOpen (hα.of_le (by simp))).mono inter_subset_right)
    ((continuousOn_d h.isOpen (h.smooth_ψ.of_le (by simp))).mono
      inter_subset_right)

/-- The pointwise identity behind Step 3. -/
theorem sum_d_chi_mul_current {φ : E n → ℝ} (hφ : ContDiffOn ℝ ∞ φ V) {x : E n} (hx : x ∈ V)
    (w : E n → ℝ) (σ lam s ε : ℝ) :
    ∑ j, d (chi ψ ψ' φ τ c s ε) x j * current g ψ w σ lam j x =
      cutoffDeriv ((τ - ψ x) / ε) * (1 / ε) * cutoff ((ψ' x - c) / ε) *
          cutoff ((φ x - s) / ε) * wT g ψ w σ lam ψ x -
        cutoff ((τ - ψ x) / ε) * (cutoffDeriv ((ψ' x - c) / ε) * (1 / ε)) *
          cutoff ((φ x - s) / ε) * wT g ψ w σ lam ψ' x -
        cutoff ((τ - ψ x) / ε) * cutoff ((ψ' x - c) / ε) *
          (cutoffDeriv ((φ x - s) / ε) * (1 / ε)) * wT g ψ w σ lam φ x := by
  have hVx : V ∈ 𝓝 x := h.isOpen.mem_nhds hx
  have hdiff : ∀ {u : E n → ℝ}, ContDiffOn ℝ ∞ u V → DifferentiableAt ℝ u x := fun hu =>
    (hu.contDiffAt hVx).differentiableAt (by simp)
  set c1 := cutoff ((τ - ψ x) / ε)
  set c2 := cutoff ((ψ' x - c) / ε)
  set c3 := cutoff ((φ x - s) / ε)
  set D1 := cutoffDeriv ((τ - ψ x) / ε)
  set D2 := cutoffDeriv ((ψ' x - c) / ε)
  set D3 := cutoffDeriv ((φ x - s) / ε)
  have hsplit : ∑ j, d (chi ψ ψ' φ τ c s ε) x j * current g ψ w σ lam j x =
      (D1 * (-1 / ε) * c2 * c3) * ∑ j, d ψ x j * current g ψ w σ lam j x +
        (c1 * (D2 * (1 / ε)) * c3) * ∑ j, d ψ' x j * current g ψ w σ lam j x +
        (c1 * c2 * (D3 * (1 / ε))) * ∑ j, d φ x j * current g ψ w σ lam j x := by
    simp only [d_chi (hdiff h.smooth_ψ) (hdiff h.smooth_ψ') (hdiff hφ), Finset.mul_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hL := h.lorentzian x hx
  rw [hsplit, sum_mul_current hL, sum_mul_current hL, sum_mul_current hL]
  simp only [wT]
  ring

end EnergySetting

end

end LorentzianCalderon
