module

public import LorentzianCalderon.Green.BoxCalculus
public import LorentzianCalderon.Local.BoxCalculus
public import LorentzianCalderon.Facts.Vocabulary
public import LorentzianCalderon.Local.Energy.Cutoff

public section

/-!
# The weak jump identity

For an eikonal phase `φ` and a function `u` whose transport coefficient
`2 Z u + u □_g φ` (with `Z u = -g(dφ, du)`) vanishes on the front `{φ = s}`,
`∫ 1_{φ > s} u □_g h ρ = ∫ 1_{φ > s} (□_g u) h ρ` for test functions `h`, where
`ρ = √|det g|`. This is one direction of the jump formula of `lem_calculus`, stated
without measures on the level set.

The proof uses the cut-offs `H_ε(φ - s)` with `H_ε(r) = H(r / ε)` for the smooth transition
function `H`. The pointwise identity
`□_g (u k(φ)) = k(φ) □_g u + k'(φ) (2 Z u + u □_g φ) - k''(φ) u g(dφ, dφ)`
and Green's formula give the identity for `H_ε`; in the limit `ε → 0` the term with `H_ε'`
vanishes, because the transport coefficient times `h ρ` is bounded by a multiple of `|φ - s|`.
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Finset Filter MeasureTheory Set

variable {n : ℕ}

section Pointwise

theorem d_comp_real {k : ℝ → ℝ} {φ : E n → ℝ} {x : E n} (hk : DifferentiableAt ℝ k (φ x))
    (hφ : DifferentiableAt ℝ φ x) (j : Fin (n + 1)) :
    d (fun y => k (φ y)) x j = deriv k (φ x) * d φ x j := by
  have := (hk.hasDerivAt.comp_hasFDerivAt x hφ.hasFDerivAt).fderiv
  simp only [d_def]
  rw [show (fun y => k (φ y)) = k ∘ φ from rfl, this]
  simp

theorem d2_mul_comp {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k) {u φ : E n → ℝ} {x : E n}
    (hu : ContDiffAt ℝ 2 u x) (hφ : ContDiffAt ℝ 2 φ x) (i j : Fin (n + 1)) :
    d2 (fun y => u y * k (φ y)) x i j =
      d2 u x i j * k (φ x) + d u x j * (deriv k (φ x) * d φ x i) +
        (d u x i * (deriv k (φ x) * d φ x j) +
          u x * (deriv (deriv k) (φ x) * d φ x i * d φ x j + deriv k (φ x) * d2 φ x i j)) := by
  have hk1 : Differentiable ℝ k := hk.differentiable (by simp)
  have hk2 : Differentiable ℝ (deriv k) :=
    (contDiff_infty_iff_deriv.1 hk).2.differentiable (by simp)
  have hev : (fun y => d (fun z => u z * k (φ z)) y j) =ᶠ[𝓝 x]
      fun y => d u y j * k (φ y) + u y * (deriv k (φ y) * d φ y j) := by
    filter_upwards [hu.eventually (by simp), hφ.eventually (by simp)] with y huy hφy
    have hud := huy.differentiableAt (by simp)
    have hφd := hφy.differentiableAt (by simp)
    rw [d_mul (v := fun z => k (φ z)) hud ((hk1 _).comp y hφd), d_comp_real (hk1 _) hφd]
  have hud := hu.differentiableAt (by simp)
  have hφd := hφ.differentiableAt (by simp)
  have hdu := differentiableAt_d hu j
  have hdφ := differentiableAt_d hφ j
  have hkφ : DifferentiableAt ℝ (fun y => k (φ y)) x := (hk1 _).comp x hφd
  have hk'φ : DifferentiableAt ℝ (fun y => deriv k (φ y)) x := (hk2 _).comp x hφd
  rw [d2_def, d_congr hev, d_add (u := fun y => d u y j * k (φ y))
    (v := fun y => u y * (deriv k (φ y) * d φ y j)) (hdu.mul hkφ) (hud.mul (hk'φ.mul hdφ)),
    d_mul hdu hkφ, d_mul (v := fun y => deriv k (φ y) * d φ y j) hud (hk'φ.mul hdφ),
    d_mul hk'φ hdφ, d_comp_real (hk1 _) hφd,
    d_comp_real (hk2 _) hφd]
  simp only [d2_def]

theorem box_mul_comp_algebra {ι : Type*} [Fintype ι] (G U P : ι → ι → ℝ)
    (hG : ∀ i j, G i j = G j i) (a f b : ι → ℝ) (u k k1 k2 : ℝ) :
    -∑ i, ∑ j, G i j * (U i j * k + a j * (k1 * f i) +
        (a i * (k1 * f j) + u * (k2 * f i * f j + k1 * P i j))) +
        ∑ j, b j * (a j * k + u * (k1 * f j)) =
      k * (-∑ i, ∑ j, G i j * U i j + ∑ j, b j * a j) +
        k1 * (2 * -∑ i, ∑ j, G i j * f i * a j +
          u * (-∑ i, ∑ j, G i j * P i j + ∑ j, b j * f j)) -
        k2 * u * ∑ i, ∑ j, G i j * f i * f j := by
  have hc : ∑ i, ∑ j, G i j * (a i * f j) = ∑ i, ∑ j, G i j * f i * a j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hG j i]
    ring
  have e1 : ∑ i, ∑ j, G i j * (U i j * k + a j * (k1 * f i) +
        (a i * (k1 * f j) + u * (k2 * f i * f j + k1 * P i j))) =
      k * ∑ i, ∑ j, G i j * U i j + k1 * ∑ i, ∑ j, G i j * f i * a j +
        k1 * ∑ i, ∑ j, G i j * (a i * f j) + k2 * u * ∑ i, ∑ j, G i j * f i * f j +
        k1 * u * ∑ i, ∑ j, G i j * P i j := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have e2 : ∑ j, b j * (a j * k + u * (k1 * f j)) =
      k * ∑ j, b j * a j + k1 * u * ∑ j, b j * f j := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e1, e2, hc]
  ring

/-- The wave operator of `u k(φ)`, blueprint `eq_calch`. -/
theorem box_mul_comp {g : MatrixField n} {x : E n}
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x) (hsymm : (g x)ᵀ = g x)
    (hdet : (g x).det ≠ 0) {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k) {u φ : E n → ℝ}
    (hu : ContDiffAt ℝ 2 u x) (hφ : ContDiffAt ℝ 2 φ x) :
    box g (fun y => u y * k (φ y)) x =
      k (φ x) * box g u x +
        deriv k (φ x) * (2 * -coform g x (d φ x) (d u x) + u x * box g φ x) -
          deriv (deriv k) (φ x) * u x * coform g x (d φ x) (d φ x) := by
  have hk1 : Differentiable ℝ k := hk.differentiable (by simp)
  have hud := hu.differentiableAt (by simp)
  have hφd := hφ.differentiableAt (by simp)
  have hF : ContDiffAt ℝ 2 (fun y => u y * k (φ y)) x :=
    hu.mul ((hk.of_le (by simp)).contDiffAt.comp x hφ)
  have hd1 : ∀ j, d (fun y => u y * k (φ y)) x j =
      d u x j * k (φ x) + u x * (deriv k (φ x) * d φ x j) := fun j => by
    rw [d_mul (v := fun z => k (φ z)) hud ((hk1 _).comp x hφd), d_comp_real (hk1 _) hφd]
  have hG : ∀ i j, (g x)⁻¹ i j = (g x)⁻¹ j i := fun i j => by
    rw [← Matrix.transpose_apply (g x)⁻¹, Matrix.transpose_nonsing_inv, hsymm]
  rw [box_eq hg hdet hF, box_eq hg hdet hu, box_eq hg hdet hφ]
  simp only [d2_mul_comp hk hu hφ, hd1, coform_def]
  exact box_mul_comp_algebra _ _ _ hG _ _ _ _ _ _ _

end Pointwise

theorem integrable_of_eq_zero_off {f : E n → ℝ} {K : Set (E n)} (hf : Continuous f)
    (hK : IsCompact K) (h0 : ∀ x ∉ K, f x = 0) : Integrable f :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.intro hK h0)

section Cutoff

open Real

theorem deriv_smoothTransition_of_neg {t : ℝ} (ht : t < 0) : deriv smoothTransition t = 0 := by
  have : smoothTransition =ᶠ[𝓝 t] fun _ => 0 := by
    filter_upwards [Iio_mem_nhds ht] with r hr
    exact smoothTransition.zero_of_nonpos (le_of_lt hr)
  rw [this.deriv_eq, deriv_const]

theorem deriv_smoothTransition_of_one_lt {t : ℝ} (ht : 1 < t) :
    deriv smoothTransition t = 0 := by
  have : smoothTransition =ᶠ[𝓝 t] fun _ => 1 := by
    filter_upwards [Ioi_mem_nhds ht] with r hr
    exact smoothTransition.one_of_one_le (le_of_lt hr)
  rw [this.deriv_eq, deriv_const]

theorem continuous_deriv_smoothTransition : Continuous (deriv smoothTransition) :=
  (smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl

theorem exists_abs_mul_deriv_smoothTransition_le :
    ∃ B, ∀ t, |t * deriv smoothTransition t| ≤ B := by
  have hc : Continuous fun t => t * deriv smoothTransition t :=
    continuous_id.mul continuous_deriv_smoothTransition
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0 : ℝ) 1)
    hc.continuousOn
  refine ⟨max B 0, fun t => ?_⟩
  by_cases h0 : t < 0
  · simp [deriv_smoothTransition_of_neg h0]
  by_cases h1 : 1 < t
  · simp [deriv_smoothTransition_of_one_lt h1]
  exact (by simpa using hB t ⟨not_lt.1 h0, not_lt.1 h1⟩ :
    |t * deriv smoothTransition t| ≤ B).trans (le_max_left _ _)

theorem tendsto_smoothTransition_div (r : ℝ) :
    Tendsto (fun ε => smoothTransition (r / ε)) (𝓝[>] 0) (𝓝 (if 0 < r then 1 else 0)) := by
  split_ifs with hr
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hr] with ε hε
    rw [smoothTransition.one_of_one_le]
    rw [le_div_iff₀ hε.1]
    linarith [hε.2]
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    rw [smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (not_lt.1 hr) hε.le)]

theorem hasDerivAt_smoothTransition_div (s ε r : ℝ) :
    HasDerivAt (fun r => smoothTransition ((r - s) / ε))
      (deriv smoothTransition ((r - s) / ε) / ε) r := by
  have h1 := (((smoothTransition.contDiff (n := 1)).differentiable (by simp))
    ((r - s) / ε)).hasDerivAt
  have h2 := ((hasDerivAt_id r).sub_const s).div_const ε
  refine (h1.comp r h2).congr_deriv ?_
  ring

end Cutoff

section Lipschitz

/-- A `C¹` function vanishing on the level set `{φ = s}` is bounded by a multiple of
`|φ - s|`, if it vanishes outside a compact set on which `dφ ≠ 0` along `{φ = s}`. -/
theorem exists_abs_le_mul_abs_sub {m φ : E n → ℝ} (hm : ContDiff ℝ 1 m) (hφ : ContDiff ℝ 1 φ)
    {K : Set (E n)} (hK : IsCompact K) (hmK : ∀ x ∉ K, m x = 0) {s : ℝ}
    (hzero : ∀ x, φ x = s → m x = 0) (hdφ : ∀ x ∈ K, φ x = s → fderiv ℝ φ x ≠ 0) :
    ∃ C, 0 ≤ C ∧ ∀ x, |m x| ≤ C * |φ x - s| := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hm.continuous.continuousOn
  have hM' : ∀ x, |m x| ≤ max M 0 := fun x => by
    by_cases hx : x ∈ K
    · exact (by simpa using hM x hx : |m x| ≤ M).trans (le_max_left _ _)
    · rw [hmK x hx, abs_zero]
      exact le_max_right _ _
  have key : ∃ C, ∀ x ∈ K, |m x| ≤ C * |φ x - s| := by
    refine hK.induction_on (p := fun S => ∃ C, ∀ x ∈ S, |m x| ≤ C * |φ x - s|) ⟨0, by simp⟩
      (fun S T hST ⟨C, hC⟩ => ⟨C, fun x hx => hC x (hST hx)⟩)
      (fun S T ⟨C, hC⟩ ⟨C', hC'⟩ => ⟨max C C', fun x hx => ?_⟩) fun p hp => ?_
    · rcases hx with hx | hx
      · exact (hC x hx).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
      · exact (hC' x hx).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _))
    by_cases hps : φ p = s
    · obtain ⟨w, hw⟩ : ∃ w, fderiv ℝ φ p w ≠ 0 := by
        by_contra! h
        exact hdφ p hp hps (ContinuousLinearMap.ext h)
      set v := (fderiv ℝ φ p w)⁻¹ • w
      have hv : fderiv ℝ φ p v = 1 := by simp [v, hw]
      have hcont : Continuous fun y => fderiv ℝ φ y v :=
        (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
      obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 ((isOpen_lt continuous_const hcont).mem_nhds
        (show (1 : ℝ) / 2 < fderiv ℝ φ p v by rw [hv]; norm_num))
      obtain ⟨L, hL⟩ := (isCompact_closedBall p r).exists_bound_of_continuousOn
        (hm.continuous_fderiv (by simp)).continuousOn
      have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL p (Metric.mem_closedBall_self hr.le))
      have hφc := hφ.continuous
      refine ⟨Metric.ball p (r / 2) ∩ {x | |φ x - s| * (2 * ‖v‖) < r / 2},
        mem_nhdsWithin_of_mem_nhds (inter_mem (Metric.ball_mem_nhds p (by positivity))
          ((isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simp [hps]; positivity))),
        2 * L * ‖v‖, fun x hx => ?_⟩
      obtain ⟨hx1, hx2 : |φ x - s| * (2 * ‖v‖) < r / 2⟩ := hx
      set T := 2 * |φ x - s| with hTdef
      have hT : 0 ≤ T := by positivity
      have hseg : ∀ t ∈ Icc (-T) T, x + t • v ∈ Metric.ball p r := by
        intro t ht
        rw [Metric.mem_ball] at hx1 ⊢
        have htT : |t| ≤ T := abs_le.2 ⟨by linarith [ht.1], ht.2⟩
        have : |t| * ‖v‖ ≤ T * ‖v‖ := mul_le_mul_of_nonneg_right htT (norm_nonneg _)
        calc dist (x + t • v) p ≤ dist x p + ‖t • v‖ := by
              rw [dist_eq_norm, dist_eq_norm, add_sub_right_comm]
              exact norm_add_le _ _
          _ < r := by
              rw [norm_smul, Real.norm_eq_abs]
              linarith
      have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => φ (x + t • v))
          (fderiv ℝ φ (x + t • v) v) t := fun t => by
        have h1 : HasDerivAt (fun t : ℝ => x + t • v) v t := by
          simpa using ((hasDerivAt_id t).smul_const v).const_add x
        exact ((hφ.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt t h1
      have hfc : Continuous fun t : ℝ => φ (x + t • v) :=
        continuous_iff_continuousAt.2 fun t => (hderiv t).continuousAt
      have hmono := (convex_Icc (-T) T).mul_sub_le_image_sub_of_le_deriv
        (f := fun t => φ (x + t • v)) hfc.continuousOn
        (fun t _ => (hderiv t).differentiableAt.differentiableWithinAt) (C := 1 / 2)
        (fun t ht => by
          rw [(hderiv t).deriv]
          exact le_of_lt (hball (hseg t (interior_subset ht))))
      have h1 := hmono 0 ⟨by linarith, hT⟩ T ⟨by linarith, le_rfl⟩ hT
      have h2 := hmono (-T) ⟨le_rfl, by linarith⟩ 0 ⟨by linarith, hT⟩ (by linarith)
      simp only [zero_smul, add_zero] at h1 h2
      obtain ⟨t, ht, hts⟩ : s ∈ (fun t => φ (x + t • v)) '' Icc (-T) T := by
        refine intermediate_value_Icc (by linarith) hfc.continuousOn ⟨?_, ?_⟩
        · linarith [le_abs_self (φ x - s)]
        · linarith [neg_abs_le (φ x - s)]
      have hx0 : x ∈ Metric.ball p r := by simpa using hseg 0 ⟨by linarith, hT⟩
      have hlip := (convex_ball p r).norm_image_sub_le_of_norm_fderiv_le (f := m)
        (fun y _ => (hm.differentiable (by simp)) y)
        (fun y hy => hL y (Metric.ball_subset_closedBall hy)) hx0 (hseg t ht)
      rw [hzero _ hts, zero_sub, norm_neg, Real.norm_eq_abs, add_sub_cancel_left, norm_smul,
        Real.norm_eq_abs] at hlip
      have htT : |t| ≤ T := abs_le.2 ⟨by linarith [ht.1], ht.2⟩
      calc |m x| ≤ L * (|t| * ‖v‖) := hlip
        _ ≤ L * (T * ‖v‖) := by gcongr
        _ = 2 * L * ‖v‖ * |φ x - s| := by rw [hTdef]; ring
    · have hpos : 0 < |φ p - s| := abs_pos.2 (sub_ne_zero.2 hps)
      refine ⟨{x | |φ p - s| / 2 < |φ x - s|}, mem_nhdsWithin_of_mem_nhds ?_,
        2 * max M 0 / |φ p - s|, fun x (hx : |φ p - s| / 2 < |φ x - s|) => ?_⟩
      · exact (isOpen_lt continuous_const ((hφ.continuous.sub continuous_const).abs)).mem_nhds
          (show |φ p - s| / 2 < |φ p - s| by linarith)
      · rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
        have := hM' x
        nlinarith [le_max_right M 0]
  obtain ⟨C, hC⟩ := key
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ K
  · exact (hC x hx).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  · rw [hmK x hx, abs_zero]
    exact mul_nonneg (le_max_right _ _) (abs_nonneg _)

end Lipschitz

section Jump

open Real

variable {g : MatrixField n}

theorem indicator_eq_mul_ite (φ f : E n → ℝ) (s : ℝ) (x : E n) :
    {x | s < φ x}.indicator f x = f x * if s < φ x then 1 else 0 := by
  by_cases h : s < φ x <;> simp [h]

/-- The weak jump identity for `u` and `φ` smooth on `ℝ^{1+n}`; the hypotheses are only needed
on the support of `h`. -/
theorem integral_indicator_mul_box_eq_of_contDiff
    (hg : ∀ i j, ContDiff ℝ ∞ fun x => g x i j) (hsymm : ∀ x, (g x)ᵀ = g x)
    (hdet : ∀ x, (g x).det ≠ 0) {u φ h : E n → ℝ} (hu : ContDiff ℝ ∞ u)
    (hφ : ContDiff ℝ ∞ φ) (hh : ContDiff ℝ ∞ h) (hhc : HasCompactSupport h) {s : ℝ}
    (heik : ∀ x ∈ tsupport h, coform g x (d φ x) (d φ x) = 0)
    (hdφ : ∀ x ∈ tsupport h, φ x = s → d φ x ≠ 0)
    (htr : ∀ x ∈ tsupport h, φ x = s →
      2 * -coform g x (d φ x) (d u x) + u x * box g φ x = 0) :
    ∫ x, {x | s < φ x}.indicator u x * box g h x * √|(g x).det| =
      ∫ x, {x | s < φ x}.indicator (box g u) x * h x * √|(g x).det| := by
  have hρs := contDiff_sqrt_abs_det hg hdet
  have hρ : Continuous fun x => √|(g x).det| := hρs.continuous
  have hbh := continuous_box hg hdet hh
  have hbu := continuous_box hg hdet hu
  have hK : IsCompact (tsupport h) := hhc
  have h0 : ∀ x ∉ tsupport h, h x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hb0 : ∀ x ∉ tsupport h, box g h x = 0 := fun x hx =>
    box_eq_zero_of_notMem_tsupport (g := g) hx
  obtain ⟨a, ha_def⟩ : ∃ a : E n → ℝ,
      a = fun x => 2 * -coform g x (d φ x) (d u x) + u x * box g φ x := ⟨_, rfl⟩
  have ha : ContDiff ℝ ∞ a := by
    rw [ha_def]
    simp only [coform_def]
    exact (contDiff_const.mul (ContDiff.sum fun j _ => ContDiff.sum fun k _ =>
      ((contDiff_inv_apply hg hdet j k).mul (contDiff_d hφ j)).mul (contDiff_d hu k)).neg).add
      (hu.mul (contDiff_box hg hdet hφ))
  obtain ⟨H, hH_def⟩ : ∃ H : ℝ → ℝ → ℝ, H = fun ε r => smoothTransition ((r - s) / ε) :=
    ⟨_, rfl⟩
  have hHval : ∀ ε r, H ε r = smoothTransition ((r - s) / ε) := by simp [hH_def]
  have hH : ∀ ε, ContDiff ℝ ∞ (H ε) := fun ε => by
    rw [hH_def]
    exact smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const ε)
  have hH' : ∀ ε r, deriv (H ε) r = deriv smoothTransition ((r - s) / ε) / ε := by
    subst hH_def
    exact fun ε r => (hasDerivAt_smoothTransition_div s ε r).deriv
  have hgd : ∀ x i j, DifferentiableAt ℝ (fun y => g y i j) x := fun x i j =>
    (hg i j).differentiable (by simp) x
  have hdT := continuous_deriv_smoothTransition
  have hdH : ∀ ε, Continuous fun x => deriv (H ε) (φ x) := fun ε => by
    simp only [hH']
    exact (hdT.comp ((hφ.continuous.sub continuous_const).div_const ε)).div_const ε
  have hid : ∀ ε, ∫ x, u x * H ε (φ x) * box g h x * √|(g x).det| =
      (∫ x, H ε (φ x) * box g u x * h x * √|(g x).det|) +
        ∫ x, deriv (H ε) (φ x) * (a x * h x * √|(g x).det|) := by
    intro ε
    have hw : ContDiff ℝ ∞ fun y => u y * H ε (φ y) := hu.mul ((hH ε).comp hφ)
    refine (integral_mul_box_comm_of_isCompact hg hsymm hdet hw hh
      (hK.of_isClosed_subset ((isClosed_tsupport _).inter (isClosed_tsupport _))
        inter_subset_right)).trans ?_
    have hHc : Continuous fun x => H ε (φ x) := (hH ε).continuous.comp hφ.continuous
    rw [← integral_add]
    · refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      by_cases hx : x ∈ tsupport h
      · simp only
        rw [box_mul_comp (hgd x) (hsymm x) (hdet x) (hH ε) (hu.contDiffAt.of_le (by simp))
          (hφ.contDiffAt.of_le (by simp)), heik x hx, ha_def]
        ring
      · simp [h0 x hx]
    · exact integrable_of_eq_zero_off (((hHc.mul hbu).mul hh.continuous).mul hρ) hK
        fun x hx => by simp [h0 x hx]
    · exact integrable_of_eq_zero_off ((hdH ε).mul ((ha.continuous.mul hh.continuous).mul hρ))
        hK fun x hx => by simp [h0 x hx]
  have hlim : ∀ x, Tendsto (fun ε => H ε (φ x)) (𝓝[>] 0)
      (𝓝 (if s < φ x then (1 : ℝ) else 0)) := fun x => by
    simpa [hHval, sub_pos] using tendsto_smoothTransition_div (φ x - s)
  have hH01 : ∀ ε r, |H ε r| ≤ 1 := fun ε r => by
    rw [hHval, abs_of_nonneg (smoothTransition.nonneg _)]
    exact smoothTransition.le_one _
  have hA : Tendsto (fun ε => ∫ x, u x * H ε (φ x) * box g h x * √|(g x).det|) (𝓝[>] 0)
      (𝓝 (∫ x, u x * (if s < φ x then 1 else 0) * box g h x * √|(g x).det|)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x => abs (u x * box g h x * √|(g x).det|)) (Eventually.of_forall fun ε => ?_)
      (Eventually.of_forall fun ε => Eventually.of_forall fun x => ?_) ?_
      (Eventually.of_forall fun x => ?_)
    · exact (((hu.continuous.mul ((hH ε).continuous.comp hφ.continuous)).mul hbh).mul
        hρ).aestronglyMeasurable
    · rw [Real.norm_eq_abs, show u x * H ε (φ x) * box g h x * √|(g x).det| =
        H ε (φ x) * (u x * box g h x * √|(g x).det|) by ring, abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (hH01 _ _)
    · exact (integrable_of_eq_zero_off ((hu.continuous.mul hbh).mul hρ) hK
        fun x hx => by simp [hb0 x hx]).abs
    · exact (((hlim x).const_mul (u x)).mul_const _).mul_const _
  have hB : Tendsto (fun ε => ∫ x, H ε (φ x) * box g u x * h x * √|(g x).det|) (𝓝[>] 0)
      (𝓝 (∫ x, (if s < φ x then 1 else 0) * box g u x * h x * √|(g x).det|)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x => abs (box g u x * h x * √|(g x).det|)) (Eventually.of_forall fun ε => ?_)
      (Eventually.of_forall fun ε => Eventually.of_forall fun x => ?_) ?_
      (Eventually.of_forall fun x => ?_)
    · exact (((((hH ε).continuous.comp hφ.continuous).mul hbu).mul hh.continuous).mul
        hρ).aestronglyMeasurable
    · rw [Real.norm_eq_abs, show H ε (φ x) * box g u x * h x * √|(g x).det| =
        H ε (φ x) * (box g u x * h x * √|(g x).det|) by ring, abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (hH01 _ _)
    · exact (integrable_of_eq_zero_off ((hbu.mul hh.continuous).mul hρ) hK
        fun x hx => by simp [h0 x hx]).abs
    · exact (((hlim x).mul_const _).mul_const _).mul_const _
  obtain ⟨C, hC0, hC⟩ := exists_abs_le_mul_abs_sub (m := fun x => a x * h x * √|(g x).det|)
    (((ha.mul hh).mul hρs).of_le (by simp)) (hφ.of_le (by simp)) hK
    (fun x hx => by simp [h0 x hx]) (s := s)
    (fun x hxs => by
      by_cases hx : x ∈ tsupport h
      · have := htr x hx hxs
        simp only [ha_def, this, zero_mul]
      · simp [h0 x hx])
    (fun x hx hxs hf => hdφ x hx hxs (by ext j; simp [d_def, hf]))
  obtain ⟨B, hB0⟩ := exists_abs_mul_deriv_smoothTransition_le
  have hC' : Tendsto (fun ε => ∫ x, deriv (H ε) (φ x) * (a x * h x * √|(g x).det|)) (𝓝[>] 0)
      (𝓝 (∫ _ : E n, (0 : ℝ))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      ((tsupport h).indicator fun _ => C * B) (Eventually.of_forall fun ε => ?_) ?_ ?_
      (Eventually.of_forall fun x => ?_)
    · exact ((hdH ε).mul ((ha.continuous.mul hh.continuous).mul hρ)).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      refine Eventually.of_forall fun x => ?_
      by_cases hx : x ∈ tsupport h
      · rw [indicator_of_mem hx, Real.norm_eq_abs, hH', abs_mul, abs_div, abs_of_pos hε]
        have h1 := hB0 ((φ x - s) / ε)
        calc |deriv smoothTransition ((φ x - s) / ε)| / ε * abs (a x * h x * √|(g x).det|)
            ≤ |deriv smoothTransition ((φ x - s) / ε)| / ε * (C * |φ x - s|) := by
              gcongr
              exact hC x
          _ = C * |(φ x - s) / ε * deriv smoothTransition ((φ x - s) / ε)| := by
              rw [abs_mul, abs_div, abs_of_pos hε]
              field_simp
          _ ≤ C * B := by gcongr
      · simp [indicator_of_notMem hx, h0 x hx]
    · exact (integrableOn_const hK.measure_lt_top.ne).integrable_indicator
        hK.isClosed.measurableSet
    · rcases lt_trichotomy (φ x) s with hlt | heq | hgt
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
        rw [hH', deriv_smoothTransition_of_neg (div_neg_of_neg_of_pos (sub_neg.2 hlt) hε)]
        simp
      · have := hC x
        rw [heq, sub_self, abs_zero, mul_zero] at this
        simp only [abs_nonpos_iff.1 this, mul_zero]
        exact tendsto_const_nhds
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 hgt)] with ε hε
        rw [hH', deriv_smoothTransition_of_one_lt ((one_lt_div hε.1).2 hε.2)]
        simp
  have hfinal := tendsto_nhds_unique hA ((hB.add hC').congr fun ε => (hid ε).symm)
  rw [integral_zero, add_zero] at hfinal
  simp only [indicator_eq_mul_ite]
  rw [hfinal]
  congr 1
  ext x
  ring

theorem contDiff_mul_of_tsupport_subset {χ f : E n → ℝ} {V : Set (E n)} (hV : IsOpen V)
    (hχ : ContDiff ℝ ∞ χ) (hχV : tsupport χ ⊆ V) (hf : ContDiffOn ℝ ∞ f V) :
    ContDiff ℝ ∞ fun x => χ x * f x := by
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  by_cases hx : x ∈ V
  · exact hχ.contDiffAt.mul (hf.contDiffAt (hV.mem_nhds hx))
  · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [notMem_tsupport_iff_eventuallyEq.1 fun h => hx (hχV h)] with y hy
    simp [hy]

/-- The weak jump identity (one direction of `lem_calculus`): for an eikonal phase `φ` with
`dφ ≠ 0` and a function `u`, both smooth on an open set `V`, whose transport coefficient
`2 Z u + u □_g φ` (with `Z u = -g(dφ, du)`) vanishes on `{φ = s}` within the support of the test
function `h`, `∫ 1_{φ > s} u □_g h ρ = ∫ 1_{φ > s} (□_g u) h ρ`. -/
theorem integral_indicator_mul_box_eq
    (hg : ∀ i j, ContDiff ℝ ∞ fun x => g x i j) (hsymm : ∀ x, (g x)ᵀ = g x)
    (hdet : ∀ x, (g x).det ≠ 0) {V : Set (E n)} (hV : IsOpen V) {u φ h : E n → ℝ}
    (hu : ContDiffOn ℝ ∞ u V) (hφ : ContDiffOn ℝ ∞ φ V) (hh : ContDiff ℝ ∞ h)
    (hhc : HasCompactSupport h) (hhV : tsupport h ⊆ V)
    (heik : ∀ x ∈ V, coform g x (d φ x) (d φ x) = 0) (hdφ : ∀ x ∈ V, d φ x ≠ 0) {s : ℝ}
    (htr : ∀ x ∈ tsupport h, φ x = s →
      2 * -coform g x (d φ x) (d u x) + u x * box g φ x = 0) :
    ∫ x, {x | s < φ x}.indicator u x * box g h x * √|(g x).det| =
      ∫ x, {x | s < φ x}.indicator (box g u) x * h x * √|(g x).det| := by
  have hK : IsCompact (tsupport h) := hhc
  obtain ⟨χ, hχ, -, -, hχV, hχ1⟩ := exists_cutoff hK hV hhV
  have hloc : ∀ (f : E n → ℝ), ∀ x ∈ tsupport h, (fun y => χ y * f y) =ᶠ[𝓝 x] f :=
    fun f x hx => by
      filter_upwards [hχ1 x hx] with y hy
      rw [hy, Pi.one_apply, one_mul]
  have hval : ∀ (f : E n → ℝ), ∀ x ∈ tsupport h, χ x * f x = f x := fun f x hx =>
    (hloc f x hx).eq_of_nhds
  have key := integral_indicator_mul_box_eq_of_contDiff hg hsymm hdet
    (contDiff_mul_of_tsupport_subset hV hχ hχV hu)
    (contDiff_mul_of_tsupport_subset hV hχ hχV hφ) hh hhc (s := s)
    (fun x hx => by
      rw [d_congr (hloc φ x hx)]
      exact heik x (hhV hx))
    (fun x hx _ => by
      rw [d_congr (hloc φ x hx)]
      exact hdφ x (hhV hx))
    (fun x hx hxs => by
      rw [hval φ x hx] at hxs
      rw [d_congr (hloc φ x hx), d_congr (hloc u x hx), box_congr (hloc φ x hx), hval u x hx]
      exact htr x hx hxs)
  simp only [indicator_eq_mul_ite] at key ⊢
  convert key using 1
  · refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ tsupport h
    · simp only [hval u x hx, hval φ x hx]
    · simp [box_eq_zero_of_notMem_tsupport (g := g) hx]
  · refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ tsupport h
    · simp only [hval φ x hx, box_congr (hloc u x hx)]
    · simp [image_eq_zero_of_notMem_tsupport hx]

/-- The weak jump identity when the transport coefficient `2 Z u + u □_g φ = θ` vanishes outside
`S`, for test functions `h` whose support does not meet `S ∩ {φ = s}`. -/
theorem integral_indicator_mul_box_eq_of_transport
    (hg : ∀ i j, ContDiff ℝ ∞ fun x => g x i j) (hsymm : ∀ x, (g x)ᵀ = g x)
    (hdet : ∀ x, (g x).det ≠ 0) {V : Set (E n)} (hV : IsOpen V) {u φ h θ : E n → ℝ}
    {S : Set (E n)} (hu : ContDiffOn ℝ ∞ u V) (hφ : ContDiffOn ℝ ∞ φ V)
    (hh : ContDiff ℝ ∞ h) (hhc : HasCompactSupport h) (hhV : tsupport h ⊆ V)
    (heik : ∀ x ∈ V, coform g x (d φ x) (d φ x) = 0) (hdφ : ∀ x ∈ V, d φ x ≠ 0)
    (htr : ∀ x ∈ V, 2 * -coform g x (d φ x) (d u x) + u x * box g φ x = θ x)
    (hθ : ∀ x ∉ S, θ x = 0) {s : ℝ} (hS : tsupport h ∩ S ∩ {x | φ x = s} = ∅) :
    ∫ x, {x | s < φ x}.indicator u x * box g h x * √|(g x).det| =
      ∫ x, {x | s < φ x}.indicator (box g u) x * h x * √|(g x).det| :=
  integral_indicator_mul_box_eq hg hsymm hdet hV hu hφ hh hhc hhV heik hdφ fun x hx hxs => by
    rw [htr x (hhV hx), hθ x fun hxS => ?_]
    exact Set.eq_empty_iff_forall_notMem.1 hS x ⟨⟨hx, hxS⟩, hxs⟩

end Jump

end

end LorentzianCalderon
