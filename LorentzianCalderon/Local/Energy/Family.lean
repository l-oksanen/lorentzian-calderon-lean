module

public import LorentzianCalderon.Local.Energy.Limits

public section

/-!
# Families of functions `w s`, jointly `C²` in `(s, x)`

The partial derivatives of `w s` in `x`, of first and second order, and `□_g (w s)` depend
continuously on `(s, x)`.
-/

namespace LorentzianCalderon

noncomputable section
open Set MeasureTheory Filter Topology
open scoped ContDiff

variable {n : ℕ}

/-- The derivative in the second variable is the restriction of the full derivative. -/
theorem continuousOn_comp_snd_prod {β : Type*} [TopologicalSpace β] {U V : Set (E n)}
    {f : E n → β} (hf : ContinuousOn f V) :
    ContinuousOn (fun p : ℝ × E n => f p.2) (univ ×ˢ (U ∩ V)) :=
  hf.comp continuousOn_snd fun _ hp => hp.2.2

theorem fderiv_snd_apply {F : ℝ × E n → ℝ} {s : ℝ} {y : E n}
    (hF : DifferentiableAt ℝ F (s, y)) (v : E n) :
    fderiv ℝ (fun y' => F (s, y')) y v = fderiv ℝ F (s, y) (0, v) := by
  have hcomp := hF.hasFDerivAt.comp y ((hasFDerivAt_const s y).prodMk (hasFDerivAt_id y))
  rw [show (fun y' => F (s, y')) = F ∘ fun y' => (s, y') from rfl, hcomp.fderiv]
  simp

section Family

variable {U : Set (E n)} {w : ℝ → E n → ℝ}

theorem isOpen_univ_prod (hU : IsOpen U) : IsOpen (univ ×ˢ U : Set (ℝ × E n)) :=
  isOpen_univ.prod hU

theorem family_contDiffOn (hW : ContDiffOn ℝ 2 (fun p : ℝ × E n => w p.1 p.2) (univ ×ˢ U))
    (s : ℝ) : ContDiffOn ℝ 2 (w s) U :=
  hW.comp (contDiff_const.prodMk contDiff_id).contDiffOn fun _ hy => ⟨mem_univ _, hy⟩

theorem family_continuousOn_d (hU : IsOpen U)
    (hW : ContDiffOn ℝ 2 (fun p : ℝ × E n => w p.1 p.2) (univ ×ˢ U)) (k : Fin (n + 1)) :
    ContinuousOn (fun p : ℝ × E n => d (w p.1) p.2 k) (univ ×ˢ U) := by
  refine (((hW.continuousOn_fderiv_of_isOpen (isOpen_univ_prod hU) one_le_two).clm_apply
    (continuousOn_const (c := ((0 : ℝ), EuclideanSpace.single k (1 : ℝ)))))).congr
      fun p hp => ?_
  exact d_param_eq ((hW.contDiffAt ((isOpen_univ_prod hU).mem_nhds
    ⟨mem_univ _, hp.2⟩)).differentiableAt (by norm_num)) k

theorem family_continuousOn_dd (hU : IsOpen U)
    (hW : ContDiffOn ℝ 2 (fun p : ℝ × E n => w p.1 p.2) (univ ×ˢ U)) (k j : Fin (n + 1)) :
    ContinuousOn (fun p : ℝ × E n => d (fun y => d (w p.1) y k) p.2 j) (univ ×ˢ U) := by
  have hO := isOpen_univ_prod hU
  set Φ : ℝ × E n → ℝ :=
    fun p => fderiv ℝ (fun p : ℝ × E n => w p.1 p.2) p (0, EuclideanSpace.single k 1)
  have hΦ : ContDiffOn ℝ 1 Φ (univ ×ˢ U) :=
    (hW.fderiv_of_isOpen hO (m := 1) (by norm_num)).clm_apply contDiffOn_const
  refine ((hΦ.continuousOn_fderiv_of_isOpen hO le_rfl).clm_apply
    (continuousOn_const (c := ((0 : ℝ), EuclideanSpace.single j (1 : ℝ))))).congr fun p hp => ?_
  simp only
  have hev : (fun y => d (w p.1) y k) =ᶠ[𝓝 p.2] fun y => Φ (p.1, y) := by
    filter_upwards [hU.mem_nhds hp.2] with y hy
    exact d_param_eq ((hW.contDiffAt ((isOpen_univ_prod hU).mem_nhds
      ⟨mem_univ _, hy⟩)).differentiableAt (by norm_num)) k
  rw [d_congr hev, d_def]
  exact fderiv_snd_apply (F := Φ) ((hΦ.contDiffAt (hO.mem_nhds hp)).differentiableAt
    (by norm_num)) _

end Family

/-- `□_g u` in terms of the first and second partial derivatives of `u`. -/
theorem box_eq_sum {V : Set (E n)} (hV : IsOpen V) {g : MatrixField n}
    (hG : ∀ c e, ContDiffOn ℝ 1 (fun y => (g y)⁻¹ c e) V) (hρ : ContDiffOn ℝ 1 (vol g) V)
    {x : E n} (hx : x ∈ V) (hρx : vol g x ≠ 0) {u : E n → ℝ} (hu : ContDiffAt ℝ 2 u x) :
    box g u x = -∑ j, ∑ k, ((vol g x)⁻¹ * d (fun y => vol g y * (g y)⁻¹ j k) x j * d u x k +
      (g x)⁻¹ j k * d (fun y => d u y k) x j) := by
  have hVx := hV.mem_nhds hx
  have hρd : DifferentiableAt ℝ (vol g) x := (hρ.contDiffAt hVx).differentiableAt one_ne_zero
  have hGd : ∀ c e, DifferentiableAt ℝ (fun y => (g y)⁻¹ c e) x := fun c e =>
    ((hG c e).contDiffAt hVx).differentiableAt one_ne_zero
  have hξ : ∀ k, DifferentiableAt ℝ (fun y => d u y k) x := fun k =>
    (contDiffAt_d (m := 1) hu k).differentiableAt one_ne_zero
  rw [show box g u x = -(vol g x)⁻¹ * ∑ j, d (Current.flux (vol g) (ginv g) (dc u) j) x j by
    rw [box_eq_flux g u x]; simp only [flux_vol_ginv_dc, vol_def]]
  have hfl : ∀ j, Current.flux (vol g) (ginv g) (dc u) j =
      fun y => ∑ k, (vol g y * (g y)⁻¹ j k) * d u y k := by
    intro j; ext y
    simp only [Current.flux_def, ginv_def, dc_def, Finset.mul_sum, mul_assoc]
  simp only [hfl]
  have hd : ∀ j, d (fun y => ∑ k, (vol g y * (g y)⁻¹ j k) * d u y k) x j =
      ∑ k, (d (fun y => vol g y * (g y)⁻¹ j k) x j * d u x k +
        vol g x * (g x)⁻¹ j k * d (fun y => d u y k) x j) := by
    intro j
    rw [d_sum (u := fun k y => (vol g y * (g y)⁻¹ j k) * d u y k)
      (fun k _ => (hρd.mul (hGd j k)).mul (hξ k))]
    exact Finset.sum_congr rfl fun k _ => d_mul (hρd.mul (hGd j k)) (hξ k) j
  simp only [hd, Finset.mul_sum]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  field_simp

namespace EnergySetting

variable {V : Set (E n)} {g : MatrixField n} {Y : E n → E n} {ψ ψ' : E n → ℝ} {τ c : ℝ}
  (h : EnergySetting V g Y ψ ψ' τ c)
include h

theorem family_continuousOn_box {U : Set (E n)} (hU : IsOpen U) {w : ℝ → E n → ℝ}
    (hW : ContDiffOn ℝ 2 (fun p : ℝ × E n => w p.1 p.2) (univ ×ˢ U)) :
    ContinuousOn (fun p : ℝ × E n => box g (w p.1) p.2) (univ ×ˢ (U ∩ V)) := by
  have hG : ∀ c e, ContDiffOn ℝ 1 (fun y => (g y)⁻¹ c e) V := fun c e =>
    (h.contDiffOn_inv c e).of_le (by simp)
  have hρ : ContDiffOn ℝ 1 (vol g) V := h.contDiffOn_vol.of_le (by simp)
  have hsub : univ ×ˢ (U ∩ V) ⊆ (univ ×ˢ U : Set (ℝ × E n)) :=
    prod_mono subset_rfl inter_subset_left
  have hcoef : ∀ j k, ContinuousOn (fun p : ℝ × E n =>
      (vol g p.2)⁻¹ * d (fun y => vol g y * (g y)⁻¹ j k) p.2 j) (univ ×ˢ (U ∩ V)) := by
    intro j k
    refine continuousOn_comp_snd_prod
      (f := fun x => (vol g x)⁻¹ * d (fun y => vol g y * (g y)⁻¹ j k) x j) (ContinuousOn.mul ?_ ?_)
    · exact hρ.continuousOn.inv₀ fun x hx => (vol_pos (h.det_ne_zero hx)).ne'
    · exact continuousOn_d_of_contDiffOn h.isOpen (hρ.mul (hG j k)) j
  have hcont : ContinuousOn (fun p : ℝ × E n => -∑ j, ∑ k,
      ((vol g p.2)⁻¹ * d (fun y => vol g y * (g y)⁻¹ j k) p.2 j * d (w p.1) p.2 k +
        (g p.2)⁻¹ j k * d (fun y => d (w p.1) y k) p.2 j)) (univ ×ˢ (U ∩ V)) := by
    refine ContinuousOn.neg (continuousOn_finsetSum _ fun j _ => continuousOn_finsetSum _
      fun k _ => ((hcoef j k).mul ((family_continuousOn_d hU hW k).mono hsub)).add ?_)
    exact (continuousOn_comp_snd_prod (U := U) (hG j k).continuousOn).mul
      ((family_continuousOn_dd hU hW k j).mono hsub)
  refine hcont.congr fun p hp => ?_
  exact box_eq_sum h.isOpen hG hρ hp.2.2 (vol_pos (h.det_ne_zero hp.2.2)).ne'
    (((family_contDiffOn hW p.1).contDiffAt (hU.mem_nhds hp.2.1)))

theorem family_continuousOn_wT {U : Set (E n)} (hU : IsOpen U) {w : ℝ → E n → ℝ}
    (hW : ContDiffOn ℝ 2 (fun p : ℝ × E n => w p.1 p.2) (univ ×ˢ U)) (σ lam : ℝ)
    {α : E n → ℝ} (hα : ContDiffOn ℝ ∞ α V) :
    ContinuousOn (fun p : ℝ × E n => wT g ψ (w p.1) σ lam α p.2) (univ ×ˢ (U ∩ V)) := by
  have hsub : univ ×ˢ (U ∩ V) ⊆ (univ ×ˢ U : Set (ℝ × E n)) :=
    prod_mono subset_rfl inter_subset_left
  have hψc : ContinuousOn ψ V := h.smooth_ψ.continuousOn
  simp only [wT_def]
  refine ((continuousOn_comp_snd_prod (U := U) (Real.continuous_exp.comp_continuousOn
    (continuousOn_const.mul hψc))).mul
    (continuousOn_comp_snd_prod (U := U) h.contDiffOn_vol.continuousOn)).mul ?_
  exact ContinuousOn.emTensor_bil (continuousOn_comp_snd_prod (U := U) h.continuousOn_ginv)
    continuousOn_const (hW.continuousOn.mono hsub)
    (continuousOn_pi.2 fun k => (family_continuousOn_d hU hW k).mono hsub)
    (continuousOn_comp_snd_prod (U := U)
      (continuousOn_d h.isOpen (hα.of_le (by simp))))
    (continuousOn_comp_snd_prod (U := U)
      (continuousOn_d h.isOpen (h.smooth_ψ.of_le (by simp))))

end EnergySetting

end

end LorentzianCalderon
