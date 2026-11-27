module

public import LorentzianCalderon.Setting.BoxGreen

public section

/-!
# Calculus of the wave operator

Linearity and locality of `□_g`, smoothness and support of `□_g u`, and Green's identity
`∫ u □_g ϑ dV_g = ∫ ϑ □_g u dV_g` on `ℝ^{1+n}` when the supports of `u` and `ϑ` meet in a
compact set.
-/

namespace LorentzianCalderon

noncomputable section
open MeasureTheory Set Filter WithLp
open scoped ContDiff Matrix Topology

variable {n : ℕ} {g g' : MatrixField n}

/-! ### Locality -/

lemma flux_eventuallyEq {u v : E n → ℝ} {x : E n} (h : u =ᶠ[𝓝 x] v) (j : Fin (n + 1)) :
    flux g u j =ᶠ[𝓝 x] flux g v j := by
  filter_upwards [h.eventuallyEq_nhds] with y hy
  simp only [flux_def, d_congr hy]

/-- `□_g u (x)` depends only on `u` near `x`. -/
theorem box_congr {u v : E n → ℝ} {x : E n} (h : u =ᶠ[𝓝 x] v) : box g u x = box g v x := by
  simp only [box_eq_flux, d_congr (flux_eventuallyEq h _)]

/-- `□_g u (x)` depends only on `g` near `x`. -/
theorem box_congr_metric {u : E n → ℝ} {x : E n} (h : g =ᶠ[𝓝 x] g') :
    box g u x = box g' u x := by
  have hflux : ∀ j, flux g u j =ᶠ[𝓝 x] flux g' u j := fun j => by
    filter_upwards [h] with y hy
    simp only [flux_def, hy]
  simp only [box_eq_flux, d_congr (hflux _), h.eq_of_nhds]

lemma box_zero (x : E n) : box g 0 x = 0 := by
  have : ∀ j, flux g (0 : E n → ℝ) j = 0 := fun j => by
    ext y
    simp [flux_def, d_def]
  simp [box_eq_flux, this, d_def]

lemma box_eq_zero_of_eventuallyEq {u : E n → ℝ} {x : E n} (h : u =ᶠ[𝓝 x] 0) :
    box g u x = 0 := by
  rw [box_congr h, box_zero]

lemma box_eq_zero_of_notMem_tsupport {u : E n → ℝ} {x : E n} (hx : x ∉ tsupport u) :
    box g u x = 0 :=
  box_eq_zero_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.1 hx)

theorem tsupport_box_subset (u : E n → ℝ) : tsupport (box g u) ⊆ tsupport u :=
  closure_minimal (fun _ hx => by_contra fun h => hx (box_eq_zero_of_notMem_tsupport h))
    (isClosed_tsupport u)

theorem hasCompactSupport_box {u : E n → ℝ} (hu : HasCompactSupport u) :
    HasCompactSupport (box g u) :=
  hu.mono' ((subset_tsupport _).trans (tsupport_box_subset (g := g) u))

/-! ### Linearity and smoothness -/

section Smooth

variable (hg : ∀ i j, ContDiff ℝ ∞ fun x => g x i j) (hdet : ∀ x, (g x).det ≠ 0)
include hg hdet

theorem contDiff_box {u : E n → ℝ} (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (box g u) := by
  have hρ : ContDiff ℝ ∞ fun x => (√|(g x).det|)⁻¹ :=
    (contDiff_sqrt_abs_det hg hdet).inv fun x => (Real.sqrt_pos.2 (abs_pos.2 (hdet x))).ne'
  rw [show box g u = fun x => -(√|(g x).det|)⁻¹ * ∑ j, d (flux g u j) x j from
    funext (box_eq_flux g u)]
  exact hρ.neg.mul (ContDiff.sum fun j _ => contDiff_d (contDiff_flux hg hdet hu j) j)

theorem box_linear {u v : E n → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (a b : ℝ)
    (x : E n) : box g (fun y => a * u y + b * v y) x = a * box g u x + b * box g v x := by
  have hdiff : ∀ {f : E n → ℝ}, ContDiff ℝ ∞ f → ∀ x, DifferentiableAt ℝ f x :=
    fun hf x => (hf.differentiable (by simp)) x
  have hd : ∀ y k, d (fun y => a * u y + b * v y) y k = a * d u y k + b * d v y k := by
    intro y k
    simp only [d_def]
    rw [fderiv_fun_add ((hdiff hu y).const_mul a) ((hdiff hv y).const_mul b),
      fderiv_const_mul (hdiff hu y), fderiv_const_mul (hdiff hv y)]
    simp
  have hflux : ∀ j, flux g (fun y => a * u y + b * v y) j =
      fun y => a * flux g u j y + b * flux g v j y := by
    intro j
    ext y
    simp only [flux_def, hd, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun k _ => by ring
  have hdflux : ∀ j, d (fun y => a * flux g u j y + b * flux g v j y) x j =
      a * d (flux g u j) x j + b * d (flux g v j) x j := by
    intro j
    simp only [d_def]
    rw [fderiv_fun_add ((hdiff (contDiff_flux hg hdet hu j) x).const_mul a)
      ((hdiff (contDiff_flux hg hdet hv j) x).const_mul b),
      fderiv_const_mul (hdiff (contDiff_flux hg hdet hu j) x),
      fderiv_const_mul (hdiff (contDiff_flux hg hdet hv j) x)]
    simp
  simp only [box_eq_flux, hflux, hdflux, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem box_sub {u v : E n → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (x : E n) :
    box g (fun y => u y - v y) x = box g u x - box g v x := by
  have := box_linear hg hdet hu hv 1 (-1) x
  simp only [one_mul, neg_one_mul, ← sub_eq_add_neg] at this
  exact this

theorem box_add {u v : E n → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (x : E n) :
    box g (fun y => u y + v y) x = box g u x + box g v x := by
  simpa using box_linear hg hdet hu hv 1 1 x

theorem box_const_mul {u : E n → ℝ} (hu : ContDiff ℝ ∞ u) (a : ℝ) (x : E n) :
    box g (fun y => a * u y) x = a * box g u x := by
  simpa using box_linear hg hdet hu hu a 0 x

end Smooth

/-! ### Green's identity on `ℝ^{1+n}` -/

/-- The divergence of `X = u J(ϑ) - ϑ J(u)`, with `J` the flux, is
`|det g|^{1/2} (ϑ □_g u - u □_g ϑ)`. -/
theorem sum_d_green_field (hg : ∀ i j, ContDiff ℝ ∞ fun x => g x i j)
    (hsymm : ∀ x, (g x)ᵀ = g x) (hdet : ∀ x, (g x).det ≠ 0) {u ϑ : E n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hϑ : ContDiff ℝ ∞ ϑ) (x : E n) :
    ∑ j, d (fun y => u y * flux g ϑ j y - ϑ y * flux g u j y) x j =
      ϑ x * box g u x * √|(g x).det| - u x * box g ϑ x * √|(g x).det| := by
  have hdiff : ∀ {f : E n → ℝ}, ContDiff ℝ ∞ f → ∀ x, DifferentiableAt ℝ f x :=
    fun hf x => (hf.differentiable (by simp)) x
  have hsymm' : ∀ x j k, (g x)⁻¹ j k = (g x)⁻¹ k j := fun x j k => by
    rw [← Matrix.transpose_apply (g x)⁻¹, Matrix.transpose_nonsing_inv, hsymm]
  have hcross : ∑ j, d u x j * flux g ϑ j x = ∑ j, d ϑ x j * flux g u j x := by
    simp only [flux_def, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [hsymm' x j k]
    ring
  have hb1 := sqrt_abs_det_mul_box (hdet x) ϑ
  have hb2 := sqrt_abs_det_mul_box (hdet x) u
  rw [Finset.sum_congr rfl fun j _ => by
    rw [d_sub (hdiff (hu.mul (contDiff_flux hg hdet hϑ j)) x)
      (hdiff (hϑ.mul (contDiff_flux hg hdet hu j)) x),
      d_mul (hdiff hu x) (hdiff (contDiff_flux hg hdet hϑ j) x),
      d_mul (hdiff hϑ x) (hdiff (contDiff_flux hg hdet hu j) x)]]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  linear_combination hcross + u x * hb1 - ϑ x * hb2

lemma flux_eventuallyEq_zero {u : E n → ℝ} {x : E n} (hx : x ∉ tsupport u) (j : Fin (n + 1)) :
    flux g u j =ᶠ[𝓝 x] 0 := by
  have := flux_eventuallyEq (g := g) (notMem_tsupport_iff_eventuallyEq.1 hx) j
  refine this.trans (Eventually.of_forall fun y => ?_)
  simp [flux_def, d_def]

/-- The divergence of a compactly supported `C¹` vector field integrates to zero. -/
theorem integral_sum_d_eq_zero (X : Fin (n + 1) → E n → ℝ) (hX : ∀ j, ContDiff ℝ 1 (X j))
    {K : Set (E n)} (hK : IsCompact K) (h0 : ∀ j, ∀ x ∉ K, X j =ᶠ[𝓝 x] 0) :
    ∫ x, ∑ j, d (X j) x j = 0 := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  set a : Fin (n + 1) → ℝ := fun _ => -(R + 1)
  set b : Fin (n + 1) → ℝ := fun _ => R + 1
  set B : Set (E n) := ofLp ⁻¹' Icc a b
  have hball : Metric.ball (0 : E n) (R + 1) ⊆ B := by
    intro x hx
    rw [Metric.mem_ball, dist_zero_right] at hx
    refine ⟨fun i => ?_, fun i => ?_⟩ <;>
    · have := (PiLp.norm_apply_le x i).trans hx.le
      rw [Real.norm_eq_abs, abs_le] at this
      simp only [a, b]
      linarith [this.1, this.2]
  have hKB : K ⊆ interior B := fun x hx =>
    interior_maximal hball Metric.isOpen_ball
      (Metric.mem_ball.2 (lt_of_le_of_lt (Metric.mem_closedBall.1 (hR hx)) (by linarith)))
  have hdiv : ∀ x ∉ K, ∑ j, d (X j) x j = 0 := fun x hx =>
    Finset.sum_eq_zero fun j _ => by rw [d_congr (h0 j x hx)]; simp [d_def]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := B) fun x hx =>
    hdiv x fun hxK => hx (interior_subset (hKB hxK))]
  refine integral_divergence_box_eq_zero X hX fun j x hx => (h0 j x fun hxK => ?_).eq_of_nhds
  rw [frontier, Set.mem_sdiff] at hx
  exact hx.2 (hKB hxK)

/-- **Green's identity on `ℝ^{1+n}`**, when the supports of `u` and `ϑ` meet in a compact set. -/
theorem integral_mul_box_comm_of_isCompact (hg : ∀ i j, ContDiff ℝ ∞ fun x => g x i j)
    (hsymm : ∀ x, (g x)ᵀ = g x) (hdet : ∀ x, (g x).det ≠ 0) {u ϑ : E n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hϑ : ContDiff ℝ ∞ ϑ) (hK : IsCompact (tsupport u ∩ tsupport ϑ)) :
    ∫ x, u x * box g ϑ x * √|(g x).det| = ∫ x, ϑ x * box g u x * √|(g x).det| := by
  set X : Fin (n + 1) → E n → ℝ := fun j y => u y * flux g ϑ j y - ϑ y * flux g u j y
  have hXs : ∀ j, ContDiff ℝ ∞ (X j) := fun j =>
    (hu.mul (contDiff_flux hg hdet hϑ j)).sub (hϑ.mul (contDiff_flux hg hdet hu j))
  have hX0 : ∀ j, ∀ x ∉ tsupport u ∩ tsupport ϑ, X j =ᶠ[𝓝 x] 0 := by
    intro j x hx
    rcases not_and_or.1 hx with h | h
    · filter_upwards [notMem_tsupport_iff_eventuallyEq.1 h, flux_eventuallyEq_zero (g := g) h j]
        with y h1 h2
      simp [X, h1, h2]
    · filter_upwards [notMem_tsupport_iff_eventuallyEq.1 h, flux_eventuallyEq_zero (g := g) h j]
        with y h1 h2
      simp [X, h1, h2]
  have hint := integral_sum_d_eq_zero X (fun j => (hXs j).of_le (by simp)) hK hX0
  simp only [X, sum_d_green_field hg hsymm hdet hu hϑ] at hint
  have hρ := (contDiff_sqrt_abs_det hg hdet).continuous
  have hcs : ∀ {f h : E n → ℝ}, ContDiff ℝ ∞ f → ContDiff ℝ ∞ h →
      (∀ x ∉ tsupport u ∩ tsupport ϑ, f x * box g h x = 0) →
      Integrable (fun x => f x * box g h x * √|(g x).det|) := by
    intro f h hf hh hfh
    refine ((hf.continuous.mul (continuous_box hg hdet hh)).mul hρ).integrable_of_hasCompactSupport
      (HasCompactSupport.intro hK fun x hx => by simp [hfh x hx])
  have hz1 : ∀ x ∉ tsupport u ∩ tsupport ϑ, ϑ x * box g u x = 0 := by
    intro x hx
    rcases not_and_or.1 hx with hx | hx
    · simp [box_eq_zero_of_notMem_tsupport hx]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hz2 : ∀ x ∉ tsupport u ∩ tsupport ϑ, u x * box g ϑ x = 0 := by
    intro x hx
    rcases not_and_or.1 hx with hx | hx
    · simp [image_eq_zero_of_notMem_tsupport hx]
    · simp [box_eq_zero_of_notMem_tsupport hx]
  rw [integral_sub (hcs hϑ hu hz1) (hcs hu hϑ hz2), sub_eq_zero] at hint
  exact hint.symm

end

end LorentzianCalderon
