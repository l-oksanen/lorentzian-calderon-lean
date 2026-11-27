module

public import LorentzianCalderon.Geometry.Exp

public section

/-!
# Extension of causal geodesics

A future-directed causal geodesic on `(a, b)` with a limit `x` at `b` extends as a geodesic
beyond `b` (`Facts.geodesic_extension`). With the linear function `τ = -g_x(·, Y x)`, the
velocity satisfies `c ‖γ̇‖ ≤ τ(γ̇)` near `x`, and the geodesic equation gives
`(τ γ̇)' ≤ K (τ γ̇)²`, so `τ(γ̇) e^{-K τ(γ)}` decreases and `γ̇` stays bounded. At a cluster point
`v` of `γ̇` at `b`, geodesics with initial data near `(x, v)` exist on a common interval
(`exists_isGeodesic_nhds`), and one of them continues `γ`.
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Set Filter

variable {n : ℕ} {g : MatrixField n} {Y : E n → E n} {γ : ℝ → E n} {I : Set ℝ}

/-- Being a geodesic is a local property. -/
theorem isGeodesic_of_locally {U : Set ℝ} (hU : IsOpen U)
    (h : ∀ t ∈ U, ∃ (σ : ℝ → E n) (J : Set ℝ), IsGeodesic g σ J ∧ t ∈ J ∧ γ =ᶠ[𝓝 t] σ) :
    IsGeodesic g γ U := by
  refine ⟨hU, fun t ht => ?_, fun t ht k => ?_⟩
  · obtain ⟨σ, J, hσ, htJ, he⟩ := h t ht
    exact ((hσ.smooth.contDiffAt (hσ.isOpen.mem_nhds htJ)).congr_of_eventuallyEq
      he).contDiffWithinAt
  · obtain ⟨σ, J, hσ, htJ, he⟩ := h t ht
    rw [he.deriv.deriv_eq, he.deriv_eq, he.eq_of_nhds]
    exact hσ.equation t htJ k

theorem inExpDomain_zero (y : E n) : InExpDomain g y 0 := by
  simpa using (isGeodesic_const (g := g) y).inExpDomain (subset_univ _)

theorem christoffelQuad_smul (z v : E n) (s : ℝ) :
    christoffelQuad g z (s • v) = (s * s) • christoffelQuad g z v := by
  ext k
  simp only [christoffelQuad_apply, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem continuous_christoffelQuad (hg : IsSpacetime g Y) :
    Continuous fun p : E n × E n => christoffelQuad g p.1 p.2 := by
  have h := continuous_snd.comp (contDiff_geodesicSpray hg).continuous
  convert h.neg using 1
  funext p
  simp [geodesicSpray_def]

/-- `g_x(Γ(z)(v, v), N)` is quadratically bounded for `z` in a compact set. -/
theorem exists_abs_form_christoffelQuad_le (hg : IsSpacetime g Y) (x N : E n) {K : Set (E n)}
    (hK : IsCompact K) :
    ∃ C, ∀ z ∈ K, ∀ v, |form (g x) (christoffelQuad g z v) N| ≤ C * ‖v‖ ^ 2 := by
  have hc : Continuous fun p : E n × E n => form (g x) (christoffelQuad g p.1 p.2) N :=
    (continuous_form hg).comp
      (continuous_const.prodMk ((continuous_christoffelQuad hg).prodMk continuous_const))
  obtain ⟨C, hC⟩ :=
    (hK.prod (isCompact_sphere (0 : E n) 1)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, fun z hz v => ?_⟩
  rcases eq_or_ne v 0 with rfl | hv
  · have : christoffelQuad g z 0 = 0 := by simpa using christoffelQuad_smul (g := g) z 0 0
    simp [this]
  have hn := norm_pos_iff.2 hv
  have hu : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : E n) 1 := by simp [norm_smul, hn.ne']
  have hb := hC (z, ‖v‖⁻¹ • v) ⟨hz, hu⟩
  have heq : christoffelQuad g z v = (‖v‖ * ‖v‖) • christoffelQuad g z (‖v‖⁻¹ • v) := by
    rw [christoffelQuad_smul, smul_smul,
      show ‖v‖ * ‖v‖ * (‖v‖⁻¹ * ‖v‖⁻¹) = 1 by field_simp, one_smul]
  rw [heq, form_smul_left, abs_mul, abs_of_nonneg (by positivity)]
  rw [Real.norm_eq_abs] at hb
  exact (mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq (by ring)

/-- Near `x`, future-directed causal vectors `v` satisfy `c ‖v‖ ≤ -g_x(v, Y x)`. -/
theorem exists_mul_norm_le_form (hg : IsSpacetime g Y) (x : E n) :
    ∃ r > 0, ∃ c > 0, ∀ z ∈ Metric.closedBall x r, ∀ v, IsFutureCausal g Y z v →
      c * ‖v‖ ≤ -form (g x) v (Y x) := by
  by_contra! h
  have hk : ∀ k : ℕ, (0 : ℝ) < 1 / (k + 1) := fun k => by positivity
  choose z hz v hv hlt using fun k : ℕ => h _ (hk k) _ (hk k)
  set u : ℕ → E n := fun k => ‖v k‖⁻¹ • v k
  have hvn : ∀ k, 0 < ‖v k‖ := fun k => norm_pos_iff.2 (hv k).ne_zero
  have hu1 : ∀ k, u k ∈ Metric.sphere (0 : E n) 1 := fun k => by
    simp [u, norm_smul, (hvn k).ne']
  have huc : ∀ k, IsFutureCausal g Y (z k) (u k) := fun k => (hv k).smul (inv_pos.2 (hvn k))
  have hul : ∀ k, -form (g x) (u k) (Y x) < 1 / (k + 1) := fun k => by
    have h' := mul_lt_mul_of_pos_left (hlt k) (inv_pos.2 (hvn k))
    rw [mul_comm (1 / ((k : ℝ) + 1)), ← mul_assoc, inv_mul_cancel₀ (hvn k).ne', one_mul] at h'
    simp only [u, form_smul_left]
    linarith
  obtain ⟨u₀, hu₀, φ, hφ, hlim⟩ := (isCompact_sphere (0 : E n) 1).tendsto_subseq hu1
  have hk0 : Tendsto (fun k => 1 / ((φ k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have hzφ : Tendsto (fun k => z (φ k)) atTop (𝓝 x) :=
    tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg)
      (fun k => Metric.mem_closedBall.1 (hz (φ k))) hk0)
  have hYc : Continuous Y := hg.globallyHyperbolic.timeOrientation.continuous
  have hA : Tendsto (fun k => form (g (z (φ k))) (u (φ k)) (u (φ k))) atTop
      (𝓝 (form (g x) u₀ u₀)) := by
    have h := ((continuous_form hg).tendsto (x, u₀, u₀)).comp
      (hzφ.prodMk_nhds (hlim.prodMk_nhds hlim))
    simp only [Function.comp_def] at h
    exact h
  have hB : Tendsto (fun k => form (g (z (φ k))) (u (φ k)) (Y (z (φ k)))) atTop
      (𝓝 (form (g x) u₀ (Y x))) := by
    have h := ((continuous_form hg).tendsto (x, u₀, Y x)).comp
      (hzφ.prodMk_nhds (hlim.prodMk_nhds ((hYc.tendsto x).comp hzφ)))
    simp only [Function.comp_def] at h
    exact h
  have hC : Tendsto (fun k => -form (g x) (u (φ k)) (Y x)) atTop
      (𝓝 (-form (g x) u₀ (Y x))) := by
    have h := ((continuous_form hg).tendsto (x, u₀, Y x)).comp
      ((tendsto_const_nhds (x := x)).prodMk_nhds
        (hlim.prodMk_nhds (tendsto_const_nhds (x := Y x))))
    simp only [Function.comp_def] at h
    exact h.neg
  have h1 : form (g x) u₀ u₀ ≤ 0 := le_of_tendsto' hA fun k => (huc _).causal
  have h3 : -form (g x) u₀ (Y x) ≤ 0 := le_of_tendsto_of_tendsto' hC hk0 fun k => (hul _).le
  have h2 : form (g x) u₀ (Y x) ≤ 0 := le_of_tendsto' hB fun k => (huc _).future.le
  have hu0 : u₀ ≠ 0 := by
    rintro rfl
    simp at hu₀
  exact (hg.lorentzian x).form_ne_zero h1 hu0 (hg.globallyHyperbolic.timeOrientation.timelike x)
    (by linarith)

/-- Geodesics with initial data near `(x, v)` exist on a common interval `(-δ, δ)`. -/
theorem exists_isGeodesic_nhds (hg : IsSpacetime g Y) (x v : E n) :
    ∃ δ > 0, ∀ᶠ z in 𝓝 (x, v), ∃ σ : ℝ → E n,
      IsGeodesic g σ (Ioo (-δ) δ) ∧ σ 0 = z.1 ∧ deriv σ 0 = z.2 := by
  obtain ⟨X, hS, -, -⟩ := exists_sprayFlow hg
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), InExpDomain g x (s • v) :=
    (by fun_prop : Continuous fun s : ℝ => (x, s • v)).continuousAt.preimage_mem_nhds
      ((isOpen_expDomain hg).mem_nhds (by simpa using inExpDomain_zero (g := g) x))
  obtain ⟨s, hs, hs0⟩ := ((hev.filter_mono (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))).and
    (self_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0))).exists
  have hs0' : 0 < s := hs0
  obtain ⟨ε, hε, hρ, -, hρ0, hρ'⟩ := hs.isGeodesic_expMap_smul hg
  set δ := s * min ε 1 / 2 with hδdef
  have hm := min_le_left ε 1
  have hm' := min_le_right ε 1
  have hδ : 0 < δ := by positivity
  have hsub : Icc (-δ) δ ⊆ (fun t => s⁻¹ * t + 0) ⁻¹' Ioo (-ε) (1 + ε) := fun t ht => by
    have h1 : s⁻¹ * δ = min ε 1 / 2 := by
      rw [hδdef]
      field_simp
    have h2 := mul_le_mul_of_nonneg_left ht.2 (inv_pos.2 hs0').le
    have h3 := mul_le_mul_of_nonneg_left ht.1 (inv_pos.2 hs0').le
    rw [mul_neg, h1] at h3
    rw [h1] at h2
    simp only [mem_preimage, add_zero, mem_Ioo]
    constructor <;> linarith
  have h0 : s⁻¹ * 0 + 0 ∈ Ioo (-ε) (1 + ε) := by
    simp only [mul_zero, add_zero, mem_Ioo]
    constructor <;> linarith
  set σ : ℝ → E n := fun t => expMap g x ((s⁻¹ * t + 0) • s • v) with hσdef
  have hσ : IsGeodesic g σ _ := hρ.comp_affine s⁻¹ 0
  have hσ0 : σ 0 = x := by simpa [hσdef] using hρ0
  have hσ'0 : deriv σ 0 = v := by
    rw [hσdef, hρ.deriv_comp_affine h0, mul_zero, add_zero, hρ', smul_smul,
      inv_mul_cancel₀ hs0'.ne', one_smul]
  have hsol := hσ.isODESolution hsub ordConnected_Icc 0
  have h0I : (0 : ℝ) ∈ Icc (-δ) δ := ⟨by linarith, by linarith⟩
  have ha := mem_sprayDomain hsol (t := -δ) ⟨le_rfl, by linarith⟩ h0I
  have hb := mem_sprayDomain hsol (t := δ) ⟨by linarith, le_rfl⟩ h0I
  simp only [hσ0, hσ'0] at ha hb
  have hN : IsOpen { p : E n × E n | ((-δ : ℝ), (0 : ℝ), p, (0 : ℝ)) ∈ sprayDomain g ∧
      (δ, (0 : ℝ), p, (0 : ℝ)) ∈ sprayDomain g } :=
    (hS.preimage (by fun_prop)).inter (hS.preimage (by fun_prop))
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hN.mem_nhds ⟨ha, hb⟩] with p hp
  exact exists_isGeodesic_of_mem_sprayDomain hg (by linarith) hδ hp.1 hp.2

/-- A future-directed causal geodesic on `(a, b)` has bounded velocity near `b` if it has a
limit at `b`. -/
theorem IsGeodesic.exists_bound_deriv (hg : IsSpacetime g Y) {a b : ℝ} (hab : a < b)
    (hγ : IsGeodesic g γ (Ioo a b)) (hc : ∀ t ∈ Ioo a b, IsFutureCausal g Y (γ t) (deriv γ t))
    {x : E n} (hlim : Tendsto γ (𝓝[<] b) (𝓝 x)) :
    ∃ M, ∀ᶠ t in 𝓝[<] b, deriv γ t ∈ Metric.closedBall (0 : E n) M := by
  obtain ⟨r, hr, c, hc0, hcone⟩ := exists_mul_norm_le_form hg x
  obtain ⟨C, hC⟩ := exists_abs_form_christoffelQuad_le hg x (Y x) (isCompact_closedBall x r)
  obtain ⟨l, hl, hlsub⟩ := mem_nhdsLT_iff_exists_Ico_subset.1
    (hlim.eventually (Metric.closedBall_mem_nhds x hr))
  set t₀ := max l ((a + b) / 2)
  have ht₀ : t₀ ∈ Ioo a b := ⟨by simp only [t₀]; exact lt_max_of_lt_right (by linarith),
    max_lt hl (by linarith)⟩
  have hball : ∀ t ∈ Ico t₀ b, γ t ∈ Metric.closedBall x r := fun t ht =>
    hlsub ⟨(le_max_left _ _).trans ht.1, ht.2⟩
  have hIco : Ico t₀ b ⊆ Ioo a b := fun t ht => ⟨ht₀.1.trans_le ht.1, ht.2⟩
  set ℓ : E n →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    { toFun := fun v => -form (g x) v (Y x)
      map_add' := fun v w => by simp only [form_add_left]; ring
      map_smul' := fun s v => by simp }
  have hℓ : ∀ v, ℓ v = -form (g x) v (Y x) := fun _ => rfl
  set u : ℝ → ℝ := fun t => ℓ (deriv γ t)
  set p : ℝ → ℝ := fun t => ℓ (γ t)
  set F : ℝ → ℝ := fun t => form (g x) (christoffelQuad g (γ t) (deriv γ t)) (Y x)
  have hu' : ∀ t ∈ Ioo a b, HasDerivAt u (F t) t := fun t ht => by
    have := ℓ.hasFDerivAt.comp_hasDerivAt t (hγ.hasDerivAt_deriv ht)
    rwa [hγ.deriv_deriv ht, hℓ, form_neg_left, neg_neg] at this
  have hp' : ∀ t ∈ Ioo a b, HasDerivAt p (u t) t := fun t ht =>
    ℓ.hasFDerivAt.comp_hasDerivAt t (hγ.hasDerivAt ht)
  have hcu : ∀ t ∈ Ico t₀ b, c * ‖deriv γ t‖ ≤ u t := fun t ht =>
    hcone _ (hball t ht) _ (hc t (hIco ht))
  set K := max C 0 / c ^ 2
  have hK : 0 ≤ K := by positivity
  have hF : ∀ t ∈ Ico t₀ b, F t ≤ K * u t ^ 2 := fun t ht => by
    have h1 := (le_abs_self _).trans (hC _ (hball t ht) (deriv γ t))
    have h2 : 0 ≤ c * ‖deriv γ t‖ := by positivity
    have h3 : (c * ‖deriv γ t‖) ^ 2 ≤ u t ^ 2 := pow_le_pow_left₀ h2 (hcu t ht) 2
    have h4 : C * ‖deriv γ t‖ ^ 2 ≤ K * (c * ‖deriv γ t‖) ^ 2 := by
      have e : K * (c * ‖deriv γ t‖) ^ 2 = max C 0 * ‖deriv γ t‖ ^ 2 := by
        simp only [K]
        field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    exact h1.trans (h4.trans (mul_le_mul_of_nonneg_left h3 hK))
  set h : ℝ → ℝ := fun t => u t * Real.exp (-(K * p t))
  have hh' : ∀ t ∈ Ioo a b, HasDerivAt h
      (F t * Real.exp (-(K * p t)) + u t * (Real.exp (-(K * p t)) * -(K * u t))) t :=
    fun t ht => (hu' t ht).mul (((hp' t ht).const_mul K).neg.exp)
  have hanti : AntitoneOn h (Ico t₀ b) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ico _ _)
      (f' := fun t => F t * Real.exp (-(K * p t)) + u t * (Real.exp (-(K * p t)) * -(K * u t)))
      (fun t ht =>
      (hh' t (hIco ht)).continuousAt.continuousWithinAt) (fun t ht => ?_) (fun t ht => ?_)
    · rw [interior_Ico] at ht
      exact (hh' t (hIco (Ioo_subset_Ico_self ht))).hasDerivWithinAt
    · rw [interior_Ico] at ht
      have := hF t (Ioo_subset_Ico_self ht)
      have he := Real.exp_pos (-(K * p t))
      nlinarith
  set P := ‖ℓ‖ * (‖x‖ + r)
  have hP : ∀ t ∈ Ico t₀ b, |p t| ≤ P := fun t ht => by
    refine (ℓ.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    have := Metric.mem_closedBall.1 (hball t ht)
    rw [dist_eq_norm] at this
    calc ‖γ t‖ = ‖x + (γ t - x)‖ := by rw [add_sub_cancel]
      _ ≤ ‖x‖ + ‖γ t - x‖ := norm_add_le _ _
      _ ≤ ‖x‖ + r := by linarith
  have ht₀' : t₀ ∈ Ico t₀ b := ⟨le_rfl, ht₀.2⟩
  refine ⟨u t₀ * Real.exp (2 * K * P) / c, ?_⟩
  filter_upwards [Ico_mem_nhdsLT ht₀.2] with t ht
  rw [mem_closedBall_zero_iff, le_div_iff₀ hc0]
  have h1 := hanti ht₀' ht ht.1
  simp only [h] at h1
  have h2 : u t ≤ u t₀ * Real.exp (K * (p t - p t₀)) := by
    have e1 : Real.exp (K * (p t - p t₀)) = Real.exp (-(K * p t₀)) * Real.exp (K * p t) := by
      rw [← Real.exp_add]
      ring_nf
    have e2 : u t = u t * Real.exp (-(K * p t)) * Real.exp (K * p t) := by
      rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    rw [e1, e2, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  have h3 : Real.exp (K * (p t - p t₀)) ≤ Real.exp (2 * K * P) := by
    refine Real.exp_le_exp.2 ?_
    have := hP t ht
    have := hP t₀ ht₀'
    rw [abs_le] at *
    nlinarith
  have hu0 : 0 ≤ u t₀ := (by positivity : 0 ≤ c * ‖deriv γ t₀‖).trans (hcu t₀ ht₀')
  nlinarith [hcu t ht, mul_le_mul_of_nonneg_left h3 hu0]

/-- A future-directed causal geodesic on `(a, b)` with a limit at `b` extends as a geodesic
beyond `b`. O'Neill, Semi-Riemannian geometry, Lemma 5.8, p. 130. O'Neill assumes that the
velocity converges along a sequence of times; for causal geodesics this follows from the
convergence of `γ`. -/
theorem Facts.geodesic_extension (hg : IsSpacetime g Y) {γ : ℝ → E n} {a b : ℝ} (hab : a < b)
    (hγ : IsGeodesic g γ (Ioo a b)) (hc : ∀ t ∈ Ioo a b, IsFutureCausal g Y (γ t) (deriv γ t))
    {x : E n} (hlim : Tendsto γ (𝓝[<] b) (𝓝 x)) :
    ∃ (γ' : ℝ → E n) (J : Set ℝ), IsGeodesic g γ' J ∧ Ioc a b ⊆ J ∧ EqOn γ γ' (Ioo a b) := by
  obtain ⟨M, hM⟩ := hγ.exists_bound_deriv hg hab hc hlim
  obtain ⟨v, -, hv⟩ := (isCompact_closedBall (0 : E n) M).exists_mapClusterPt
    (f := 𝓝[<] b) (u := deriv γ) (le_principal_iff.2 hM)
  obtain ⟨δ, hδ, hN⟩ := exists_isGeodesic_nhds hg x v
  rw [nhds_prod_eq] at hN
  obtain ⟨pa, hpa, pb, hpb, hP⟩ := eventually_prod_iff.1 hN
  have hfr : ∃ᶠ t in 𝓝[<] b, ∃ σ : ℝ → E n,
      IsGeodesic g σ (Ioo (-δ) δ) ∧ σ 0 = γ t ∧ deriv σ 0 = deriv γ t :=
    ((hv.frequently hpb).and_eventually (hlim.eventually hpa)).mono fun t ht => hP ht.2 ht.1
  have hlt : max a (b - δ / 2) < b := max_lt hab (by linarith)
  obtain ⟨t₁, ⟨σ₁, hσ₁, hσ₁0, hσ₁'⟩, ht₁⟩ := (hfr.and_eventually (Ioo_mem_nhdsLT hlt)).exists
  have ha₁ : a < t₁ := (le_max_left _ _).trans_lt ht₁.1
  have hb₁ : b - δ / 2 < t₁ := (le_max_right _ _).trans_lt ht₁.1
  set σ : ℝ → E n := fun t => σ₁ (1 * t + -t₁)
  have hσ : IsGeodesic g σ (Ioo (t₁ - δ) (t₁ + δ)) :=
    (hσ₁.comp_affine 1 (-t₁)).mono (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      isOpen_Ioo
  have h0 : 1 * t₁ + -t₁ ∈ Ioo (-δ) δ := by
    simp only [one_mul, add_neg_cancel, mem_Ioo]
    constructor <;> linarith
  have hσt₁ : γ t₁ = σ t₁ := by simp [σ, hσ₁0]
  have hσ't₁ : deriv γ t₁ = deriv σ t₁ := by
    rw [hσ₁.deriv_comp_affine h0]
    simp [hσ₁']
  set J₀ := Ioo (max a (t₁ - δ)) b
  have heq := (IsGeodesic.eqOn hg hγ hσ (J := J₀)
    (fun t ht => ⟨(le_max_left _ _).trans_lt ht.1, ht.2⟩)
    (fun t ht => ⟨(le_max_right _ _).trans_lt ht.1, by linarith [ht.2]⟩) ordConnected_Ioo
    ⟨max_lt ha₁ (by linarith), ht₁.2⟩ hσt₁ hσ't₁).1
  classical
  refine ⟨fun t => if t < b then γ t else σ t, Ioo a (t₁ + δ), ?_, fun t ht =>
    ⟨ht.1, by linarith [ht.2]⟩, fun t ht => by simp [ht.2]⟩
  refine isGeodesic_of_locally isOpen_Ioo fun t ht => ?_
  by_cases htb : t < b
  · refine ⟨γ, Ioo a b, hγ, ⟨ht.1, htb⟩, ?_⟩
    filter_upwards [Iio_mem_nhds htb] with s hs
    simp [show s < b from hs]
  · have hlt' : max a (t₁ - δ) < t := (max_lt ha₁ (by linarith)).trans_le
      (ht₁.2.le.trans (not_lt.1 htb))
    refine ⟨σ, _, hσ, ⟨by linarith [le_max_right a (t₁ - δ)], ht.2⟩, ?_⟩
    filter_upwards [Ioi_mem_nhds hlt'] with s hs
    by_cases hsb : s < b
    · simp only [hsb, ↓reduceIte]
      exact heq ⟨hs, hsb⟩
    · simp [hsb]

/-- `exp_{γ(t)} (s k γ̇(t)) = γ(k s + t)`, as long as `γ` is defined in between. -/
theorem IsGeodesic.expMap_smul_smul_deriv (hg : IsSpacetime g Y) (hγ : IsGeodesic g γ I)
    {t k s : ℝ} (h : ∀ τ ∈ uIcc 0 s, k * τ + t ∈ I) :
    InExpDomain g (γ t) (s • k • deriv γ t) ∧
      expMap g (γ t) (s • k • deriv γ t) = γ (k * s + t) := by
  have h0 : k * 0 + t ∈ I := h 0 left_mem_uIcc
  have := (hγ.comp_affine k t).expMap_smul_eq hg (t := s) h
  rw [hγ.deriv_comp_affine h0] at this
  simpa using this

/-- The ray `r ↦ exp_y (r w)` is a geodesic on its whole domain, with velocity `w` at `0`. -/
theorem isGeodesic_expMap_smul (hg : IsSpacetime g Y) (y w : E n) :
    IsGeodesic g (fun r : ℝ => expMap g y (r • w)) {r | InExpDomain g y (r • w)} ∧
      deriv (fun r : ℝ => expMap g y (r • w)) 0 = w := by
  set U := {r : ℝ | InExpDomain g y (r • w)}
  have hU : IsOpen U :=
    (isOpen_expDomain hg).preimage (by fun_prop : Continuous fun r : ℝ => (y, r • w))
  have loc : ∀ r₁ ∈ U, r₁ ≠ 0 → ∃ J : Set ℝ,
      IsGeodesic g (fun r : ℝ => expMap g y (r • w)) J ∧
      0 ∈ J ∧ r₁ ∈ J ∧ deriv (fun r : ℝ => expMap g y (r • w)) 0 = w := by
    intro r₁ hr₁ hne
    obtain ⟨ε, hε, hσ, -, -, hσ'⟩ := InExpDomain.isGeodesic_expMap_smul hg hr₁
    have heq : (fun r : ℝ => expMap g y (r • w)) =
        fun r => expMap g y ((r₁⁻¹ * r + 0) • r₁ • w) := by
      funext r
      rw [smul_smul]
      congr 2
      field_simp
      ring
    have h0 : r₁⁻¹ * 0 + 0 ∈ Ioo (-ε) (1 + ε) := by
      simp only [mul_zero, add_zero, mem_Ioo]
      constructor <;> linarith
    have h1 : r₁⁻¹ * r₁ + 0 ∈ Ioo (-ε) (1 + ε) := by
      rw [inv_mul_cancel₀ hne, add_zero, mem_Ioo]
      constructor <;> linarith
    refine ⟨_, heq ▸ hσ.comp_affine r₁⁻¹ 0, h0, h1, ?_⟩
    rw [heq, hσ.deriv_comp_affine h0, mul_zero, add_zero, hσ', smul_smul, inv_mul_cancel₀ hne,
      one_smul]
  have h0U : (0 : ℝ) ∈ U := by simpa [U] using inExpDomain_zero (g := g) y
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU 0 h0U
  have hδU : δ / 2 ∈ U := hball <| by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]
    linarith
  obtain ⟨J, -, -, -, hderiv⟩ := loc _ hδU (by positivity)
  refine ⟨isGeodesic_of_locally hU fun r hr => ?_, hderiv⟩
  rcases eq_or_ne r 0 with rfl | hr0
  · obtain ⟨J, hJ, h0J, -, -⟩ := loc _ hδU (by positivity)
    exact ⟨_, J, hJ, h0J, EventuallyEq.rfl⟩
  · obtain ⟨J, hJ, -, hrJ, -⟩ := loc r hr hr0
    exact ⟨_, J, hJ, hrJ, EventuallyEq.rfl⟩

end

end LorentzianCalderon
