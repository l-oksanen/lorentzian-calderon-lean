module

public import LorentzianCalderon.Geometry.Lagrangian

public section

/-!
# The Gauss lemma

`g(d(exp_y)_w w, d(exp_y)_w ξ) = g_y(w, ξ)` (`Facts.gauss`), from the variation
`Φ(t, s) = exp_y (t (w + s ξ))` through geodesics: `t ↦ g(∂ₜΦ, ∂ₛΦ)` at `s = 0` has derivative
`½ ∂ₛ g(∂ₜΦ, ∂ₜΦ) = g_y(w, ξ)` by the geodesic equation, the symmetry of `∂ₜ∂ₛΦ`, and the
conservation of `g(∂ₜΦ, ∂ₜΦ) = g_y(w + s ξ, w + s ξ)` along each geodesic.
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Set Filter

variable {n : ℕ} {g : MatrixField n} {Y : E n → E n}

/-- The derivative `∂_X g(x)` of the metric coefficients in the direction `X`. -/
def metricDeriv (g : MatrixField n) (x X : E n) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j => fderiv ℝ (fun y => g y i j) x X

/-- The product rule for `r ↦ g(x(r))(u(r), v(r))`. -/
theorem hasDerivAt_form_comp (hg : IsSpacetime g Y) {x u v : ℝ → E n} {x' u' v' : E n}
    {r : ℝ} (hx : HasDerivAt x x' r) (hu : HasDerivAt u u' r) (hv : HasDerivAt v v' r) :
    HasDerivAt (fun s => form (g (x s)) (u s) (v s))
      (form (metricDeriv g (x r) x') (u r) (v r) + form (g (x r)) u' (v r) +
        form (g (x r)) (u r) v') r := by
  have hu' : ∀ i, HasDerivAt (fun s => u s i) (u' i) r := fun i =>
    (EuclideanSpace.proj i : E n →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt r hu
  have hv' : ∀ i, HasDerivAt (fun s => v s i) (v' i) r := fun i =>
    (EuclideanSpace.proj i : E n →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt r hv
  have hG : ∀ i j, HasDerivAt (fun s => g (x s) i j)
      (fderiv ℝ (fun y => g y i j) (x r) x') r := fun i j =>
    ((hg.smooth i j).differentiable (by simp) (x r)).hasFDerivAt.comp_hasDerivAt r hx
  have hq := HasDerivAt.sum (u := Finset.univ) fun i _ => HasDerivAt.sum (u := Finset.univ)
    fun j _ => ((hu' i).mul (hG i j)).mul (hv' j)
  simp only [form_def]
  convert hq using 1
  · funext s
    simp only [Finset.sum_apply, Pi.mul_apply]
  · simp only [metricDeriv, Matrix.of_apply, Pi.mul_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

/-- The Christoffel term paired with a vector:
`g(Γ(v, v), u) = (∂_v g)(v, u) - ½ (∂_u g)(v, v)`. -/
theorem form_christoffelQuad_left (hg : IsSpacetime g Y) (x v u : E n) :
    form (g x) (christoffelQuad g x v) u =
      form (metricDeriv g x v) v u - (1 / 2) * form (metricDeriv g x u) v v := by
  set P : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → ℝ := fun i j a => d (fun y => g y i j) x a
  set q : Fin (n + 1) → ℝ := fun l =>
    (1 / 2) * ∑ a, ∑ b, (P b l a + P a l b - P a b l) * v a * v b with hq
  have hΓ : (christoffelQuad g x v).ofLp = (g x)⁻¹ *ᵥ q := by
    funext k
    simp only [christoffelQuad_apply, christoffel_def, Matrix.mulVec, dotProduct, hq, P,
      Finset.mul_sum, Finset.sum_mul]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun l _ => by ring
  have hsymm : (g x)ᵀ = g x := (hg.lorentzian x).symm
  have hunit : IsUnit (g x).det := (hg.det_ne_zero x).isUnit
  have hform : form (g x) (christoffelQuad g x v) u = q ⬝ᵥ u.ofLp := by
    rw [form_eq_dotProduct, hΓ, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose,
      Matrix.vecMul_vecMul, Matrix.transpose_nonsing_inv, hsymm,
      Matrix.nonsing_inv_mul _ hunit, Matrix.vecMul_one]
  have hM : ∀ X i j, metricDeriv g x X i j = ∑ a, X a * P i j a := fun X i j =>
    fderiv_apply_eq_sum_d _ x X
  set S1 := ∑ l, ∑ a, ∑ b, P b l a * v a * v b * u l
  set S2 := ∑ l, ∑ a, ∑ b, P a l b * v a * v b * u l
  set S3 := ∑ l, ∑ a, ∑ b, P a b l * v a * v b * u l
  have e : q ⬝ᵥ u.ofLp = 1 / 2 * (S1 + S2 - S3) := by
    simp only [dotProduct, hq, S1, S2, S3, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun b _ => by ring
  have h2 : S2 = S1 :=
    sum_sum_sum_eq_of_equiv ⟨fun p => (p.1, p.2.2, p.2.1), fun p => (p.1, p.2.2, p.2.1),
      fun _ => rfl, fun _ => rfl⟩ fun _ => by simp only [Equiv.coe_fn_mk]; ring
  have hR1 : form (metricDeriv g x v) v u = S1 := by
    simp only [form_def, hM, S1, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine sum_sum_sum_eq_of_equiv ⟨fun p => (p.1, p.2.2, p.2.1), fun p => (p.1, p.2.2, p.2.1),
      fun _ => rfl, fun _ => rfl⟩ fun _ => by simp only [Equiv.coe_fn_mk]; ring
  have hR2 : form (metricDeriv g x u) v v = S3 := by
    simp only [form_def, hM, S3, Finset.sum_mul, Finset.mul_sum]
    exact sum_sum_sum_eq_of_equiv ⟨fun p => (p.2.2, p.1, p.2.1), fun p => (p.2.1, p.2.2, p.1),
      fun _ => rfl, fun _ => rfl⟩ fun _ => by simp only [Equiv.coe_fn_mk]; ring
  rw [hform, e, h2, hR1, hR2]
  ring

/-- The Gauss lemma. O'Neill, Semi-Riemannian geometry, Lemma 5.1, p. 127. -/
theorem Facts.gauss (hg : IsSpacetime g Y) {y w : E n} (hdom : InExpDomain g y w) (ξ : E n) :
    form (g (expMap g y w)) (fderiv ℝ (expMap g y) w w) (fderiv ℝ (expMap g y) w ξ) =
      form (g y) w ξ := by
  set e := expMap g y
  have hD : IsOpen {v : E n | InExpDomain g y v} :=
    (isOpen_expDomain hg).preimage (by fun_prop : Continuous fun v : E n => (y, v))
  have he : ContDiffOn ℝ ∞ e {v : E n | InExpDomain g y v} :=
    (contDiffOn_expMap hg).comp (by fun_prop : ContDiff ℝ ∞ fun v : E n => (y, v)).contDiffOn
      fun v hv => hv
  set φ : ℝ × ℝ → E n := fun p => p.1 • (w + p.2 • ξ)
  set U := φ ⁻¹' {v : E n | InExpDomain g y v}
  have hU : IsOpen U := hD.preimage (by fun_prop)
  set Φ : ℝ × ℝ → E n := fun p => e (φ p)
  have hΦ : ContDiffOn ℝ ∞ Φ U :=
    he.comp (by fun_prop : ContDiff ℝ ∞ φ).contDiffOn fun p hp => hp
  have hΦd : ∀ p ∈ U, HasFDerivAt Φ (fderiv ℝ Φ p) p := fun p hp =>
    ((hΦ.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hp)).hasFDerivAt
  have hΦ'd : ∀ p ∈ U, HasFDerivAt (fderiv ℝ Φ) (fderiv ℝ (fderiv ℝ Φ) p) p := fun p hp =>
    (((hΦ.fderiv_of_isOpen hU (m := 1) (by simp)).differentiableOn (by simp)).differentiableAt
      (hU.mem_nhds hp)).hasFDerivAt
  have hsymm : ∀ p ∈ U, IsSymmSndFDerivAt ℝ Φ p := fun p hp =>
    (hΦ.contDiffAt (hU.mem_nhds hp)).isSymmSndFDerivAt (by simp)
  have hlt : ∀ t s : ℝ, HasDerivAt (fun r : ℝ => (r, s)) ((1 : ℝ), (0 : ℝ)) t :=
    fun _ _ => (hasDerivAt_id _).prodMk (hasDerivAt_const _ _)
  have hls : ∀ t s : ℝ, HasDerivAt (fun r : ℝ => (t, r)) ((0 : ℝ), (1 : ℝ)) s :=
    fun _ _ => (hasDerivAt_const _ _).prodMk (hasDerivAt_id _)
  set T : ℝ × ℝ → E n := fun p => fderiv ℝ Φ p (1, 0)
  set S : ℝ × ℝ → E n := fun p => fderiv ℝ Φ p (0, 1)
  set A : ℝ → E n := fun t => fderiv ℝ (fderiv ℝ Φ) (t, 0) (1, 0) (0, 1)
  have hΦt : ∀ t s, (t, s) ∈ U → HasDerivAt (fun r => Φ (r, s)) (T (t, s)) t :=
    fun t s hp => by
      have h := (hΦd (t, s) hp).comp_hasDerivAt t (hlt t s)
      exact h
  have hΦs : ∀ t s, (t, s) ∈ U → HasDerivAt (fun r => Φ (t, r)) (S (t, s)) s :=
    fun t s hp => (hΦd (t, s) hp).comp_hasDerivAt s (hls t s)
  have hSt : ∀ t, (t, (0 : ℝ)) ∈ U → HasDerivAt (fun r => S (r, 0)) (A t) t := fun t ht =>
    (ContinuousLinearMap.apply ℝ (E n) ((0 : ℝ), (1 : ℝ))).hasFDerivAt.comp_hasDerivAt t
      ((hΦ'd _ ht).comp_hasDerivAt t (hlt t 0))
  have hTs : ∀ t, (t, (0 : ℝ)) ∈ U → HasDerivAt (fun s => T (t, s)) (A t) 0 := fun t ht =>
    ((ContinuousLinearMap.apply ℝ (E n) ((1 : ℝ), (0 : ℝ))).hasFDerivAt.comp_hasDerivAt
      (0 : ℝ) ((hΦ'd _ ht).comp_hasDerivAt (0 : ℝ) (hls t 0))).congr_deriv (hsymm _ ht _ _)
  obtain ⟨ε, hε, hγ, hγd, -, -⟩ := hdom.isGeodesic_expMap_smul hg
  have hΦ0 : ∀ t : ℝ, Φ (t, 0) = e (t • w) := fun t => by simp [Φ, φ]
  have hU0 : ∀ t ∈ Ioo (-ε) (1 + ε), (t, (0 : ℝ)) ∈ U := fun t ht => by
    simpa [U, φ] using hγd t ht
  have hTγ : ∀ t ∈ Ioo (-ε) (1 + ε), deriv (fun t => e (t • w)) t = T (t, 0) := fun t ht => by
    have := hΦt _ _ (hU0 t ht)
    simp only [hΦ0] at this
    exact this.deriv
  have hTt : ∀ t ∈ Ioo (-ε) (1 + ε), HasDerivAt (fun r => T (r, 0))
      (-christoffelQuad g (Φ (t, 0)) (T (t, 0))) t := fun t ht => by
    have hev : deriv (fun t => e (t • w)) =ᶠ[𝓝 t] fun r => T (r, 0) :=
      eventually_of_mem (isOpen_Ioo.mem_nhds ht) hTγ
    have := (hγ.hasDerivAt_deriv ht).congr_of_eventuallyEq hev.symm
    rw [hγ.deriv_deriv ht, hTγ t ht] at this
    rwa [hΦ0]
  have hS00 : S (0, 0) = 0 := by
    have := hΦs 0 0 (hU0 0 ⟨by linarith, by linarith⟩)
    have hc : (fun r => Φ (0, r)) = fun _ => e 0 := by
      funext r
      simp [Φ, φ]
    rw [hc] at this
    exact this.unique (hasDerivAt_const _ _)
  have hE : ∀ t ∈ Icc (0 : ℝ) 1, (fun s => form (g (Φ (t, s))) (T (t, s)) (T (t, s))) =ᶠ[𝓝 0]
      fun s => form (g y) (w + s • ξ) (w + s • ξ) := by
    intro t ht
    have hcont : Continuous fun s : ℝ => w + s • ξ := by fun_prop
    have hw : w + (0 : ℝ) • ξ ∈ {v : E n | InExpDomain g y v} := by simpa using hdom
    filter_upwards [hcont.continuousAt.preimage_mem_nhds (hD.mem_nhds hw)] with s hs
    obtain ⟨ε', hε', hγs, hγsd, h0s, h0s'⟩ := InExpDomain.isGeodesic_expMap_smul hg hs
    have hsub : Icc (0 : ℝ) 1 ⊆ Ioo (-ε') (1 + ε') := fun r hr =>
      ⟨by linarith [hr.1], by linarith [hr.2]⟩
    have hts : (t, s) ∈ U := hγsd t (hsub ht)
    have hd : deriv (fun r : ℝ => expMap g y (r • (w + s • ξ))) t = T (t, s) :=
      (hΦt t s hts).deriv
    have := hγs.form_deriv_eq hg hsub ordConnected_Icc ht ⟨le_rfl, zero_le_one⟩
    rw [h0s, h0s', hd] at this
    exact this
  set c := form (g y) w ξ
  set f : ℝ → ℝ := fun t => form (g (Φ (t, 0))) (T (t, 0)) (S (t, 0))
  have hf : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f c t := by
    intro t ht
    have ht' : t ∈ Ioo (-ε) (1 + ε) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have h0 := hU0 t ht'
    have h1 := hasDerivAt_form_comp hg (hΦt t 0 h0) (hTt t ht') (hSt t h0)
    have h2 := hasDerivAt_form_comp hg (hΦs t 0 h0) (hTs t h0) (hTs t h0)
    have hl : HasDerivAt (fun s : ℝ => w + s • ξ) ξ 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const ξ).const_add w
    have h3 := (hasDerivAt_form_self (hg.lorentzian y).symm hl).congr_of_eventuallyEq (hE t ht)
    have h4 := h3.unique h2
    beta_reduce at h1 h4
    rw [zero_smul, add_zero] at h4
    refine h1.congr_deriv ?_
    rw [form_neg_left, form_christoffelQuad_left hg,
      form_comm (hg.lorentzian (Φ (t, 0))).symm (A t) (T (t, 0))] at *
    linarith
  have hconst := constant_of_has_deriv_right_zero (f := fun t => f t - t * c) (a := 0) (b := 1)
    (fun t ht => ((hf t ht).sub ((hasDerivAt_id t).mul_const c)).continuousAt.continuousWithinAt)
    (fun t ht => by
      have := (hf t (Ico_subset_Icc_self ht)).sub ((hasDerivAt_id t).mul_const c)
      exact (this.congr_deriv (by ring)).hasDerivWithinAt) 1 ⟨zero_le_one, le_rfl⟩
  have hf0 : f 0 = 0 := by simp [f, hS00]
  have hew : HasFDerivAt e (fderiv ℝ e w) w :=
    ((he.differentiableOn (by simp)).differentiableAt (hD.mem_nhds hdom)).hasFDerivAt
  have hT1 : T (1, 0) = fderiv ℝ e w w := by
    have h1 := hΦt 1 0 (hU0 1 ⟨by linarith, by linarith⟩)
    have hc : (fun r => Φ (r, 0)) = fun r : ℝ => e (r • w) := funext hΦ0
    rw [hc] at h1
    have hd : HasFDerivAt e (fderiv ℝ e w) ((1 : ℝ) • w) := by rwa [one_smul]
    have := hd.comp_hasDerivAt (1 : ℝ) ((hasDerivAt_id (1 : ℝ)).smul_const w)
    rw [one_smul] at this
    exact h1.unique this
  have hS1 : S (1, 0) = fderiv ℝ e w ξ := by
    have h1 := hΦs 1 0 (hU0 1 ⟨by linarith, by linarith⟩)
    have hc : (fun r => Φ (1, r)) = fun r : ℝ => e (w + r • ξ) := by
      funext r
      simp [Φ, φ]
    rw [hc] at h1
    have hd : HasFDerivAt e (fderiv ℝ e w) (w + (0 : ℝ) • ξ) := by rwa [zero_smul, add_zero]
    have hl : HasDerivAt (fun s : ℝ => w + s • ξ) ξ 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const ξ).const_add w
    have := hd.comp_hasDerivAt (0 : ℝ) hl
    exact h1.unique this
  have hf1 : f 1 = form (g (e w)) (fderiv ℝ e w w) (fderiv ℝ e w ξ) := by
    simp only [f, hT1, hS1, hΦ0, one_smul]
  simp only [hf0] at hconst
  rw [← hf1]
  linarith

end

end LorentzianCalderon
