module

public import LorentzianCalderon.Induction.PropagationA
public import LorentzianCalderon.Waves.OneSided
public import LorentzianCalderon.Geometry.Emission

public section

/-!
# Transfer of causal relations

Blueprint, Lemma `lem_causal_transfer`: under `P(τ)`, if `x ∈ A_τ`, `y ∈ O` and `y ≤_g x`, then
`y ≤_{g'} Ψ(x)`.

* Outside `M₀` both metrics are Minkowskian with the same time orientation, so `g`-causal curves
  in `O` are `g'`-causal (`causalLE_of_isGeodesic_subset_O`).
* A retarded solution which is `u H(φ - s)` near a point of `{φ = s}` with `u > 0` and `dφ ≠ 0`
  does not vanish on any neighbourhood of that point (`not_vanishesOn_of_agreesOn`).
* For a null geodesic `σ₀` from `z ∈ O` to a point `σ₀ 1 ∉ I⁺(z)`, the one-sided wave emitted
  near `z` gives `z ≤_{g'} Ψ(σ₀ a)` for `a ∈ (0, 1)` with `σ₀ a ∈ A_τ`
  (`ExtensionProperty.causalLE_of_null`), by propagation (a).
* The theorem (`ExtensionProperty.causalLE_transfer`): the last point `z` of an escaping ray from
  `y` in `J⁻_g(x)`, and the limit `a → 1`.
-/

namespace LorentzianCalderon

noncomputable section
open MeasureTheory Set Filter Function
open scoped ContDiff Topology

variable {n : ℕ}

/-! ### Causality outside `M₀` -/

section Exterior

variable {T : ℝ} {g g' : MatrixField n} {Y Y' : E n → E n}

/-- A future-directed causal `g`-geodesic segment in `O` is a `g'`-causal curve. -/
theorem causalLE_of_isGeodesic_subset_O (hgA : IsAdmissibleMetric n T g)
    (hg'A : IsAdmissibleMetric n T g') (hg : IsSpacetime g Y) (hg' : IsSpacetime g' Y')
    (hY : ∀ x ∉ M0 n T, form (g x) (EuclideanSpace.single 0 1) (Y x) < 0)
    (hY' : ∀ x ∉ M0 n T, form (g' x) (EuclideanSpace.single 0 1) (Y' x) < 0)
    {γ : ℝ → E n} {I : Set ℝ} (hγ : IsGeodesic g γ I) {a b : ℝ} (hab : a ≤ b)
    (hI : Icc a b ⊆ I) (hP : ∀ t ∈ Icc a b, IsFutureCausal g Y (γ t) (deriv γ t))
    (hO : ∀ t ∈ Icc a b, γ t ∈ O n T) : CausalLE g' Y' (γ a) (γ b) := by
  rcases hab.lt_or_eq with hab | rfl
  · exact causalLE_of_isPathOn (hγ.isPathOn hab hI fun t ht =>
      (isFutureCausal_iff_of_exterior hg hg' hgA.minkowski_exterior hg'A.minkowski_exterior hY
        hY' (not_mem_M0_of_mem_O (hO t ht)) _).1 (hP t ht))
  · exact CausalLE.refl _

end Exterior

/-! ### Non-vanishing of one-sided waves -/

section NonVanishing

/-- A function with nonzero differential at `x₀` takes values larger than `φ x₀` arbitrarily
close to `x₀`. -/
lemma frequently_lt_of_hasFDerivAt {φ : E n → ℝ} {L : E n →L[ℝ] ℝ} {x₀ : E n}
    (h : HasFDerivAt φ L x₀) (hL : L ≠ 0) : ∃ᶠ y in 𝓝 x₀, φ x₀ < φ y := by
  obtain ⟨v, hv⟩ : ∃ v, 0 < L v := by
    by_contra! hle
    refine hL (ContinuousLinearMap.ext fun v => le_antisymm (hle v) ?_)
    have := hle (-v)
    rw [map_neg] at this
    simp only [zero_apply]
    linarith
  have hline : HasDerivAt (fun t : ℝ => x₀ + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x₀
  have hd : HasDerivAt (fun t : ℝ => φ (x₀ + t • v)) (L v) 0 :=
    h.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hslope := hd.tendsto_slope_zero_right
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), φ x₀ < φ (x₀ + t • v) := by
    filter_upwards [hslope.eventually (lt_mem_nhds hv), self_mem_nhdsWithin] with t ht ht0
    simp only [zero_add, zero_smul, add_zero, smul_eq_mul] at ht
    have ht0' : (0 : ℝ) < t := ht0
    have := (inv_pos.2 ht0').le
    nlinarith [mul_pos (inv_pos.2 ht0') ht0', inv_mul_cancel₀ ht0'.ne']
  have hc : Tendsto (fun t : ℝ => x₀ + t • v) (𝓝[>] 0) (𝓝 x₀) := by
    have : Continuous fun t : ℝ => x₀ + t • v := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  rw [Filter.frequently_iff]
  intro U hU
  obtain ⟨t, htU, ht⟩ := ((hc.eventually hU).and hev).exists
  exact ⟨_, htU, ht⟩

variable {g : MatrixField n} {Y : E n → E n}

/-- A functional agreeing on `V` with `H(φ - s) u`, where `u` is continuous on `V`, positive at a
point `x₀ ∈ V` with `φ x₀ = s` at which `φ` has nonzero differential, vanishes on no
neighbourhood of `x₀`. -/
theorem not_vanishesOn_of_agreesOn (hg : IsSpacetime g Y) {U : (E n → ℝ) → ℝ}
    {φ u : E n → ℝ} {s : ℝ} {V : Set (E n)} (hV : IsOpen V)
    (hU : AgreesOn g U ({x | s ≤ φ x}.indicator u) V) (hu : ContinuousOn u V)
    (hφ : ContinuousOn φ V) {x₀ : E n} (hx₀ : x₀ ∈ V) {L : E n →L[ℝ] ℝ}
    (hφd : HasFDerivAt φ L x₀) (hL : L ≠ 0) (hφ₀ : φ x₀ = s) (hu₀ : 0 < u x₀) :
    ∀ V', IsOpen V' → x₀ ∈ V' → ¬ VanishesOn U V' := by
  intro V' hV' hx₀' hvan
  set G := (V ∩ u ⁻¹' Ioi 0) ∩ V'
  have hG : IsOpen G := (hu.isOpen_inter_preimage hV isOpen_Ioi).inter hV'
  obtain ⟨c, hc, hcG⟩ := ((frequently_lt_of_hasFDerivAt hφd hL).and_eventually
    (hG.mem_nhds ⟨⟨hx₀, hu₀⟩, hx₀'⟩)).exists
  rw [hφ₀] at hc
  set G' := (V ∩ φ ⁻¹' Ioi s) ∩ G
  have hG' : IsOpen G' := (hφ.isOpen_inter_preimage hV isOpen_Ioi).inter hG
  obtain ⟨r, hr, hrG⟩ := Metric.isOpen_iff.1 hG' c ⟨⟨hcG.1.1, hc⟩, hcG⟩
  let h : ContDiffBump c := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hball : Metric.closedBall c (r / 2) ⊆ G' :=
    (Metric.closedBall_subset_ball (by linarith)).trans hrG
  have hts : tsupport h ⊆ G' := by
    rw [h.tsupport_eq]
    exact hball
  have hsm : ContDiff ℝ ∞ h := h.contDiff
  have hcs : HasCompactSupport h := h.hasCompactSupport
  have h0 := (vanishesOn_iff.1 hvan) h hsm hcs (hts.trans fun x hx => hx.2.2)
  rw [(agreesOn_iff.1 hU) h hsm hcs (hts.trans fun x hx => hx.1.1)] at h0
  set ρ : E n → ℝ := fun x => √|(g x).det|
  have hρ : Continuous ρ := (contDiff_sqrt_abs_det hg.smooth hg.det_ne_zero).continuous
  have hρpos : ∀ x, 0 < ρ x := fun x => Real.sqrt_pos.2 (abs_pos.2 (hg.det_ne_zero x))
  set f : E n → ℝ := fun x => {x | s ≤ φ x}.indicator u x * h x * ρ x
  have hfeq : ∀ x ∈ G', f x = u x * h x * ρ x := fun x hx => by
    have hxs : x ∈ {x | s ≤ φ x} := le_of_lt (show s < φ x from hx.1.2)
    simp only [f, indicator_of_mem hxs]
  have hf0 : ∀ x ∉ G', f x = 0 := fun x hx => by
    simp [f, image_eq_zero_of_notMem_tsupport fun h' => hx (hts h')]
  have hfnn : ∀ x, 0 ≤ f x := fun x => by
    by_cases hx : x ∈ G'
    · rw [hfeq x hx]
      exact mul_nonneg (mul_nonneg hx.2.1.2.le (h.nonneg)) (hρpos x).le
    · rw [hf0 x hx]
  have hfint : Integrable f := by
    have hK : IsCompact (Metric.closedBall c (r / 2)) := isCompact_closedBall c _
    have hcont : ContinuousOn (fun x => u x * h x * ρ x) (Metric.closedBall c (r / 2)) :=
      ((hu.mono fun x hx => (hball hx).1.1).mul hsm.continuous.continuousOn).mul
        hρ.continuousOn
    have hint := (hcont.integrableOn_compact (μ := volume) hK).congr_fun
      (fun x hx => (hfeq x (hball hx)).symm) measurableSet_closedBall
    refine hint.integrable_of_forall_notMem_eq_zero fun x hx => ?_
    simp [f, image_eq_zero_of_notMem_tsupport fun h' => hx (by rwa [h.tsupport_eq] at h')]
  have hpos : 0 < ∫ x, f x := by
    rw [integral_pos_iff_support_of_nonneg hfnn hfint]
    refine (Metric.measure_ball_pos volume c (by positivity : (0 : ℝ) < r / 2)).trans_le
      (measure_mono fun x hx => ?_)
    have hxG : x ∈ G' := hball (Metric.ball_subset_closedBall hx)
    rw [mem_support, hfeq x hxG]
    exact (mul_pos (mul_pos hxG.2.1.2 (h.pos_of_mem_ball hx)) (hρpos x)).ne'
  exact hpos.ne' h0

end NonVanishing

/-! ### One-sided waves from emission functions -/

section Emission

variable {g : MatrixField n} {Y : E n → E n}

/-- **One-sided retarded waves** (`lem_onesided`) from the conclusions of the emission lemma
(`IsEmissionFunction`) and the hypotheses on `σ`, `t₁`, `t₂` and `μ`: this is
`IsEmission.exists_isOneSidedWave` with the hypotheses of `IsEmission` spelled out. -/
theorem IsEmissionFunction.exists_isOneSidedWave {σ : ℝ → E n} {t₁ t₂ : ℝ} {μ : ℝ → E n}
    {η : ℝ} {T : Set (E n)} {φ : E n → ℝ} (hE : IsEmissionFunction g Y σ t₁ t₂ μ η T φ)
    (hg : IsSpacetime g Y) {I : Set ℝ} {b : ℝ} (hσ : IsGeodesic g σ I) (hI : Icc 0 b ⊆ I)
    (hnull : ∀ t ∈ Icc 0 b, form (g (σ t)) (deriv σ t) (deriv σ t) = 0)
    (hfut : ∀ t ∈ Icc 0 b, IsFutureCausal g Y (σ t) (deriv σ t))
    (hfirst : σ b ∉ chronFuture g Y (σ 0)) (ht₁ : 0 < t₁) (ht₁1 : t₁ < 1) (h1t₂ : 1 < t₂)
    (ht₂ : t₂ < b) (hη : 0 < η) (hμ : ContDiffOn ℝ ∞ μ (Ioo (-η) η))
    (hμt : ∀ s ∈ Ioo (-η) η, IsFutureTimelike g Y (μ s) (deriv μ s)) {t : ℝ}
    (ht : t ∈ Ioo t₁ 1) {N : Set (E n)} (hN : IsOpen N) (htN : σ t ∈ N) :
    ∃ (θ : E n → ℝ) (V : Set (E n)) (u a b : ℝ → E n → ℝ) (F : ℝ → (E n → ℝ) → ℝ),
      0 < θ (σ t) ∧ IsOneSidedWave g Y φ T N μ η (σ 1) θ V u a b F :=
  IsEmission.exists_isOneSidedWave hg
    { geodesic := ⟨I, hσ, hI⟩
      null := hnull
      future := hfut
      notMem_chronFuture := hfirst
      t₁_pos := ht₁
      t₁_lt_one := ht₁1
      one_lt_t₂ := h1t₂
      t₂_lt := ht₂
      η_pos := hη
      image_subset := hE.subset
      eikonal := ⟨hE.isOpen, hE.smooth, hE.eikonal, hE.d_ne_zero, hE.future⟩
      mem_Ioo := hE.mem_Ioo
      front := hE.front
      tangent := hE.tangent
      curve_smooth := hμ
      curve_timelike := hμt
      causalFuture_inter := hE.causalFuture_inter } ht hN htN

end Emission

/-! ### Transfer along null geodesics -/

namespace ExtensionProperty

variable {T : ℝ} {g g' : MatrixField n} {Y Y' : E n → E n} {ψ : E n → ℝ} {τ : ℝ}
  {Ψ : E n → E n} {Φ : ℝ → E n → E n}

/-- Under `P(τ)`, for a future-directed null geodesic `σ₀` from `z = σ₀ 0 ∈ O` with
`σ₀ 1 ∉ I⁺_g(z)`, every point `σ₀ a`, `0 < a < 1`, of `A_τ` satisfies `z ≤_{g'} Ψ(σ₀ a)`.

The one-sided wave of `σ(t) = σ₀(a t)` (emitted near `z`, from a source supported in
`J⁺_{g'}(z) ∩ O`) does not vanish near `σ₀ a`, so by propagation (a) its `g'`-retarded solution
does not vanish near `Ψ(σ₀ a)`, which therefore lies in the `g'`-future of the source. -/
theorem causalLE_of_null (hP : ExtensionProperty g g' ψ (W n T) τ Ψ)
    (hgA : IsAdmissibleMetric n T g) (hg'A : IsAdmissibleMetric n T g')
    (hg : IsSpacetime g Y) (hg' : IsSpacetime g' Y')
    (hY : ∀ x ∉ M0 n T, form (g x) (EuclideanSpace.single 0 1) (Y x) < 0)
    (hY' : ∀ x ∉ M0 n T, form (g' x) (EuclideanSpace.single 0 1) (Y' x) < 0)
    (hC : CauchyDataSubset n T g g') (hψ : IsCauchyTemporal g Y ψ)
    (hΦ : Continuous fun p : ℝ × E n => Φ p.1 p.2) (hΦ0 : ∀ x, Φ 0 x = x)
    (hΦψ : ∀ t x, ψ (Φ t x) = ψ x + t) {σ₀ : ℝ → E n} {I : Set ℝ} (hσ₀ : IsGeodesic g σ₀ I)
    (hI : Icc 0 1 ⊆ I) (hnull : form (g (σ₀ 0)) (deriv σ₀ 0) (deriv σ₀ 0) = 0)
    (hfut : IsFutureCausal g Y (σ₀ 0) (deriv σ₀ 0)) (hfirst : ¬ ChronLT g Y (σ₀ 0) (σ₀ 1))
    (hz : σ₀ 0 ∈ O n T) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hA : σ₀ a ∈ A ψ τ) :
    CausalLE g' Y' (σ₀ 0) (Ψ (σ₀ a)) := by
  obtain ⟨ha0, ha1⟩ := ha
  set σ : ℝ → E n := fun t => σ₀ (a * t + 0)
  set J := (fun t : ℝ => a * t + 0) ⁻¹' I
  have hσ : IsGeodesic g σ J := hσ₀.comp_affine a 0
  set b := a⁻¹
  have hb0 : 0 < b := inv_pos.2 ha0
  have hb1 : 1 < b := (one_lt_inv₀ ha0).2 ha1
  have hab : a * b = 1 := mul_inv_cancel₀ ha0.ne'
  have hJ : Icc 0 b ⊆ J := fun t ht => by
    show a * t + 0 ∈ I
    rw [add_zero]
    exact hI ⟨mul_nonneg ha0.le ht.1, hab ▸ mul_le_mul_of_nonneg_left ht.2 ha0.le⟩
  have h0J : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb0.le⟩
  have hσ0 : σ 0 = σ₀ 0 := by simp [σ]
  have hσ1 : σ 1 = σ₀ a := by simp [σ]
  have hσb : σ b = σ₀ 1 := by simp [σ, hab]
  have hd0 : deriv σ 0 = a • deriv σ₀ 0 := by
    have := hσ₀.deriv_comp_affine (c := a) (d := 0) (s := 0)
      (by simpa using hI ⟨le_rfl, zero_le_one⟩)
    exact this.trans (by simp)
  have hnull': form (g (σ 0)) (deriv σ 0) (deriv σ 0) = 0 := by
    rw [hd0, hσ0, form_smul_left, form_smul_right, hnull]
    ring
  have hfut' : IsFutureCausal g Y (σ 0) (deriv σ 0) := by
    rw [hd0, hσ0]
    exact hfut.smul ha0
  have hfirst' : ¬ ChronLT g Y (σ 0) (σ b) := by rwa [hσ0, hσb]
  -- an initial piece `σ([0, ts])` in `O`
  have hσc : ContinuousAt σ 0 :=
    hσ.smooth.continuousOn.continuousAt (hσ.isOpen.mem_nhds (hJ h0J))
  obtain ⟨ε, hε, hεO⟩ := Metric.mem_nhds_iff.1
    (hσc.preimage_mem_nhds (isOpen_O.mem_nhds (hσ0 ▸ hz)))
  set ts := min (ε / 2) (1 / 2)
  have hts0 : 0 < ts := lt_min (by positivity) (by norm_num)
  have hts1 : ts < 1 := min_lt_of_right_lt (by norm_num)
  have htsO : σ '' Icc 0 ts ⊆ O n T := by
    rintro _ ⟨t, ht, rfl⟩
    apply hεO
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
    exact lt_of_le_of_lt (ht.2.trans (min_le_left _ _)) (half_lt_self hε)
  set t₁ := ts / 2
  set t₂ := (1 + b) / 2
  have ht₁ts : t₁ < ts := half_lt_self hts0
  have ht₁1 : t₁ < 1 := ht₁ts.trans hts1
  have h1t₂ : 1 < t₂ := by simp only [t₂]; linarith
  have ht₂b : t₂ < b := by simp only [t₂]; linarith
  -- the timelike curve `μ` through `z`
  set e₀ : E n := EuclideanSpace.single 0 1
  set μ : ℝ → E n := fun s => σ₀ 0 + s • e₀
  have hμc : Continuous μ := by fun_prop
  obtain ⟨η₀, hη₀, hη₀O⟩ := Metric.mem_nhds_iff.1
    ((hμc.continuousAt (x := 0)).preimage_mem_nhds (isOpen_O.mem_nhds (by simpa [μ] using hz)))
  have hμt : ∀ s ∈ Ioo (-η₀) η₀, IsFutureTimelike g Y (μ s) (deriv μ s) := by
    intro s hs
    have hd : deriv μ s = e₀ := by
      have : HasDerivAt μ e₀ s :=
        (by simpa using (hasDerivAt_id s).smul_const e₀ :
          HasDerivAt (fun x : ℝ => x • e₀) e₀ s).const_add (σ₀ 0)
      exact this.deriv
    have hsO : μ s ∈ O n T := hη₀O (by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
      exact ⟨hs.1, hs.2⟩)
    have hM := not_mem_M0_of_mem_O hsO
    rw [hd]
    exact (isFutureTimelike_iff_of_minkowski (hgA.minkowski_exterior _ hM)
      (hg.globallyHyperbolic.timeOrientation.timelike _) (hY _ hM)).2
      ⟨by simp [e₀, form_minkowski_self], by simp [e₀]⟩
  have hμsm : ContDiffOn ℝ ∞ μ (Ioo (-η₀) η₀) :=
    (contDiff_const.add (contDiff_id.smul contDiff_const)).contDiffOn
  have hμ0 : μ 0 = σ 0 := by simp [μ, hσ0]
  -- the emission function and the one-sided wave
  obtain ⟨η, hη, Tφ, φ, hEF⟩ := exists_isEmissionFunction hg hσ hJ hnull' hfut' hfirst'
    (t₁ := t₁) (t₂ := t₂) (by positivity) ht₂b hη₀ hμsm hμt hμ0
  have hφT : IsFutureEikonal g Y φ Tφ :=
    ⟨hEF.isOpen, hEF.smooth, hEF.eikonal, hEF.d_ne_zero, hEF.future⟩
  have htsI : ts ∈ Icc t₁ t₂ := ⟨ht₁ts.le, (hts1.trans h1t₂).le⟩
  obtain ⟨C₁, hC₁, hseg⟩ := hEF.segment ts htsI (O n T) (isOpen_O.mem_nhdsSet.2 htsO)
  set N := interior C₁ ∩ O n T
  have hN : IsOpen N := isOpen_interior.inter isOpen_O
  have hσN : σ ts ∈ N :=
    ⟨mem_interior_iff_mem_nhds.2 hC₁, htsO ⟨ts, ⟨hts0.le, le_rfl⟩, rfl⟩⟩
  obtain ⟨θ, V, u, _, _, F, -, hW⟩ := hEF.exists_isOneSidedWave hg hσ hJ
    (fun t ht => (hσ.form_deriv_eq hg hJ ordConnected_Icc ht h0J).trans hnull')
    (fun t ht => hσ.isFutureCausal hg hJ ordConnected_Icc h0J hfut' ht) (fun h => hfirst'
      (mem_chronFuture.1 h))
    (by positivity) ht₁1 h1t₂ ht₂b hη.1 (hμsm.mono (Ioo_subset_Ioo (neg_le_neg hη.2.le) hη.2.le))
    (fun s hs => hμt s ⟨by linarith [hs.1, hη.2], by linarith [hs.2, hη.2]⟩)
    ⟨ht₁ts, hts1⟩ hN hσN
  have h0η : (0 : ℝ) ∈ Ioo (-η) η := ⟨by linarith [hη.1], hη.1⟩
  set K := tsupport θ ∩ {x | φ x = 0}
  have hF : IsSource (F 0) K := hW.source 0 h0η
  have hKO : K ⊆ O n T := fun p hp => (hW.tsupport_theta_subset hp.1).1.2
  -- the source lies in `J⁺_{g'}(z)`
  have hKz : ∀ p ∈ K, CausalLE g' Y' (σ₀ 0) p := by
    intro p hp
    have hpN := hW.tsupport_theta_subset hp.1
    obtain ⟨w, hwf, -, hwd, hwp, hwC⟩ := hseg p ⟨interior_subset hpN.1.1, hpN.2⟩ hp.2
    obtain ⟨ε', hε', hγ, -, hγ0, hγd⟩ := hwd.isGeodesic_expMap_smul hg
    have hsub : Icc (0 : ℝ) 1 ⊆ Ioo (-ε') (1 + ε') := fun r hr =>
      ⟨by linarith [hr.1], by linarith [hr.2]⟩
    have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
    have hf0 : IsFutureCausal g Y (expMap g (σ 0) ((0 : ℝ) • w))
        (deriv (fun t : ℝ => expMap g (σ 0) (t • w)) 0) := by
      rw [hγ0, hγd]
      exact hwf
    have := causalLE_of_isGeodesic_subset_O hgA hg'A hg hg' hY hY' hγ zero_le_one hsub
      (fun r hr => hγ.isFutureCausal hg hsub ordConnected_Icc h01 hf0 hr) hwC
    convert this using 2
    · exact (hγ0.trans hσ0).symm
    · show p = expMap g (σ 0) ((1 : ℝ) • w)
      rw [one_smul, hwp]
  -- the `g`-retarded solution does not vanish near `σ 1`
  have h1V : σ 1 ∈ V := hW.mem
  have h1T : σ 1 ∈ Tφ := hW.subset h1V
  have hfront : φ (σ 1) = 0 := hEF.front 1 ⟨ht₁1.le, h1t₂.le⟩
  have huc : ContinuousOn (u 0) V :=
    hW.smooth.continuousOn.comp (by fun_prop : Continuous fun x : E n => ((0 : ℝ), x)).continuousOn
      fun x hx => ⟨h0η, hx⟩
  have hφc : ContinuousOn φ V := hEF.smooth.continuousOn.mono hW.subset
  have hφd : HasFDerivAt φ (fderiv ℝ φ (σ 1)) (σ 1) :=
    ((hEF.smooth.contDiffAt (hEF.isOpen.mem_nhds h1T)).differentiableAt (by simp)).hasFDerivAt
  have hnv := not_vanishesOn_of_agreesOn hg hW.isOpen (hW.retarded 0 h0η) huc hφc h1V hφd
    (hφT.fderiv_ne_zero h1T) hfront (hW.pos 0 h0η _ h1V hfront)
  -- propagation (a)
  have hA' : σ 1 ∈ A ψ τ := hσ1 ▸ hA
  have hmem : Ψ (σ 1) ∈ causalFutureSet g' Y' K := by
    by_contra hc
    obtain ⟨V'', hV'', hx'', -, hvan⟩ := hP.exists_vanishesOn_retardedS hgA hg'A hg hg' hY hY'
      hC hψ hΦ hΦ0 hΦψ hF hKO (isOpen_compl_causalFutureSet hg' hF.isCompact)
      (hF.vanishesOn_retardedS hg') hA' hc
    exact hnv V'' hV'' hx'' hvan
  obtain ⟨p, hpK, hp⟩ := mem_causalFutureSet.1 hmem
  rw [← hσ1]
  exact (hKz p hpK).trans (mem_causalFuture.1 hp)

/-! ### Transfer of causal relations -/

/-- **Transfer of causal relations** (blueprint, Lemma `lem_causal_transfer`): under `P(τ)`, if
`x ∈ A_τ`, `y ∈ O` and `y ≤_g x`, then `y ≤_{g'} Ψ(x)`. -/
theorem causalLE_transfer (hP : ExtensionProperty g g' ψ (W n T) τ Ψ)
    (hgA : IsAdmissibleMetric n T g) (hg'A : IsAdmissibleMetric n T g')
    (hg : IsSpacetime g Y) (hg' : IsSpacetime g' Y')
    (hY : ∀ x ∉ M0 n T, form (g x) (EuclideanSpace.single 0 1) (Y x) < 0)
    (hY' : ∀ x ∉ M0 n T, form (g' x) (EuclideanSpace.single 0 1) (Y' x) < 0)
    (hC : CauchyDataSubset n T g g') (hψ : IsCauchyTemporal g Y ψ)
    (hΦ : Continuous fun p : ℝ × E n => Φ p.1 p.2) (hΦ0 : ∀ x, Φ 0 x = x)
    (hΦψ : ∀ t x, ψ (Φ t x) = ψ x + t) {x y : E n} (hx : x ∈ A ψ τ) (hy : y ∈ O n T)
    (hyx : CausalLE g Y y x) : CausalLE g' Y' y (Ψ x) := by
  -- the escaping ray `c` from `y`
  obtain ⟨v, hv0, hvv, hvO⟩ := exists_escape_direction (by have := hg.two_le; omega) hy
  set c : ℝ → E n := fun s => y + s • v
  have hcc : Continuous c := by fun_prop
  have hc0 : c 0 = y := by simp [c]
  have htl : ∀ {G : MatrixField n} {Z : E n → E n}, IsAdmissibleMetric n T G →
      IsSpacetime G Z → (∀ x ∉ M0 n T, form (G x) (EuclideanSpace.single 0 1) (Z x) < 0) →
      ∀ s : ℝ, 0 ≤ s → IsFutureTimelike G Z (c s) v := by
    intro G Z hGA hG hZ s hs
    have hM := not_mem_M0_of_mem_O (hvO s hs)
    exact (isFutureTimelike_iff_of_minkowski (hGA.minkowski_exterior _ hM)
      (hG.globallyHyperbolic.timeOrientation.timelike _) (hZ _ hM)).2
      ⟨hvv, by rw [hv0]; exact one_pos⟩
  have hle : ∀ {G : MatrixField n} {Z : E n → E n}, IsAdmissibleMetric n T G →
      IsSpacetime G Z → (∀ x ∉ M0 n T, form (G x) (EuclideanSpace.single 0 1) (Z x) < 0) →
      ∀ s : ℝ, 0 ≤ s → CausalLE G Z y (c s) := by
    intro G Z hGA hG hZ s hs
    rcases hs.lt_or_eq with hs | rfl
    · have := causalLE_of_isPathOn (isPathOn_line (x := y) (v := v) hs fun t ht =>
        (htl hGA hG hZ t ht.1).isFutureCausal)
      simpa using this
    · rw [hc0]
  -- the last point `z` of `c` in `J⁻_g(x)`
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.1 ((tendsto_cocompact_line (x := y)
    (fun h : v = 0 => by simp [h] at hv0)).eventually
    (hg.globallyHyperbolic.compact_diamond y x).compl_mem_cocompact)
  set S := {t : ℝ | 0 ≤ t ∧ CausalLE g Y (c t) x}
  have hS : IsClosed S := (isClosed_Ici (a := (0 : ℝ))).inter
    ((Facts.isClosed_causalLE hg).preimage (hcc.prodMk continuous_const))
  have hS0 : (0 : ℝ) ∈ S := ⟨le_rfl, by rw [hc0]; exact hyx⟩
  have hSb : BddAbove S := ⟨t₀, fun t ht => by
    by_contra h
    exact ht₀ t (not_le.1 h).le ⟨mem_causalFuture.2 (hle hgA hg hY t ht.1),
      mem_causalPast.2 ht.2⟩⟩
  set ts := sSup S
  have hts : ts ∈ S := hS.csSup_mem ⟨0, hS0⟩ hSb
  set z := c ts
  have hzO : z ∈ O n T := hvO ts hts.1
  have hyz : CausalLE g' Y' y z := hle hg'A hg' hY' ts hts.1
  have hzx : CausalLE g Y z x := hts.2
  have hnc : ¬ ChronLT g Y z x := by
    intro h
    have hop : IsOpen {t : ℝ | ChronLT g Y (c t) x} := by
      have e : {t : ℝ | ChronLT g Y (c t) x} = c ⁻¹' chronPast g Y x := by
        ext t
        simp only [mem_ofPred_eq, mem_preimage, mem_chronPast]
      rw [e, ← chronFuture_neg]
      exact (Facts.isOpen_chronFuture hg.neg x).preimage hcc
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hop ts h
    have hmem : ts + ε / 2 ∈ S := by
      refine ⟨by linarith [hts.1], (hball ?_).causalLE⟩
      rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hε)]
      exact half_lt_self hε
    have := le_csSup hSb hmem
    linarith
  by_cases hzx' : z = x
  · have hxO : x ∈ O n T := hzx' ▸ hzO
    rw [hP.eq_self x hx (mem_O.1 hxO), ← hzx']
    exact hyz
  -- a null geodesic from `z` to `x`
  obtain ⟨σ₀, I, hσ, hI, hσ0, hσ1, hcaus, hnullI⟩ := Facts.exists_causal_geodesic hg hzx hzx' hnc
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hnull : form (g (σ₀ 0)) (deriv σ₀ 0) (deriv σ₀ 0) = 0 := hnullI 0 (hI h0)
  have hkey : ∀ a ∈ Ioo (0 : ℝ) 1, σ₀ a ∈ A ψ τ → CausalLE g' Y' z (Ψ (σ₀ a)) :=
    fun a ha hA => by
      have := hP.causalLE_of_null hgA hg'A hg hg' hY hY' hC hψ hΦ hΦ0 hΦψ hσ hI hnull
        (hcaus 0 h0) (by rwa [hσ0, hσ1]) (by rw [hσ0]; exact hzO) ha hA
      rwa [hσ0] at this
  -- the limit `a → 1`
  have hσc : Tendsto σ₀ (𝓝[<] 1) (𝓝 x) := by
    rw [← hσ1]
    exact (hσ.smooth.continuousOn.continuousAt
      (hσ.isOpen.mem_nhds (hI ⟨zero_le_one, le_rfl⟩))).tendsto.mono_left nhdsWithin_le_nhds
  have hAo := isOpen_A hψ.smooth.continuous τ
  have hΨc : ContinuousAt Ψ x := hP.smooth.continuousOn.continuousAt (hAo.mem_nhds hx)
  have hev : ∀ᶠ a in 𝓝[<] (1 : ℝ), Ψ (σ₀ a) ∈ causalFuture g' Y' z := by
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one, hσc.eventually (hAo.mem_nhds hx)] with a ha hA
    exact mem_causalFuture.2 (hkey a ha hA)
  exact hyz.trans (mem_causalFuture.1
    ((isClosed_causalFuture hg' z).mem_of_tendsto (hΨc.tendsto.comp hσc) hev))

end ExtensionProperty

end

end LorentzianCalderon
