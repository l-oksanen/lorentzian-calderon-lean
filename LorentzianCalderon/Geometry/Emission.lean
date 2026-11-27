module

public import LorentzianCalderon.Geometry.WorldFunctionDeriv

public section

/-!
# The emission-time function

Blueprint, Lemma `lem_emission`: along a first-arrival null geodesic `σ` and for a future-directed
timelike curve `μ` through `σ 0`, the emission time `φ(x)` (the parameter `s` for which `x` lies
on the future light cone of `μ(s)`) is an eikonal function of future type near `σ([t₁, t₂])`.
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Set Filter

variable {n : ℕ} {g : MatrixField n} {Y : E n → E n}

/-- If `dφ(x) = c g(V, ·)`, then `grad φ(x) = c V` and `g(dφ, dφ) = c² g(V, V)`. -/
theorem grad_eq_smul_of_fderiv_eq (hg : IsSpacetime g Y) {φ : E n → ℝ} {x V : E n} {c : ℝ}
    (h : ∀ w, fderiv ℝ φ x w = c * form (g x) V w) :
    grad g φ x = c • V ∧ coform g x (d φ x) (d φ x) = c ^ 2 * form (g x) V V := by
  have hA := (hg.lorentzian x).symm
  have hunit : IsUnit (g x).det := (hg.det_ne_zero x).isUnit
  have hξ : d φ x = c • (g x *ᵥ V.ofLp) := by
    funext k
    have hs := (Matrix.mulVec_transpose (g x) V.ofLp)
    rw [hA] at hs
    simp only [d_def, h, form_def, Pi.smul_apply, smul_eq_mul]
    simp only [PiLp.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, hs]
    rfl
  have hgrad : (fun j => ∑ k, (g x)⁻¹ j k * d φ x k) = c • V.ofLp := by
    have : (g x)⁻¹ *ᵥ d φ x = c • V.ofLp := by
      rw [hξ, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit,
        Matrix.one_mulVec]
    rw [← this]
    rfl
  refine ⟨?_, ?_⟩
  · simp only [grad_def, hgrad]
    rfl
  · have : coform g x (d φ x) (d φ x) = d φ x ⬝ᵥ ((g x)⁻¹ *ᵥ d φ x) := by
      simp only [coform_def, dotProduct, Matrix.mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [this, show (g x)⁻¹ *ᵥ d φ x = c • V.ofLp from hgrad, hξ, form_eq_dotProduct,
      dotProduct_smul, smul_dotProduct, dotProduct_comm]
    simp only [smul_eq_mul]
    ring

/-- Along a geodesic `σ`, `d(exp_{σ 0})_{t σ'(0)} (t σ'(0)) = t σ'(t)`. -/
theorem IsGeodesic.fderiv_expMap_smul (hg : IsSpacetime g Y) {σ : ℝ → E n} {I : Set ℝ} {b : ℝ}
    (hσ : IsGeodesic g σ I) (hI : Icc 0 b ⊆ I) {t : ℝ} (ht : t ∈ Ioo 0 b) :
    fderiv ℝ (expMap g (σ 0)) (t • deriv σ 0) (t • deriv σ 0) = t • deriv σ t := by
  have hsub : ∀ r ∈ Ioo 0 (b / t), uIcc 0 (r * t) ⊆ I := fun r hr => by
    have h1 : 0 < r * t := mul_pos hr.1 ht.1
    have h2 : r * t < b := (lt_div_iff₀ ht.1).1 hr.2
    exact (uIcc_subset_Icc ⟨le_rfl, h1.le.trans h2.le⟩ ⟨h1.le, h2.le⟩).trans hI
  have h1 : (1 : ℝ) ∈ Ioo 0 (b / t) := ⟨one_pos, (one_lt_div ht.1).2 ht.2⟩
  have hdom := (hσ.expMap_smul_eq hg (by simpa using hsub 1 h1)).1
  have hD := hasDerivAt_expMap_smul_one hg hdom
  have hev : (fun r : ℝ => expMap g (σ 0) (r • t • deriv σ 0)) =ᶠ[𝓝 1] fun r => σ (r * t) := by
    filter_upwards [isOpen_Ioo.mem_nhds h1] with r hr
    rw [smul_smul]
    exact (hσ.expMap_smul_eq hg (hsub r hr)).2
  have hσt : HasDerivAt (fun r => σ (r * t)) ((1 * t) • deriv σ (1 * t)) 1 :=
    (by simpa using hσ.hasDerivAt (hI ⟨ht.1.le, ht.2.le⟩) :
      HasDerivAt σ (deriv σ (1 * t)) (1 * t)).scomp 1 ((hasDerivAt_id 1).mul_const t)
  simp only [one_mul] at hσt
  exact hD.unique (hσt.congr_of_eventuallyEq hev)

/-- The implicit function theorem for a scalar equation `G(s, p) = 0`: a solution `φ` that is
locally unique near a regular zero is smooth there. -/
theorem contDiffAt_of_eq_zero {G : ℝ × E n → ℝ} {φ : E n → ℝ} {p₀ : E n} {S : Set ℝ}
    (hS : IsOpen S) (hG : ContDiffAt ℝ ∞ G (φ p₀, p₀)) (hD : fderiv ℝ G (φ p₀, p₀) (1, 0) ≠ 0)
    (hφS : φ p₀ ∈ S) (h0 : G (φ p₀, p₀) = 0)
    (huniq : ∀ᶠ p in 𝓝 p₀, ∀ s ∈ S, G (s, p) = 0 → s = φ p) : ContDiffAt ℝ ∞ φ p₀ := by
  set z₀ : ℝ × E n := (φ p₀, p₀)
  set L := fderiv ℝ G z₀
  set Φ : ℝ × E n → ℝ × E n := fun z => (G z, z.2)
  have hΦ : ContDiffAt ℝ ∞ Φ z₀ := hG.prodMk contDiffAt_snd
  set M : (ℝ × E n) →L[ℝ] (ℝ × E n) := L.prod (ContinuousLinearMap.snd ℝ ℝ (E n))
  have hM : HasFDerivAt Φ M z₀ :=
    (hG.differentiableAt (by simp)).hasFDerivAt.prodMk hasFDerivAt_snd
  have hinj : Function.Injective M := by
    refine (injective_iff_map_eq_zero M).2 ?_
    rintro ⟨a, h⟩ hah
    simp only [M, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_snd',
      Prod.mk_eq_zero] at hah
    obtain ⟨ha, rfl⟩ := hah
    have : L (a, 0) = a * L (1, 0) := by
      rw [show ((a, 0) : ℝ × E n) = a • ((1 : ℝ), (0 : E n)) by simp, map_smul, smul_eq_mul]
    rw [this] at ha
    simp [(mul_eq_zero.1 ha).resolve_right hD]
  set f' : (ℝ × E n) ≃L[ℝ] (ℝ × E n) := (LinearEquiv.ofInjectiveEndo
    (M : (ℝ × E n) →ₗ[ℝ] (ℝ × E n)) hinj).toContinuousLinearEquiv
  have hf' : HasFDerivAt Φ (f' : (ℝ × E n) →L[ℝ] (ℝ × E n)) z₀ := by
    convert hM using 1
    ext x <;> simp [f', LinearEquiv.coe_ofInjectiveEndo]
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hs := hΦ.hasStrictFDerivAt' hf' hn
  set ψ := hΦ.localInverse hf' hn
  have hψ : ContDiffAt ℝ ∞ ψ (Φ z₀) := hΦ.to_localInverse hf' hn
  have hΦz : Φ z₀ = (0, p₀) := by simp [Φ, z₀, h0]
  have hright : ∀ᶠ y in 𝓝 (Φ z₀), Φ (ψ y) = y := hs.eventually_right_inverse
  have hcont : ContinuousAt ψ (Φ z₀) := hs.localInverse_continuousAt
  have hψz : ψ (Φ z₀) = z₀ := hΦ.localInverse_apply_image hf' hn
  have hline : Tendsto (fun p : E n => ((0 : ℝ), p)) (𝓝 p₀) (𝓝 (Φ z₀)) := by
    rw [hΦz]
    exact (continuous_const.prodMk continuous_id :
      Continuous fun p : E n => ((0 : ℝ), p)).tendsto p₀
  have hmemS : ∀ᶠ y in 𝓝 (Φ z₀), (ψ y).1 ∈ S :=
    hcont.eventually ((hS.preimage continuous_fst).mem_nhds (by rw [hψz]; exact hφS))
  have hev : φ =ᶠ[𝓝 p₀] fun p => (ψ (0, p)).1 := by
    filter_upwards [hline.eventually hright, hline.eventually hmemS, huniq] with p h1 h2 h3
    have h1' := Prod.ext_iff.1 h1
    have hz : ψ (0, p) = ((ψ (0, p)).1, p) := Prod.ext rfl h1'.2
    refine (h3 _ h2 ?_).symm
    rw [← hz]
    exact h1'.1
  have hc : ContDiffAt ℝ ∞ (fun p : E n => (ψ (0, p)).1) p₀ := by
    have : ContDiffAt ℝ ∞ ψ ((0 : ℝ), p₀) := hΦz ▸ hψ
    exact contDiffAt_fst.comp p₀ (this.comp p₀ (contDiffAt_const.prodMk contDiffAt_id))
  exact hc.congr_of_eventuallyEq hev

/-- The conclusion of Lemma `lem_emission`: `φ`, with values in `(-η, η)`, is an emission-time
function on the open neighbourhood `T` of `σ([t₁, t₂])` for the timelike curve `μ`. -/
structure IsEmissionFunction (g : MatrixField n) (Y : E n → E n) (σ : ℝ → E n) (t₁ t₂ : ℝ)
    (μ : ℝ → E n) (η : ℝ) (T : Set (E n)) (φ : E n → ℝ) : Prop where
  isOpen : IsOpen T
  subset : σ '' Icc t₁ t₂ ⊆ T
  smooth : ContDiffOn ℝ ∞ φ T
  mem_Ioo : ∀ x ∈ T, φ x ∈ Ioo (-η) η
  eikonal : ∀ x ∈ T, coform g x (d φ x) (d φ x) = 0
  d_ne_zero : ∀ x ∈ T, d φ x ≠ 0
  future : ∀ x ∈ T, IsFutureCausal g Y x (-grad g φ x)
  front : ∀ t ∈ Icc t₁ t₂, φ (σ t) = 0
  tangent : ∀ t ∈ Icc t₁ t₂, ∃ c : ℝ, 0 < c ∧ -grad g φ (σ t) = c • deriv σ t
  causalFuture_inter : ∀ s ∈ Ioo (-η) η, causalFuture g Y (μ s) ∩ T = {x ∈ T | s ≤ φ x}
  segment : ∀ t ∈ Icc t₁ t₂, ∀ C ∈ 𝓝ˢ (σ '' Icc 0 t), ∃ C₁ ∈ 𝓝 (σ t), ∀ x ∈ C₁ ∩ T,
    φ x = 0 → ∃ w, IsFutureCausal g Y (σ 0) w ∧ form (g (σ 0)) w w = 0 ∧
      InExpDomain g (σ 0) w ∧ expMap g (σ 0) w = x ∧
      ∀ r ∈ Icc (0 : ℝ) 1, expMap g (σ 0) (r • w) ∈ C

/-- Blueprint, Lemma `lem_emission`: along a first-arrival null geodesic `σ` on `[0, b]`, for a
smooth future-directed timelike curve `μ` with `μ 0 = σ 0`, the emission time `φ`
(`φ(x) = s` iff `x` lies on the future light cone of `μ(s)`, within the exponential chart of
`exists_worldFunction`) is an emission-time function near `σ([t₁, t₂])`. -/
theorem exists_isEmissionFunction (hg : IsSpacetime g Y) {σ : ℝ → E n} {I : Set ℝ} {b : ℝ}
    (hσ : IsGeodesic g σ I) (hI : Icc 0 b ⊆ I)
    (hnull : form (g (σ 0)) (deriv σ 0) (deriv σ 0) = 0)
    (hfut : IsFutureCausal g Y (σ 0) (deriv σ 0)) (hfirst : ¬ ChronLT g Y (σ 0) (σ b))
    {t₁ t₂ : ℝ} (ht₁ : 0 < t₁) (ht₂ : t₂ < b) {μ : ℝ → E n} {η₀ : ℝ} (hη₀ : 0 < η₀)
    (hμ : ContDiffOn ℝ ∞ μ (Ioo (-η₀) η₀))
    (hμt : ∀ s ∈ Ioo (-η₀) η₀, IsFutureTimelike g Y (μ s) (deriv μ s)) (hμ0 : μ 0 = σ 0) :
    ∃ η ∈ Ioo 0 η₀, ∃ T φ, IsEmissionFunction g Y σ t₁ t₂ μ η T φ := by
  obtain ⟨U, U', W, hc, hKU, hKU', hfutU, hrel⟩ :=
    exists_worldFunction hg hσ hI hnull hfut hfirst ht₁ ht₂
  have hIoo : ∀ t ∈ Icc t₁ t₂, t ∈ Ioo 0 b := fun t ht =>
    ⟨ht₁.trans_le ht.1, ht.2.trans_lt ht₂⟩
  have hexp : ∀ t ∈ Icc t₁ t₂, expMap g (σ 0) (t • deriv σ 0) = σ t := fun t ht =>
    (hσ.expMap_smul_eq hg ((uIcc_subset_Icc ⟨le_rfl, (hIoo t ht).1.le.trans (hIoo t ht).2.le⟩
      ⟨(hIoo t ht).1.le, (hIoo t ht).2.le⟩).trans hI)).2
  have hWσ : ∀ t ∈ Icc t₁ t₂, W (σ 0, σ t) = t • deriv σ 0 := fun t ht => by
    have := hc.inv_expPair _ (hKU t ht)
    simpa only [expPair_def, hexp t ht] using this
  have hμd : ∀ s ∈ Ioo (-η₀) η₀, HasDerivAt μ (deriv μ s) s := fun s hs =>
    ((hμ.differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hs)).hasDerivAt
  obtain ⟨G, hG⟩ : ∃ G : ℝ × E n → ℝ, ∀ z, G z = worldFn g W (μ z.1, z.2) := ⟨_, fun _ => rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ × E n → ℝ, ∀ z,
      D z = -2 * form (g (μ z.1)) (W (μ z.1, z.2)) (deriv μ z.1) := ⟨_, fun _ => rfl⟩
  set O : Set (ℝ × E n) :=
    Prod.fst ⁻¹' Ioo (-η₀) η₀ ∩ (fun z : ℝ × E n => (μ z.1, z.2)) ⁻¹' U' with hO_def
  have hμO : ContinuousOn (fun z : ℝ × E n => (μ z.1, z.2)) (Prod.fst ⁻¹' Ioo (-η₀) η₀) :=
    (hμ.continuousOn.comp continuousOn_fst fun z hz => hz).prodMk continuousOn_snd
  have hO : IsOpen O :=
    hμO.isOpen_inter_preimage (isOpen_Ioo.preimage continuous_fst) hc.isOpen'
  have hGs : ContDiffOn ℝ ∞ G O := by
    have h1 : ContDiffOn ℝ ∞ (fun z : ℝ × E n => (μ z.1, z.2)) O :=
      (hμ.comp contDiffOn_fst fun z hz => hz.1).prodMk contDiffOn_snd
    have h4 := (hc.contDiffOn_worldFn hg).comp h1 fun z hz => hz.2
    simp only [Function.comp_def] at h4
    rw [show G = fun z => worldFn g W (μ z.1, z.2) from funext hG]
    exact h4
  have hGd : ∀ z ∈ O, HasDerivAt (fun s => G (s, z.2)) (D z) z.1 := by
    rintro ⟨s, p⟩ hz
    obtain ⟨hdiff, hval⟩ := hc.fderiv_worldFn_fst hg (q := (μ s, p)) hz.2
    have h4 := hdiff.hasFDerivAt.comp_hasDerivAt s (hμd s hz.1)
    simp only [Function.comp_def, hval] at h4
    simp only [hG, hD]
    exact h4
  have hDc : ContinuousOn D O := by
    have hμ' : ContinuousOn (deriv μ) (Ioo (-η₀) η₀) :=
      hμ.continuousOn_deriv_of_isOpen isOpen_Ioo (by simp)
    have hW : ContinuousOn (fun z : ℝ × E n => W (μ z.1, z.2)) O :=
      hc.smooth.continuousOn.comp (hμO.mono inter_subset_left) fun z hz => hz.2
    have h3 : ContinuousOn (fun z : ℝ × E n => (μ z.1, W (μ z.1, z.2), deriv μ z.1)) O :=
      (hμ.continuousOn.comp continuousOn_fst fun z hz => hz.1).prodMk
        (hW.prodMk (hμ'.comp continuousOn_fst fun z hz => hz.1))
    have h4 := continuousOn_const (c := (-2 : ℝ)).mul ((continuous_form hg).comp_continuousOn h3)
    simp only [Function.comp_def] at h4
    rw [show D = fun z => -2 * form (g (μ z.1)) (W (μ z.1, z.2)) (deriv μ z.1) from funext hD]
    exact h4
  have h0η₀ : (0 : ℝ) ∈ Ioo (-η₀) η₀ := ⟨by linarith, hη₀⟩
  have hD0 : ∀ t ∈ Icc t₁ t₂, ((0 : ℝ), σ t) ∈ O ∧ 0 < D (0, σ t) := by
    intro t ht
    refine ⟨⟨h0η₀, by simpa [hμ0] using hKU' t ht⟩, ?_⟩
    have hμt0 : IsFutureTimelike g Y (σ 0) (deriv μ 0) := by simpa [hμ0] using hμt 0 h0η₀
    have hneg := hμt0.form_neg (hg.lorentzian _) (hg.globallyHyperbolic.timeOrientation.timelike _) hfut
    rw [form_comm (hg.lorentzian _).symm] at hneg
    rw [hD]
    simp only [hμ0, hWσ t ht, form_smul_left]
    nlinarith [(hIoo t ht).1]
  have hGσ : ∀ t ∈ Icc t₁ t₂, G (0, σ t) = 0 := fun t ht => by
    simp only [hG, worldFn_def, hμ0, hWσ t ht, form_smul_left, form_smul_right, hnull, mul_zero]
  set K := σ '' Icc t₁ t₂ with hK_def
  have hK : IsCompact K := isCompact_Icc.image_of_continuousOn
    (hσ.smooth.continuousOn.mono ((Icc_subset_Icc ht₁.le ht₂.le).trans hI))
  have hP : IsOpen (O ∩ D ⁻¹' Ioi 0) := hDc.isOpen_inter_preimage hO isOpen_Ioi
  obtain ⟨u, V, hu, hV, h0u, hKV, huV⟩ := generalized_tube_lemma
    (isCompact_singleton (x := (0 : ℝ))) hK hP (by
      rintro ⟨s, p⟩ ⟨hs, ⟨t, ht, rfl⟩⟩
      obtain rfl : s = 0 := hs
      exact hD0 t ht)
  obtain ⟨ε, hε, hεu⟩ := Metric.isOpen_iff.1 hu 0 (h0u rfl)
  set η := min (ε / 2) (η₀ / 2) with hη_def
  have hη : 0 < η := lt_min (half_pos hε) (half_pos hη₀)
  have hηη₀ : η < η₀ := (min_le_right _ _).trans_lt (half_lt_self hη₀)
  have hIccu : Icc (-η) η ⊆ u := fun s hs => hεu (by
    have := min_le_left (ε / 2) (η₀ / 2)
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    constructor <;> linarith [hs.1, hs.2])
  have hPV : ∀ p ∈ V, ∀ s ∈ Icc (-η) η, (s, p) ∈ O ∧ 0 < D (s, p) := fun p hp s hs =>
    huV ⟨hIccu hs, hp⟩
  have hmono : ∀ p ∈ V, StrictMonoOn (fun s => G (s, p)) (Icc (-η) η) := by
    intro p hp
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (fun s hs => (hGd _ (hPV p hp s hs).1).continuousAt.continuousWithinAt) fun s hs => ?_
    rw [interior_Icc] at hs
    rw [(hGd _ (hPV p hp s (Ioo_subset_Icc_self hs)).1).deriv]
    exact (hPV p hp s (Ioo_subset_Icc_self hs)).2
  have hGc : ∀ s ∈ Icc (-η) η, ContinuousOn (fun p => G (s, p)) V := fun s hs =>
    hGs.continuousOn.comp (continuousOn_const.prodMk continuousOn_id) fun p hp => (hPV p hp s hs).1
  have hηm : -η ∈ Icc (-η) η := ⟨le_rfl, by linarith⟩
  have hηp : η ∈ Icc (-η) η := ⟨by linarith, le_rfl⟩
  have h0η : (0 : ℝ) ∈ Icc (-η) η := ⟨by linarith, hη.le⟩
  set T := (V ∩ (fun p => G (-η, p)) ⁻¹' Iio 0) ∩ (fun p => G (η, p)) ⁻¹' Ioi 0 with hT_def
  have hT : IsOpen T := ((hGc η hηp).mono inter_subset_left).isOpen_inter_preimage
    ((hGc (-η) hηm).isOpen_inter_preimage hV isOpen_Iio) isOpen_Ioi
  have hTV : ∀ p ∈ T, p ∈ V := fun p hp => hp.1.1
  have hKT : K ⊆ T := by
    rintro _ ⟨t, ht, rfl⟩
    have hV' := hKV ⟨t, ht, rfl⟩
    refine ⟨⟨hV', ?_⟩, ?_⟩
    · show G (-η, σ t) < 0
      rw [← hGσ t ht]
      exact hmono _ hV' hηm h0η (by linarith)
    · show 0 < G (η, σ t)
      rw [← hGσ t ht]
      exact hmono _ hV' h0η hηp hη
  have hex : ∀ p ∈ T, ∃ s, s ∈ Ioo (-η) η ∧ G (s, p) = 0 := by
    intro p hp
    obtain ⟨s, hs, h⟩ := intermediate_value_Ioo (by linarith : -η ≤ η)
      (f := fun s => G (s, p)) (hGs.continuousOn.comp (continuousOn_id.prodMk continuousOn_const)
        fun s hs => (hPV p hp.1.1 s hs).1) ⟨hp.1.2, hp.2⟩
    exact ⟨s, hs, h⟩
  choose! φ hφI hφ0 using hex
  have hle : ∀ p ∈ T, ∀ s ∈ Ioo (-η) η, G (s, p) ≤ 0 ↔ s ≤ φ p := by
    intro p hp s hs
    rw [← hφ0 p hp]
    exact (hmono p (hTV p hp)).le_iff_le (Ioo_subset_Icc_self hs)
      (Ioo_subset_Icc_self (hφI p hp))
  have huniq : ∀ p ∈ T, ∀ s ∈ Ioo (-η) η, G (s, p) = 0 → s = φ p := fun p hp s hs h =>
    (hmono p (hTV p hp)).injOn (Ioo_subset_Icc_self hs) (Ioo_subset_Icc_self (hφI p hp))
      (h.trans (hφ0 p hp).symm)
  have hφσ : ∀ t ∈ Icc t₁ t₂, φ (σ t) = 0 := fun t ht =>
    (huniq _ (hKT ⟨t, ht, rfl⟩) 0 ⟨by linarith, hη⟩ (hGσ t ht)).symm
  have hTO : ∀ p ∈ T, ∀ s ∈ Ioo (-η) η, (s, p) ∈ O ∧ 0 < D (s, p) := fun p hp s hs =>
    hPV p (hTV p hp) s (Ioo_subset_Icc_self hs)
  have hφs : ∀ p ∈ T, ContDiffAt ℝ ∞ φ p := by
    intro p hp
    obtain ⟨hzO, hzD⟩ := hTO p hp _ (hφI p hp)
    have hGz := hGs.contDiffAt (hO.mem_nhds hzO)
    refine contDiffAt_of_eq_zero isOpen_Ioo hGz ?_ (hφI p hp) (hφ0 p hp) ?_
    · have h1 : HasDerivAt (fun s => G (s, p)) (fderiv ℝ G (φ p, p) (1, 0)) (φ p) :=
        (hGz.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq (φ p)
          (HasDerivAt.prodMk (hasDerivAt_id' (φ p)) (hasDerivAt_const (φ p) p)) rfl
      rw [← (hGd _ hzO).unique h1]
      exact hzD.ne'
    · filter_upwards [hT.mem_nhds hp] with p' hp' using huniq p' hp'
  have hdφ : ∀ p ∈ T, ∀ h, fderiv ℝ φ p h = -(2 / D (φ p, p)) *
      form (g p) (fderiv ℝ (expMap g (μ (φ p))) (W (μ (φ p), p)) (W (μ (φ p), p))) h := by
    intro p hp h
    obtain ⟨hzO, hzD⟩ := hTO p hp _ (hφI p hp)
    have hGz : HasFDerivAt G (fderiv ℝ G (φ p, p)) (φ p, p) :=
      ((hGs.contDiffAt (hO.mem_nhds hzO)).differentiableAt (by simp)).hasFDerivAt
    have hpair : HasFDerivAt (fun x => (φ x, x))
        ((fderiv ℝ φ p).prod (ContinuousLinearMap.id ℝ (E n))) p :=
      ((hφs p hp).differentiableAt (by simp)).hasFDerivAt.prodMk (hasFDerivAt_id p)
    have hcomp : HasFDerivAt (fun p' => G (φ p', p'))
        ((fderiv ℝ G (φ p, p)).comp ((fderiv ℝ φ p).prod (ContinuousLinearMap.id ℝ (E n)))) p :=
      HasFDerivAt.comp (g := G) (f := fun x => (φ x, x)) p hGz hpair
    have hzero : HasFDerivAt (fun p' => G (φ p', p')) (0 : E n →L[ℝ] ℝ) p :=
      (hasFDerivAt_const 0 p).congr_of_eventuallyEq
        (by filter_upwards [hT.mem_nhds hp] with p' hp' using hφ0 p' hp')
    have h0 := DFunLike.congr_fun (hcomp.unique hzero) h
    have hsplit : ((fderiv ℝ φ p h, h) : ℝ × E n) =
        fderiv ℝ φ p h • ((1 : ℝ), (0 : E n)) + ((0 : ℝ), h) := by
      ext <;> simp
    have h1 : fderiv ℝ G (φ p, p) (1, 0) = D (φ p, p) :=
      ((hGd _ hzO).unique (hGz.comp_hasDerivAt_of_eq (φ p)
        (HasDerivAt.prodMk (hasDerivAt_id' (φ p)) (hasDerivAt_const (φ p) p)) rfl)).symm
    have h2 : fderiv ℝ G (φ p, p) (0, h) = 2 * form (g p)
        (fderiv ℝ (expMap g (μ (φ p))) (W (μ (φ p), p)) (W (μ (φ p), p))) h := by
      obtain ⟨-, hval⟩ := hc.fderiv_worldFn_snd hg (q := (μ (φ p), p)) hzO.2
      have hx : HasFDerivAt (fun x => G (φ p, x))
          ((fderiv ℝ G (φ p, p)).comp (ContinuousLinearMap.inr ℝ ℝ (E n))) p :=
        hGz.comp p (hasFDerivAt_prodMk_right (φ p) p)
      have hfun : (fun x => G (φ p, x)) = fun x => worldFn g W (μ (φ p), x) := funext fun x => hG _
      rw [hfun] at hx
      have := DFunLike.congr_fun hx.fderiv h
      rw [hval] at this
      simpa using this.symm
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply, zero_apply] at h0
    rw [hsplit, map_add, map_smul, h1, h2, smul_eq_mul] at h0
    have hD' := hzD.ne'
    field_simp
    linarith
  have hV : ∀ p ∈ T, IsFutureCausal g Y p
      (fderiv ℝ (expMap g (μ (φ p))) (W (μ (φ p), p)) (W (μ (φ p), p))) ∧
      form (g p) (fderiv ℝ (expMap g (μ (φ p))) (W (μ (φ p), p)) (W (μ (φ p), p)))
        (fderiv ℝ (expMap g (μ (φ p))) (W (μ (φ p), p)) (W (μ (φ p), p))) = 0 := by
    intro p hp
    have hq := (hTO p hp _ (hφI p hp)).1.2
    have hU := hc.inv_mem _ hq
    have hQ : form (g (μ (φ p))) (W (μ (φ p), p)) (W (μ (φ p), p)) = 0 := by
      have := hφ0 p hp
      simpa only [hG, worldFn_def] using this
    have hw := (hfutU _ hU).2 hQ.le
    have := (hc.inExpDomain _ hU).isFutureCausal_fderiv hg hw
    have he := hc.expMap_inv _ hq
    dsimp only at this he
    rw [he] at this
    refine ⟨this, ?_⟩
    have := hc.worldFn_eq hg hq
    dsimp only at this
    rw [← this]
    simpa only [worldFn_def] using hQ
  have hgrad : ∀ p ∈ T, -grad g φ p = (2 / D (φ p, p)) •
      fderiv ℝ (expMap g (μ (φ p))) (W (μ (φ p), p)) (W (μ (φ p), p)) ∧
      coform g p (d φ p) (d φ p) = 0 := by
    intro p hp
    obtain ⟨h1, h2⟩ := grad_eq_smul_of_fderiv_eq hg (hdφ p hp)
    refine ⟨by rw [h1, ← neg_smul, neg_neg], ?_⟩
    rw [h2, (hV p hp).2, mul_zero]
  refine ⟨η, ⟨hη, hηη₀⟩, T, φ, ⟨hT, hKT, fun p hp => (hφs p hp).contDiffWithinAt, hφI,
    fun p hp => (hgrad p hp).2, ?_, ?_, hφσ, ?_, ?_, ?_⟩⟩
  · intro p hp h0
    have hD' := (hTO p hp _ (hφI p hp)).2
    have hg0 : grad g φ p = 0 := by
      simp [grad_def, h0]
      rfl
    have := (hgrad p hp).1
    rw [hg0, neg_zero, eq_comm, smul_eq_zero] at this
    rcases this with h | h
    · exact (div_pos two_pos hD').ne' h
    · exact (hV p hp).1.ne_zero h
  · intro p hp
    rw [(hgrad p hp).1]
    exact (hV p hp).1.smul (div_pos two_pos (hTO p hp _ (hφI p hp)).2)
  · intro t ht
    have hp := hKT ⟨t, ht, rfl⟩
    have := (hgrad _ hp).1
    rw [hφσ t ht, hμ0, hWσ t ht, hσ.fderiv_expMap_smul hg hI (hIoo t ht), smul_smul] at this
    exact ⟨2 / D (0, σ t) * t, mul_pos (div_pos two_pos (hD0 t ht).2) (hIoo t ht).1, this⟩
  · intro s hs
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, mem_causalFuture]
    constructor
    · rintro ⟨hx, hxT⟩
      refine ⟨hxT, (hle x hxT s hs).1 ?_⟩
      rw [hG]
      simpa only [worldFn_def] using ((hrel _ (hTO x hxT s hs).1.2).1).1 hx
    · rintro ⟨hxT, hsx⟩
      have := (hle x hxT s hs).2 hsx
      rw [hG] at this
      exact ⟨((hrel _ (hTO x hxT s hs).1.2).1).2 (by simpa only [worldFn_def] using this), hxT⟩
  · intro t ht C hC
    have ht0 := (hIoo t ht).1
    have hWc : ContinuousAt (fun x => W (σ 0, x)) (σ t) :=
      (hc.smooth.continuousOn.continuousAt (hc.isOpen'.mem_nhds (hKU' t ht))).comp
        (continuousAt_const.prodMk continuousAt_id)
    have hev : ∀ᶠ x in 𝓝 (σ t), ∀ r ∈ Icc (0 : ℝ) 1,
        expMap g (σ 0) (r • W (σ 0, x)) ∈ C := by
      refine isCompact_Icc.eventually_forall_of_forall_eventually fun r hr => ?_
      have hrt : r * t ∈ Icc 0 t := ⟨mul_nonneg hr.1 ht0.le, by nlinarith [hr.2]⟩
      have hsub : uIcc 0 (r * t) ⊆ I := (uIcc_subset_Icc ⟨le_rfl, ht0.le.trans (hIoo t ht).2.le⟩
        ⟨hrt.1, hrt.2.trans (hIoo t ht).2.le⟩).trans hI
      obtain ⟨hdom, hval⟩ := hσ.expMap_smul_eq hg hsub
      rw [← smul_smul] at hdom hval
      have h1 : Tendsto (fun z : E n × ℝ => W (σ 0, z.1)) (𝓝 (σ t, r))
          (𝓝 (t • deriv σ 0)) := by
        rw [← hWσ t ht]
        exact hWc.tendsto.comp continuousAt_fst
      have hlim : Tendsto (fun z : E n × ℝ => (σ 0, z.2 • W (σ 0, z.1))) (𝓝 (σ t, r))
          (𝓝 (σ 0, r • t • deriv σ 0)) :=
        tendsto_const_nhds.prodMk_nhds ((continuousAt_snd.tendsto).smul h1)
      have := (tendsto_expMap hg hdom).comp hlim
      rw [hval] at this
      exact this (mem_nhdsSet_iff_forall.1 hC _ ⟨r * t, hrt, rfl⟩)
    refine ⟨_, hev, fun x ⟨hxC, hxT⟩ hx0 => ?_⟩
    have hq : (σ 0, x) ∈ U' := by
      have : (μ 0, x) ∈ U' := (hTO x hxT 0 ⟨by linarith, hη⟩).1.2
      rwa [hμ0] at this
    have hU := hc.inv_mem _ hq
    have hQ : form (g (σ 0)) (W (σ 0, x)) (W (σ 0, x)) = 0 := by
      have := hφ0 x hxT
      rw [hx0, hG] at this
      simpa [worldFn_def, hμ0] using this
    exact ⟨W (σ 0, x), (hfutU _ hU).2 hQ.le, hQ, hc.inExpDomain _ hU, hc.expMap_inv _ hq, hxC⟩

end

end LorentzianCalderon
