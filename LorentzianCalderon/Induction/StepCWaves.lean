module

public import LorentzianCalderon.Induction.GWaves
public import LorentzianCalderon.Induction.CausalTransfer
public import LorentzianCalderon.Geometry.FirstArrival

public section

/-!
# The induction, Step C1: the waves of an admissible direction

Blueprint, Lemma `lem_ind_local_extension`, Step C1: for an admissible direction `ζ` at the
cluster point `p₀` of the frontier point `q₀`, the emission-time function `φ'` of `g'` along
`σ_ζ(t) = exp_{p₀}((t - 1) ζ)` (`lem_emission`, for a timelike line `μ` through `σ_ζ(0) ∈ O`),
its one-sided wave (`lem_onesided`) and the `g`-wave near `q₀` (`lem_g_waves`), with
`dφ'(p₀) = -c g'(ζ, ·)` for some `c > 0`.
-/

namespace LorentzianCalderon

noncomputable section
open Set Filter Matrix
open scoped ContDiff Topology

variable {n : ℕ}

/-- `dφ = g (grad φ)`. -/
theorem d_eq_mulVec_grad {g : MatrixField n} {x : E n} (hdet : (g x).det ≠ 0) (φ : E n → ℝ) :
    d φ x = g x *ᵥ (grad g φ x).ofLp := by
  have hgrad : (grad g φ x).ofLp = (g x)⁻¹ *ᵥ d φ x := by
    ext j
    simp [grad_def, mulVec, dotProduct]
  rw [hgrad, mulVec_mulVec, mul_nonsing_inv _ hdet.isUnit, one_mulVec]

namespace ExtensionProperty

variable {T : ℝ} {g g' : MatrixField n} {Y Y' : E n → E n} {ψ : E n → ℝ} {τ : ℝ}
  {Ψ : E n → E n} {Φ : ℝ → E n → E n}

/-- **The waves of an admissible direction** (Step C1 of `lem_ind_local_extension`). -/
theorem exists_waves (hP : ExtensionProperty g g' ψ (W n T) τ Ψ)
    (hgA : IsAdmissibleMetric n T g) (hg'A : IsAdmissibleMetric n T g')
    (hg : IsSpacetime g Y) (hg' : IsSpacetime g' Y')
    (hY : ∀ x ∉ M0 n T, form (g x) (EuclideanSpace.single 0 1) (Y x) < 0)
    (hY' : ∀ x ∉ M0 n T, form (g' x) (EuclideanSpace.single 0 1) (Y' x) < 0)
    (hC : CauchyDataSubset n T g g') (hψ : IsCauchyTemporal g Y ψ)
    (hΦ : Continuous fun p : ℝ × E n => Φ p.1 p.2) (hΦ0 : ∀ x, Φ 0 x = x)
    (hΦψ : ∀ t x, ψ (Φ t x) = ψ x + t)
    {m : ℕ} {v' : Fin m → E n → ℝ} (hv' : ∀ i, ContDiff ℝ ∞ (v' i))
    (hbox' : ∀ i x, box g' (v' i) x = 0)
    (himm : ∀ x ∈ W n T, Function.Injective (fderiv ℝ (fun y i => v' i y) x)) {q₀ p₀ : E n}
    (hq₀ : ψ q₀ = τ) (hq₀W : q₀ ∈ W n T) (hp₀W : p₀ ∈ W n T)
    (hlim : Tendsto Ψ (𝓝[A ψ τ] q₀) (𝓝 p₀)) (hp₀V : ∀ i, v' i p₀ = transfer n T g (v' i) q₀)
    {ζ : E n} (hζ : IsAdmissibleDirection g' Y' (O n T) p₀ ζ) :
    ∃ (φ' : E n → ℝ) (𝒯 : Set (E n)) (μ : ℝ → E n) (η : ℝ) (θ : E n → ℝ) (V' : Set (E n))
      (u' a' b' : ℝ → E n → ℝ) (F : ℝ → (E n → ℝ) → ℝ) (V : Set (E n)) (η₂ : ℝ)
      (φ : E n → ℝ) (u a b : ℝ → E n → ℝ) (c : ℝ),
      0 < c ∧ d φ' p₀ = -c • (g' p₀ *ᵥ ζ.ofLp) ∧ φ' p₀ = 0 ∧ IsFutureEikonal g' Y' φ' 𝒯 ∧
      IsOneSidedWave g' Y' φ' 𝒯 (O n T) μ η p₀ θ V' u' a' b' F ∧ 0 < η₂ ∧ η₂ ≤ η ∧
      IsFrontierWave g Y ψ τ Ψ φ' V' u' θ F q₀ V η₂ φ u a b := by
  obtain ⟨hfut, hnull, b, hb, t₁, ht₁, hdom, hnot, hO⟩ := isAdmissibleDirection_iff.1 hζ
  obtain ⟨hσ, hσ1'⟩ := isGeodesic_expMap_sub_one_smul hg' p₀ ζ
  set σ := fun t : ℝ => expMap g' p₀ ((t - 1) • ζ) with hσ_def
  have hI : Icc 0 b ⊆ { t : ℝ | InExpDomain g' p₀ ((t - 1) • ζ) } := fun t ht => hdom t ht
  have h1 : (1 : ℝ) ∈ Icc 0 b := ⟨zero_le_one, hb.le⟩
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, by linarith⟩
  have hσ1 : σ 1 = p₀ := by simp [σ, expMap_zero hg']
  have hfut1 : IsFutureCausal g' Y' (σ 1) (deriv σ 1) := by rw [hσ1, hσ1']; exact hfut
  have hfut0 : ∀ t ∈ Icc 0 b, IsFutureCausal g' Y' (σ t) (deriv σ t) := fun t ht =>
    hσ.isFutureCausal hg' hI ordConnected_Icc h1 hfut1 ht
  have hnull0 : ∀ t ∈ Icc 0 b, form (g' (σ t)) (deriv σ t) (deriv σ t) = 0 := fun t ht => by
    rw [hσ.form_deriv_eq hg' hI ordConnected_Icc ht h1, hσ1, hσ1', hnull]
  have hfirst : ¬ ChronLT g' Y' (σ 0) (σ b) := hnot
  -- the timelike line `μ` through `σ 0 ∈ O`
  have hσ0O : σ 0 ∈ O n T := hO 0 ⟨le_rfl, ht₁.1.le⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isOpen_O _ hσ0O
  set e₀ : E n := EuclideanSpace.single 0 1
  have he₀ : ‖e₀‖ = 1 := by simp [e₀]
  set μ : ℝ → E n := fun s => σ 0 + s • e₀
  have hμO : ∀ s ∈ Ioo (-r) r, μ s ∈ O n T := fun s hs => hball (by
    rw [Metric.mem_ball, dist_eq_norm]
    simp only [μ, add_sub_cancel_left, norm_smul, he₀, mul_one, Real.norm_eq_abs]
    exact abs_lt.2 hs)
  have hμd : ∀ s, HasDerivAt μ e₀ s := fun s => by
    have := ((hasDerivAt_id s).smul_const e₀).const_add (σ 0)
    rwa [one_smul] at this
  have hμs : ContDiffOn ℝ ∞ μ (Ioo (-r) r) := by
    simp only [μ]
    fun_prop
  have hμt : ∀ s ∈ Ioo (-r) r, IsFutureTimelike g' Y' (μ s) (deriv μ s) := by
    intro s hs
    have hM := not_mem_M0_of_mem_O (hμO s hs)
    rw [(hμd s).deriv]
    refine (isFutureTimelike_iff_of_minkowski (hg'A.minkowski_exterior _ hM)
      (hg'.globallyHyperbolic.timeOrientation.timelike _) (hY' _ hM)).2 ⟨?_, ?_⟩
    · rw [form_minkowski_single_zero, single_zero_apply_zero]
      norm_num
    · rw [single_zero_apply_zero]
      norm_num
  have hμ0 : μ 0 = σ 0 := by simp [μ]
  obtain ⟨η, hη, 𝒯, φ', hEF⟩ := exists_isEmissionFunction hg' hσ hI (hnull0 0 h0) (hfut0 0 h0)
    hfirst (t₁ := t₁ / 2) (t₂ := (1 + b) / 2) (by linarith [ht₁.1]) (by linarith) hr hμs hμt hμ0
  have hηr : Ioo (-η) η ⊆ Ioo (-r) r := Ioo_subset_Ioo (by linarith [hη.2]) hη.2.le
  have hE : IsEmission g' Y' σ b (t₁ / 2) ((1 + b) / 2) η 𝒯 φ' μ :=
    { geodesic := ⟨_, hσ, hI⟩
      null := hnull0
      future := hfut0
      notMem_chronFuture := fun h => hfirst (mem_chronFuture.1 h)
      t₁_pos := by linarith [ht₁.1]
      t₁_lt_one := by linarith [ht₁.2]
      one_lt_t₂ := by linarith
      t₂_lt := by linarith
      η_pos := hη.1
      image_subset := hEF.subset
      eikonal := ⟨hEF.isOpen, hEF.smooth, hEF.eikonal, hEF.d_ne_zero, hEF.future⟩
      mem_Ioo := hEF.mem_Ioo
      front := hEF.front
      tangent := hEF.tangent
      curve_smooth := hμs.mono hηr
      curve_timelike := fun s hs => hμt s (hηr hs)
      causalFuture_inter := hEF.causalFuture_inter }
  obtain ⟨θ, V', u', a', b', F, -, hw⟩ := hE.exists_isOneSidedWave hg' (t := t₁)
    ⟨by linarith [ht₁.1], ht₁.2⟩ isOpen_O (hO t₁ ⟨ht₁.1.le, le_rfl⟩)
  rw [hσ1] at hw
  have h1I : (1 : ℝ) ∈ Icc (t₁ / 2) ((1 + b) / 2) := ⟨by linarith [ht₁.2], by linarith⟩
  obtain ⟨V, η₂, φ, u, a, b₂, hη₂, hη₂η, hfw⟩ := hP.g_waves hgA hg'A hg hg' hY hY' hC hψ hΦ hΦ0
    hΦψ (fun x hx y hy hyx => hP.causalLE_transfer hgA hg'A hg hg' hY hY' hC hψ hΦ hΦ0 hΦψ hx
      hy hyx) hv' hbox' himm hq₀ hq₀W hp₀W hlim hp₀V hE hσ1 hw
  obtain ⟨c, hc, hgrad⟩ := hEF.tangent 1 h1I
  refine ⟨φ', 𝒯, μ, η, θ, V', u', a', b', F, V, η₂, φ, u, a, b₂, c, hc, ?_, ?_, hE.eikonal, hw,
    hη₂, hη₂η, hfw⟩
  · rw [hσ1, hσ1'] at hgrad
    rw [d_eq_mulVec_grad (hg'.det_ne_zero p₀), show grad g' φ' p₀ = -(c • ζ) by
      rw [← hgrad, neg_neg]]
    simp [mulVec_neg, mulVec_smul]
  · rw [← hσ1]
    exact hEF.front 1 h1I

end ExtensionProperty

end

end LorentzianCalderon
