module

public import LorentzianCalderon.Green.Periodize
public import LorentzianCalderon.Green.Sweep
public import LorentzianCalderon.Green.Coordinates
public import LorentzianCalderon.Green.Temporal

public section

/-!
# Existence of retarded solutions

`Facts.exists_retarded`. For a standard time
`ψ` with adapted chart `χ` (`IsStandardTime.exists_isAdaptedChart`), the equation
`□_{g_ε} V = F(s)` for the narrowed metric `g_ε = g + ε dψ²` becomes, for `v = V ∘ χ`, the normal
form `∂ₜ²v = a^{ij} ∂ᵢ∂ⱼv + b^μ ∂_μv + N² F(s) ∘ χ` (`IsAdaptedChart.box_narrow_eq_iff`), whose
coefficients are flat for `|y| > R`. With the parameters `l = (s, μ)` and
`ε = ε₁ · smoothTransition μ ∈ [0, ε₁]`, it satisfies `IsFlatNormalForm` (`isFlatNormalForm_ret`),
so it has solutions `v_m` on `{t < m}` (`IsFlatNormalForm.exists_local_solution`).

For `μ > 0`, i.e. `ε > 0`, the sweep (`support_subset_of_narrow`) shows that a solution of the
homogeneous equation off `J⁺(K)` vanishing in the past vanishes off `J⁺(K)`, up to the time
where it is a solution (`exists_sweep`). This gives both `v_m = 0` off `J⁺(K)` and
`v_m = v_{m'}` on `{t < min m m' - 1}`; by continuity both persist at `μ = 0`, i.e. for `g`
itself. Gluing the `v_m` at `μ = 0` gives the retarded solution.
-/

namespace LorentzianCalderon

noncomputable section
open Set Filter Function Matrix
open scoped ContDiff Topology

variable {n : ℕ}

/-- The narrowing parameter `ε = ε₁ · smoothTransition μ ∈ [0, ε₁]` for `l = (s, μ)`. -/
def retEps (ε₁ : ℝ) (l : Fin 2 → ℝ) : ℝ := ε₁ * Real.smoothTransition (l 1)

/-- The metric `χ^*(g + ε dψ²)` in adapted coordinates, at the parameter `l = (s, μ)`. -/
def retMetric (g : MatrixField n) (ψ : E n → ℝ) (χ : E n → E n) (ε₁ : ℝ) (l : Fin 2 → ℝ) :
    MatrixField n :=
  pullMetric (narrow g ψ (retEps ε₁ l)) χ

/-- `ε ≥ 0`. -/
theorem retEps_nonneg {ε₁ : ℝ} (h : 0 ≤ ε₁) (l : Fin 2 → ℝ) : 0 ≤ retEps ε₁ l :=
  mul_nonneg h (Real.smoothTransition.nonneg _)

/-- `ε ≤ ε₁`. -/
theorem retEps_le {ε₁ : ℝ} (h : 0 ≤ ε₁) (l : Fin 2 → ℝ) : retEps ε₁ l ≤ ε₁ :=
  mul_le_of_le_one_right h (Real.smoothTransition.le_one _)

/-- `ε > 0` for `μ > 0`. -/
theorem retEps_pos {ε₁ : ℝ} (h : 0 < ε₁) {l : Fin 2 → ℝ} (hl : 0 < l 1) : 0 < retEps ε₁ l :=
  mul_pos h (Real.smoothTransition.pos_of_pos hl)

/-- `ε = 0` for `μ ≤ 0`. -/
theorem retEps_of_nonpos {ε₁ : ℝ} {l : Fin 2 → ℝ} (hl : l 1 ≤ 0) : retEps ε₁ l = 0 := by
  simp [retEps, Real.smoothTransition.zero_of_nonpos hl]

/-- `ε` depends smoothly on `l`. -/
theorem contDiff_retEps (ε₁ : ℝ) : ContDiff ℝ ∞ (retEps ε₁) :=
  contDiff_const.mul (Real.smoothTransition.contDiff.comp (contDiff_apply ℝ ℝ 1))

namespace IsAdaptedChart

variable {g : MatrixField n} {Y : E n → E n} {ψ : E n → ℝ} {χ χinv : E n → E n} {ε₀ R : ℝ}
  (hg : IsSpacetime g Y) (hψ : IsStandardTime g Y ψ) (hχ : IsAdaptedChart g ψ χ χinv ε₀ R)

include hg hψ hχ

/-- `χ^*(g + ε dψ²)` is symmetric for `ε < ε₀`. -/
theorem pullMetric_narrow_symm {ε : ℝ} (hε : ε < ε₀) (z : E n) :
    (pullMetric (narrow g ψ ε) χ z)ᵀ = pullMetric (narrow g ψ ε) χ z := by
  simp only [pullMetric_def, transpose_mul, transpose_transpose,
    (hχ.isLorentzian_narrow hg hψ hε (χ z)).symm, Matrix.mul_assoc]

/-- The normal form of `□_{g_ε} V = F(s)` in adapted coordinates satisfies the hypotheses of the
periodization: `t₀` lies below `ψ(K)` and `R₀` bounds both the curved region and `χ⁻¹(K)`. -/
theorem isFlatNormalForm_ret {ε₁ : ℝ} (hε₁ : 0 < ε₁) (hε₁₀ : ε₁ < ε₀)
    {F : ℝ → E n → ℝ} (hF : ContDiff ℝ ∞ fun p : ℝ × E n => F p.1 p.2) {K : Set (E n)}
    (hsupp : ∀ s, Function.support (F s) ⊆ K) {R₀ t₀ : ℝ} (hR : R ≤ R₀)
    (hRK : ∀ x ∈ K, ‖spatial (χinv x)‖ ≤ R₀) (ht₀ : ∀ x ∈ K, t₀ < ψ x) :
    IsFlatNormalForm (fun i j l z => normalA (retMetric g ψ χ ε₁ l) z i j)
      (fun k l z => normalB (retMetric g ψ χ ε₁ l) z k)
      (fun l z => lapseSq (retMetric g ψ χ ε₁ l) z * F (l 0) (χ z))
      (fun l => 1 - retEps ε₁ l) R₀ t₀ := by
  have hlt : ∀ l, retEps ε₁ l < ε₀ := fun l => (retEps_le hε₁.le l).trans_lt hε₁₀
  have hmap : ContDiff ℝ ∞ fun q : (Fin 2 → ℝ) × E n => (retEps ε₁ q.1, q.2) :=
    ((contDiff_retEps ε₁).comp contDiff_fst).prodMk contDiff_snd
  have hcoeffs : ∀ q : (Fin 2 → ℝ) × E n,
      ContDiffAt ℝ ∞ (fun q : (Fin 2 → ℝ) × E n => lapseSq (retMetric g ψ χ ε₁ q.1) q.2) q ∧
      (∀ i j, ContDiffAt ℝ ∞
        (fun q : (Fin 2 → ℝ) × E n => normalA (retMetric g ψ χ ε₁ q.1) q.2 i j) q) ∧
      ∀ k, ContDiffAt ℝ ∞
        (fun q : (Fin 2 → ℝ) × E n => normalB (retMetric g ψ χ ε₁ q.1) q.2 k) q := by
    intro q
    obtain ⟨h1, h2, h3⟩ := hχ.contDiffAt_coeffs hg hψ (hlt q.1) q.2
    have hm : ContDiffAt ℝ ∞ (fun q : (Fin 2 → ℝ) × E n => (retEps ε₁ q.1, q.2)) q :=
      hmap.contDiffAt
    exact ⟨h1.comp (f := fun q : (Fin 2 → ℝ) × E n => (retEps ε₁ q.1, q.2)) q hm,
      fun i j => (h2 i j).comp (f := fun q : (Fin 2 → ℝ) × E n => (retEps ε₁ q.1, q.2)) q hm,
      fun k => (h3 k).comp (f := fun q : (Fin 2 → ℝ) × E n => (retEps ε₁ q.1, q.2)) q hm⟩
  have hKψ : ∀ z : E n, χ z ∈ K → t₀ < z 0 := fun z hz => hχ.time z ▸ ht₀ _ hz
  have hFz : ∀ s z, χ z ∉ K → F s (χ z) = 0 := fun s z hz => by
    by_contra h
    exact hz (hsupp s h)
  refine
    { smooth_A := fun i j => contDiff_iff_contDiffAt.2 fun q => (hcoeffs q).2.1 i j
      smooth_B := fun k => contDiff_iff_contDiffAt.2 fun q => (hcoeffs q).2.2 k
      smooth_S := contDiff_iff_contDiffAt.2 fun q => (hcoeffs q).1.mul
        (hF.comp ((contDiff_apply ℝ ℝ 0).comp contDiff_fst |>.prodMk
          (hχ.smooth.comp contDiff_snd))).contDiffAt
      symm := fun i j l z => normalA_symm (hχ.pullMetric_narrow_symm hg hψ (hlt l) z) i j
      pos := fun K' hK' => ?_
      c_pos := fun l => by linarith [retEps_le hε₁.le l, hχ.ε₀_le_one]
      c_le_one := fun l => by linarith [retEps_nonneg hε₁.le l]
      far_A := fun l z hz => (coeffs_of_far hχ (hlt l) (hR.trans_lt hz)).2.1
      far_B := fun l z hz => (coeffs_of_far hχ (hlt l) (hR.trans_lt hz)).2.2
      far_S := fun l z hz => by
        rw [hFz _ z fun hzK => ?_, mul_zero]
        have := hRK _ hzK
        rw [hχ.inv_apply] at this
        linarith
      past_S := fun l z hz => by
        rw [hFz _ z fun hzK => ?_, mul_zero]
        linarith [hKψ z hzK] }
  set f : (Fin 2 → ℝ) × ℝ → ℝ × ℝ := fun q => (retEps ε₁ q.1, q.2)
  have hf : Continuous f :=
    ((contDiff_retEps ε₁).continuous.comp continuous_fst).prodMk continuous_snd
  obtain ⟨κ, hκ, hpos⟩ := hχ.exists_pos_uniform hg hψ (hK'.image hf)
    (by rintro _ ⟨q, -, rfl⟩; exact hlt q.1)
  exact ⟨κ, hκ, fun l z hlz ξ => hpos (f (l, z 0)) ⟨_, hlz, rfl⟩ z rfl ξ⟩

/-- **The sweep in adapted coordinates.** For small `ε > 0`: a function `w` that is smooth on
`{t < T}`, vanishes on `{t < t₀}`, and solves the homogeneous normal form of `□_{g_ε}` at the
points of `{t < T}` outside `χ⁻¹(J⁺(K))` vanishes there on `{t < T - 1}`
(`support_subset_of_narrow`, applied to `w ∘ χ⁻¹` cut off in time and to `K ∪ {ψ ≥ T - 1}`). -/
theorem exists_sweep : ∃ εs > 0, ∀ ε ∈ Ioc 0 εs, ε < ε₀ → ∀ {K : Set (E n)} {w : E n → ℝ}
    {T t₀ : ℝ}, (∀ z, z 0 < T → ContDiffAt ℝ ∞ w z) → (∀ z, z 0 < t₀ → w z = 0) →
    (∀ z, z 0 < T → χ z ∉ causalFutureSet g Y K →
      d2 w z 0 0 = ∑ i, ∑ j, normalA (pullMetric (narrow g ψ ε) χ) z i j * d2 w z i.succ j.succ +
        ∑ k, normalB (pullMetric (narrow g ψ ε) χ) z k * d w z k) →
    ∀ z, z 0 < T - 1 → χ z ∉ causalFutureSet g Y K → w z = 0 := by
  obtain ⟨εs, hεs, hsw⟩ := support_subset_of_narrow hg hψ
  refine ⟨εs, hεs, fun ε hε hε₀ K w T t₀ hw hw0 heq z hzT hzK => ?_⟩
  set ρ : ℝ → ℝ := fun τ => 1 - Real.smoothTransition (2 * (τ - (T - 1)))
  have hρ1 : ∀ τ, τ ≤ T - 1 → ρ τ = 1 := fun τ hτ => by
    simp [ρ, Real.smoothTransition.zero_of_nonpos (by linarith : 2 * (τ - (T - 1)) ≤ 0)]
  have hρ0 : ∀ τ, T - 1 / 2 ≤ τ → ρ τ = 0 := fun τ hτ => by
    simp [ρ, Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 2 * (τ - (T - 1)))]
  have hρs : ContDiff ℝ ∞ ρ :=
    contDiff_const.sub (Real.smoothTransition.contDiff.comp
      (contDiff_const.mul (contDiff_id.sub contDiff_const)))
  set W : E n → ℝ := fun x => ρ (ψ x) * w (χinv x)
  have hχinv0 : ∀ x, (χinv x) 0 = ψ x := fun x => by rw [← hχ.time, hχ.apply_inv]
  have hW : ContDiff ℝ ∞ W := contDiff_iff_contDiffAt.2 fun x => by
    by_cases hx : ψ x < T
    · exact ((hρs.comp hψ.smooth).contDiffAt).mul
        ((hw _ (by rw [hχinv0]; exact hx)).comp x hχ.smooth_inv.contDiffAt)
    · push Not at hx
      refine contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_lt continuous_const hψ.smooth.continuous).mem_nhds
        (show T - 1 / 2 < ψ x by linarith)] with x' hx'
      simp [W, hρ0 _ (le_of_lt hx')]
  have hWχ : ∀ z' : E n, z' 0 ≤ T - 1 → W (χ z') = w z' := fun z' hz' => by
    simp only [W, hχ.time, hχ.inv_apply, hρ1 _ hz', one_mul]
  set K' := K ∪ {x | T - 1 ≤ ψ x}
  have hsub := hsw ε hε (K := K') (V := W) (t₀ := t₀) (hW.of_le (by simp)) (fun x hx => ?_)
    (fun x hx => by simp [W, hw0 _ (by rw [hχinv0]; exact hx)])
  · by_contra hne
    have hmem : χ z ∈ causalFutureSet g Y K' := hsub (by
      rw [Function.mem_support, hWχ z hzT.le]
      exact hne)
    obtain ⟨p, hp, hpz⟩ := mem_causalFutureSet.1 hmem
    rcases hp with hp | hp
    · exact hzK (mem_causalFutureSet.2 ⟨p, hp, hpz⟩)
    · have := le_of_causalLE hg (hψ.smooth.differentiable (by simp)) hψ.past_gradient
        (mem_causalFuture.1 hpz)
      rw [hχ.time] at this
      simp only [mem_ofPred_eq] at hp
      linarith
  · have hxK' : x ∉ K' := fun h => hx (mem_causalFutureSet.2 ⟨x, h, mem_causalFuture_self x⟩)
    have hxψ : ψ x < T - 1 := by
      by_contra h
      exact hxK' (Or.inr (not_lt.1 h))
    have hxK : x ∉ causalFutureSet g Y K := fun h => hx (by
      obtain ⟨p, hp, hpx⟩ := mem_causalFutureSet.1 h
      exact mem_causalFutureSet.2 ⟨p, Or.inl hp, hpx⟩)
    set z' := χinv x
    have hx' : x = χ z' := (hχ.apply_inv x).symm
    have hz'0 : z' 0 < T - 1 := by rw [hχinv0]; exact hxψ
    have hev : W ∘ χ =ᶠ[𝓝 z'] w := by
      filter_upwards [(isOpen_lt (contDiff_coordinate 0).continuous continuous_const).mem_nhds
        hz'0] with z'' hz''
      exact hWχ z'' hz''.le
    rw [hx']
    refine (hχ.box_narrow_eq_iff hg hψ hε₀ (hW.contDiffAt.of_le (by simp)) 0).2 ?_
    simp only [d2_congr hev, d_congr hev, mul_zero, add_zero]
    exact heq z' (by linarith) (by rwa [← hx'])

end IsAdaptedChart

/-- `∂ᵢ∂ⱼ(u - v) = ∂ᵢ∂ⱼu - ∂ᵢ∂ⱼv` for `C²` functions. -/
theorem d2_sub {u v : E n → ℝ} {x : E n} (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x)
    (i j : Fin (n + 1)) : d2 (fun y => u y - v y) x i j = d2 u x i j - d2 v x i j := by
  have hev : (fun y => d (fun y => u y - v y) y j) =ᶠ[𝓝 x] fun y => d u y j - d v y j := by
    filter_upwards [hu.eventually (by simp), hv.eventually (by simp)] with y hy1 hy2
    exact d_sub (hy1.differentiableAt (by simp)) (hy2.differentiableAt (by simp)) j
  rw [d2_def, d_congr hev, d_sub (differentiableAt_d hu j) (differentiableAt_d hv j), d2_def,
    d2_def]

/-- A function of `μ`, continuous at `0` and vanishing for `μ > 0`, vanishes at `0`. -/
theorem eq_zero_of_pos_of_continuousAt {f : ℝ → ℝ} (hf : ContinuousAt f 0)
    (h : ∀ μ, 0 < μ → f μ = 0) : f 0 = 0 := by
  have h1 : Tendsto f (𝓝[>] 0) (𝓝 (f 0)) := hf.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto f (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun μ hμ => (h μ hμ).symm)
  exact tendsto_nhds_unique h1 h2

/-- `x ↦ (f x, 0)` is smooth. -/
theorem contDiff_vecCons_zero {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : X → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ fun x => (![f x, 0] : Fin 2 → ℝ) := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases i
  · simpa using hf
  · simpa using contDiff_const

/-- **Existence of retarded solutions**, depending smoothly on a parameter: for a jointly smooth
family of sources `F s` supported in a fixed compact set `K` there are solutions of
`□_g (V s) = F s` supported in `J⁺(K)`, jointly smooth in `(s, x)`. This was cited from
Bär–Ginoux–Pfäffle, Wave equations on Lorentzian manifolds and quantization, Corollary 3.4.3,
p. 89 (with Theorems 3.2.11, p. 84, 3.2.12, p. 86, and 3.3.1, p. 87); it is proved here by
Fourier–Galerkin approximation on a torus in adapted coordinates (`PDE.exists_periodic_solution`,
`IsFlatNormalForm.exists_local_solution`) and the sweep for narrowed metrics
(`support_subset_of_narrow`). -/
theorem Facts.exists_retarded {g : MatrixField n} {Y : E n → E n} (hg : IsSpacetime g Y)
    {F : ℝ → E n → ℝ} (hF : ContDiff ℝ ∞ fun p : ℝ × E n => F p.1 p.2) {K : Set (E n)}
    (hK : IsCompact K) (hsupp : ∀ s, Function.support (F s) ⊆ K) :
    ∃ V : ℝ → E n → ℝ, (ContDiff ℝ ∞ fun p : ℝ × E n => V p.1 p.2) ∧
      ∀ s, (∀ x, box g (V s) x = F s x) ∧ Function.support (V s) ⊆ causalFutureSet g Y K := by
  obtain ⟨ψ, hψ⟩ := exists_standardTime hg
  obtain ⟨χ, χinv, ε₀, R, hχ⟩ := hψ.exists_isAdaptedChart hg
  obtain ⟨εs, hεs, hsweep⟩ := hχ.exists_sweep hg hψ
  set ε₁ := min (ε₀ / 2) εs
  have hε₁ : 0 < ε₁ := lt_min (half_pos hχ.ε₀_pos) hεs
  have hε₁₀ : ε₁ < ε₀ := (min_le_left _ _).trans_lt (half_lt_self hχ.ε₀_pos)
  obtain ⟨RK, hRK⟩ : ∃ RK, ∀ x ∈ K, ‖spatial (χinv x)‖ ≤ RK := by
    obtain ⟨C, hC⟩ := (hK.image hχ.smooth_inv.continuous).isBounded.exists_norm_le
    exact ⟨C, fun x hx => (norm_spatial_le _).trans (hC _ ⟨x, hx, rfl⟩)⟩
  obtain ⟨m₀, hm₀⟩ := hK.bddBelow_image hψ.smooth.continuous.continuousOn
  have hflat := hχ.isFlatNormalForm_ret hg hψ hε₁ hε₁₀ hF hsupp (R₀ := max R RK) (t₀ := m₀ - 1)
    (le_max_left _ _) (fun x hx => (hRK x hx).trans (le_max_right _ _))
    (fun x hx => by linarith [hm₀ ⟨x, hx, rfl⟩])
  choose v hvs hv0 hveq using fun m : ℕ => hflat.exists_local_solution (m : ℝ)
  have hslice : ∀ (m : ℕ) l (z : E n), z 0 < m → ContDiffAt ℝ ∞ (v m l) z := fun m l z hz =>
    (hvs m l z hz).comp (f := fun w : E n => (l, w)) z (contDiffAt_const.prodMk contDiffAt_id)
  have hεl : ∀ l, retEps ε₁ l < ε₀ := fun l => (retEps_le hε₁.le l).trans_lt hε₁₀
  have hεs' : ∀ l, 0 < l 1 → retEps ε₁ l ∈ Ioc 0 εs := fun l hl =>
    ⟨retEps_pos hε₁ hl, (retEps_le hε₁.le l).trans (min_le_right _ _)⟩
  have hsupp_pos : ∀ (m : ℕ) l z, 0 < l 1 → z 0 < (m : ℝ) - 1 →
      χ z ∉ causalFutureSet g Y K → v m l z = 0 := by
    intro m l z hl hz hzK
    refine hsweep _ (hεs' l hl) (hεl l) (K := K) (w := v m l) (T := m) (t₀ := m₀ - 1)
      (fun z hz => hslice m l z hz) (fun z hz => hv0 m l z hz.le) (fun z hz hzK => ?_) z hz hzK
    have hF0 : F (l 0) (χ z) = 0 := by
      by_contra h
      exact hzK (mem_causalFutureSet.2 ⟨χ z, hsupp _ h, mem_causalFuture_self _⟩)
    rw [hveq m l z hz, hF0, mul_zero, add_zero]
    rfl
  have hagree_pos : ∀ (m m' : ℕ) l z, 0 < l 1 → z 0 < min (m : ℝ) m' - 1 →
      v m l z = v m' l z := by
    intro m m' l z hl hz
    have hT : ∀ z : E n, z 0 < min (m : ℝ) m' → z 0 < m ∧ z 0 < m' := fun z hz =>
      ⟨hz.trans_le (min_le_left _ _), hz.trans_le (min_le_right _ _)⟩
    have := hsweep _ (hεs' l hl) (hεl l) (K := ∅) (w := fun w => v m l w - v m' l w)
      (T := min (m : ℝ) m') (t₀ := m₀ - 1)
      (fun z hz => (hslice m l z (hT z hz).1).sub (hslice m' l z (hT z hz).2))
      (fun z hz => by simp [hv0 m l z hz.le, hv0 m' l z hz.le]) (fun z hz _ => ?_) z hz
      (by simp [causalFutureSet_def])
    · exact sub_eq_zero.1 this
    · obtain ⟨h1, h2⟩ := hT z hz
      have hc1 := (hslice m l z h1).of_le (by simp : (2 : WithTop ℕ∞) ≤ ∞)
      have hc2 := (hslice m' l z h2).of_le (by simp : (2 : WithTop ℕ∞) ≤ ∞)
      have hd : ∀ k, d (fun w => v m l w - v m' l w) z k = d (v m l) z k - d (v m' l) z k :=
        fun k => d_sub (hc1.differentiableAt (by simp)) (hc2.differentiableAt (by simp)) k
      simp only [d2_sub hc1 hc2, hd, hveq m l z h1, hveq m' l z h2, mul_sub,
        Finset.sum_sub_distrib, retMetric]
      ring
  have hcont : ∀ (m : ℕ) s (z : E n), z 0 < m →
      ContinuousAt (fun μ : ℝ => v m ![s, μ] z) 0 := fun m s z hz => by
    have h := (hvs m ![s, 0] z hz).continuousAt
    have hc : Continuous fun μ : ℝ => (![s, μ] : Fin 2 → ℝ) :=
      continuous_pi fun i => by
        fin_cases i
        · simpa using continuous_const
        · exact continuous_id'
    exact h.comp (f := fun μ : ℝ => ((![s, μ] : Fin 2 → ℝ), z))
      (hc.prodMk continuous_const).continuousAt
  have hsupp0 : ∀ (m : ℕ) s z, z 0 < (m : ℝ) - 1 → χ z ∉ causalFutureSet g Y K →
      v m ![s, 0] z = 0 := fun m s z hz hzK =>
    eq_zero_of_pos_of_continuousAt (f := fun μ => v m ![s, μ] z) (hcont m s z (by linarith))
      fun μ hμ => hsupp_pos m _ z (by simpa using hμ) hz hzK
  have hagree0 : ∀ (m m' : ℕ) s z, z 0 < min (m : ℝ) m' - 1 →
      v m ![s, 0] z = v m' ![s, 0] z := fun m m' s z hz => by
    have hm : z 0 < m := by linarith [min_le_left (m : ℝ) m']
    have hm' : z 0 < m' := by linarith [min_le_right (m : ℝ) m']
    have := eq_zero_of_pos_of_continuousAt (f := fun μ => v m ![s, μ] z - v m' ![s, μ] z)
      ((hcont m s z hm).sub (hcont m' s z hm'))
      fun μ hμ => sub_eq_zero.2 (hagree_pos m m' _ z (by simpa using hμ) hz)
    exact sub_eq_zero.1 this
  set M : E n → ℕ := fun z => ⌈z 0⌉₊ + 3
  have hM : ∀ z : E n, z 0 < (M z : ℝ) - 1 := fun z => by
    have := Nat.le_ceil (z 0)
    simp only [M]
    push_cast
    linarith
  set V : ℝ → E n → ℝ := fun s x => v (M (χinv x)) ![s, 0] (χinv x)
  have hloc : ∀ x₀ : E n, ∀ᶠ x in 𝓝 x₀, ∀ s,
      V s x = v (M (χinv x₀) + 1) ![s, 0] (χinv x) := by
    intro x₀
    have hc : Continuous fun x => χinv x 0 :=
      (contDiff_coordinate 0).continuous.comp hχ.smooth_inv.continuous
    filter_upwards [hc.continuousAt.eventually (gt_mem_nhds (lt_add_one (χinv x₀ 0)))]
      with x hx s
    refine hagree0 _ _ s _ ?_
    have h1 := hM (χinv x)
    have h2 := Nat.le_ceil (χinv x₀ 0)
    rw [lt_sub_iff_add_lt, lt_min_iff]
    simp only [M] at h1 ⊢
    push_cast at h1 ⊢
    constructor <;> linarith
  have hlocT : ∀ x₀ : E n, χinv x₀ 0 < ((M (χinv x₀) + 1 : ℕ) : ℝ) := fun x₀ => by
    have := hM (χinv x₀)
    push_cast
    linarith
  have hsmooth : ContDiff ℝ ∞ fun p : ℝ × E n => V p.1 p.2 := by
    refine contDiff_iff_contDiffAt.2 fun ⟨s₀, x₀⟩ => ?_
    have hev : (fun p : ℝ × E n => V p.1 p.2) =ᶠ[𝓝 (s₀, x₀)]
        fun p => v (M (χinv x₀) + 1) ![p.1, 0] (χinv p.2) :=
      ((continuous_snd.tendsto (s₀, x₀)).eventually (hloc x₀)).mono fun p hp => hp p.1
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    have hf : ContDiff ℝ ∞ fun p : ℝ × E n => ((![p.1, 0] : Fin 2 → ℝ), χinv p.2) :=
      (contDiff_vecCons_zero contDiff_fst).prodMk (hχ.smooth_inv.comp contDiff_snd)
    exact (hvs _ ![s₀, 0] (χinv x₀) (hlocT x₀)).comp
      (f := fun p : ℝ × E n => ((![p.1, 0] : Fin 2 → ℝ), χinv p.2)) (s₀, x₀) hf.contDiffAt
  have hret0 : ∀ s, retMetric g ψ χ ε₁ ![s, 0] = pullMetric (narrow g ψ 0) χ := fun s => by
    simp [retMetric, retEps_of_nonpos]
  refine ⟨V, hsmooth, fun s => ⟨fun x => ?_, fun x hx => ?_⟩⟩
  · set z := χinv x
    have hVs : ContDiffAt ℝ 2 (V s) (χ z) := by
      rw [hχ.apply_inv]
      exact ((hsmooth.comp (contDiff_const.prodMk contDiff_id)).contDiffAt).of_le (by simp)
    have hev : V s ∘ χ =ᶠ[𝓝 z] v (M (χinv x) + 1) ![s, 0] := by
      have := (hχ.smooth.continuous.tendsto z).eventually (hloc (χ z))
      rw [hχ.apply_inv] at this
      filter_upwards [this] with w hw
      simp only [Function.comp, hw s, hχ.inv_apply]
    have key := (hχ.box_narrow_eq_iff hg hψ (ε := 0) hχ.ε₀_pos hVs (F s (χ z))).2 (by
      simp only [d2_congr hev, d_congr hev]
      have := hveq _ ![s, 0] z (hlocT x)
      simpa [hret0] using this)
    rwa [narrow_zero, hχ.apply_inv] at key
  · by_contra hxK
    exact hx (hsupp0 _ s _ (hM _) (by rwa [hχ.apply_inv]))

end

end LorentzianCalderon
