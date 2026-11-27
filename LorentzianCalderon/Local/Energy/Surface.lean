module

public import LorentzianCalderon.Local.Energy.SurfaceAux

public section

/-!
# The integrated surface estimate

The surface term of the blueprint's `eq_energy`, integrated over `s ∈ [s₁, s₂]`: by the coarea
formula, `∫ ds ∫_{Γ_s ∩ L} (…) dμ_s` is a volume integral over `L ∩ {s₁ ≤ φ ≤ s₂}` with
`s = φ(x)`. We integrate the identity of Step 3 over `s` and let `ε → 0`: by Fubini,
`∫ ds G_ε(s) = ∫ dx ∫ ds H'_ε(φ(x) - s) (…)`, and the mollifier in `s` converges to the
evaluation at `s = φ(x)`.
-/

namespace LorentzianCalderon

noncomputable section
open Set MeasureTheory Filter Topology
open scoped ContDiff

variable {n : ℕ}

namespace EnergySetting

variable {V : Set (E n)} {g : MatrixField n} {Y : E n → E n} {ψ ψ' : E n → ℝ} {τ c : ℝ}
  (h : EnergySetting V g Y ψ ψ' τ c)
include h

omit h in
theorem measure_prod_restrict_eq (S : Set ℝ) (T : Set (E n)) :
    (volume.restrict S).prod (volume.restrict T) = volume.restrict (S ×ˢ T) := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]

/-- **Integrated surface estimate**: for a family `w s` of functions, jointly `C²` in `(s, x)`
on `ℝ × U` for a neighbourhood `U` of the lens `L`, with `w s = 0` and `d(w s) = 0` on
`{ψ = τ} ∩ {φ ≥ s} ∩ L` for `s ∈ [s₁, s₂]`, and `Z = -grad φ`,
`σ ∫_{L ∩ {s₁ ≤ φ ≤ s₂}} e^{2σψ(x)} ((Z w_{φ(x)})(x)² + σ² w_{φ(x)}(x)²) dx ≤
  C ∫_{s₁}^{s₂} ∫_{L ∩ {φ > s}} e^{2σψ} |□_g w_s|² dx ds`. -/
theorem energy_surface {φ : E n → ℝ} (hφ : IsEikonal V g Y φ) :
    ∃ C σ₀ : ℝ, ∀ σ ≥ σ₀, ∀ (s₁ s₂ : ℝ) (U : Set (E n)) (w : ℝ → E n → ℝ), s₁ ≤ s₂ →
      IsOpen U → lens V ψ ψ' τ c ⊆ U →
      ContDiffOn ℝ 2 (fun p : ℝ × E n => w p.1 p.2) (univ ×ˢ U) →
      (∀ s ∈ Icc s₁ s₂, ∀ x ∈ lens V ψ ψ' τ c, ψ x = τ → s ≤ φ x →
        w s x = 0 ∧ fderiv ℝ (w s) x = 0) →
      σ * ∫ x in lens V ψ ψ' τ c ∩ {x | s₁ ≤ φ x ∧ φ x ≤ s₂},
          Real.exp (2 * σ * ψ x) *
            (fderiv ℝ (w (φ x)) x (-grad g φ x) ^ 2 + σ ^ 2 * w (φ x) x ^ 2) ≤
        C * ∫ s in s₁..s₂, ∫ x in lens V ψ ψ' τ c ∩ {x | s < φ x},
          Real.exp (2 * σ * ψ x) * box g (w s) x ^ 2 := by
  obtain ⟨ε₀, hε₀, a, ha, b, hb, σ₀, hσ₀, hstep⟩ := h.step1
  obtain ⟨c₃, hc₃, hlow⟩ := h.exists_null_flux_lower hφ hε₀
  refine ⟨b / c₃, σ₀, fun σ hσ s₁ s₂ U w hs hU hLU hW hvan => ?_⟩
  have hσ0 : 0 < σ := lt_of_lt_of_le hσ₀ hσ
  have hLV := h.lens_subset (ψ := ψ) (ψ' := ψ') (τ := τ) (c := c)
  have hLUV : lens V ψ ψ' τ c ⊆ U ∩ V := subset_inter hLU hLV
  have hLc : IsCompact (lens V ψ ψ' τ c) := h.isCompact
  have hLm : MeasurableSet (lens V ψ ψ' τ c) := hLc.measurableSet
  set L := lens V ψ ψ' τ c with hLdef
  set lam := ε₀ ^ 2 * σ ^ 2 with hlam_def
  have hlam : 0 ≤ lam := by positivity
  have hvan' : ∀ s ∈ Icc s₁ s₂, ∀ x ∈ L, ψ x = τ → s ≤ φ x → w s x = 0 ∧ d (w s) x = 0 := by
    intro s hs' x hx h1 h2
    obtain ⟨h3, h4⟩ := hvan s hs' x hx h1 h2
    exact ⟨h3, by ext i; simp [d_def, h4]⟩
  have hws : ∀ s, ContDiffOn ℝ 2 (w s) U := family_contDiffOn hW
  have hψc : ContinuousOn ψ V := h.smooth_ψ.continuousOn
  have hψ'c : ContinuousOn ψ' V := h.smooth_ψ'.continuousOn
  have hφc : ContinuousOn φ V := hφ.smooth.continuousOn
  have hE : ContinuousOn (fun x => Real.exp (2 * σ * ψ x)) V :=
    Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hψc)
  have hsub : Icc s₁ s₂ ×ˢ L ⊆ univ ×ˢ (U ∩ V) := fun p hp => ⟨mem_univ _, hLUV hp.2⟩
  have hsub' : Icc s₁ s₂ ×ˢ L ⊆ (univ ×ˢ U : Set (ℝ × E n)) := fun p hp => ⟨mem_univ _, hLU hp.2⟩
  have hKc : IsCompact (Icc s₁ s₂ ×ˢ L) := isCompact_Icc.prod hLc
  have hKm : MeasurableSet (Icc s₁ s₂ ×ˢ L) := hKc.measurableSet
  have hsnd : ∀ {f : E n → ℝ}, ContinuousOn f V →
      ContinuousOn (fun p : ℝ × E n => f p.2) (Icc s₁ s₂ ×ˢ L) := fun hf =>
    hf.comp continuousOn_snd fun p hp => hLV hp.2
  -- the terms of Step 1 for each `w s`
  set N : ℝ → E n → ℝ := fun s x =>
    a * σ * (Real.exp (2 * σ * ψ x) * (‖d (w s) x‖ ^ 2 + σ ^ 2 * w s x ^ 2)) with hNdef
  set B : ℝ → E n → ℝ := fun s x =>
    b / σ * (Real.exp (2 * σ * ψ x) * box g (w s) x ^ 2) with hBdef
  have hBc : ContinuousOn (fun p : ℝ × E n => B p.1 p.2) (Icc s₁ s₂ ×ˢ L) :=
    continuousOn_const.mul ((hsnd hE).mul (((h.family_continuousOn_box hU hW).mono hsub).pow 2))
  have hNs : ∀ s, ContinuousOn (N s) L := fun s =>
    continuousOn_const.mul ((hE.mono hLV).mul (((h.continuousOn_norm_d hU (hws s)).mono hLU).pow
      2 |>.add (continuousOn_const.mul (((hws s).continuousOn.mono hLU).pow 2))))
  have hBs : ∀ s, ContinuousOn (B s) L := fun s =>
    continuousOn_const.mul ((hE.mono hLV).mul (((h.continuousOn_box hU (hws s)).mono hLUV).pow 2))
  have hB0 : ∀ s, ∀ x ∈ L, 0 ≤ B s x := fun s x _ => by
    simp only [hBdef]; have := Real.exp_pos (2 * σ * ψ x); positivity
  have hN0 : ∀ s, ∀ x ∈ L, 0 ≤ N s x := fun s x _ => by
    simp only [hNdef]; have := Real.exp_pos (2 * σ * ψ x); positivity
  have hdiv : ∀ s, ∀ x ∈ L, ∑ j, d (current g ψ (w s) σ lam j) x j ≤ B s x - N s x := by
    intro s x hx
    have := hstep σ hσ (w s) x hx ((hws s).contDiffAt (hU.mem_nhds (hLU hx)))
    simp only [hBdef, hNdef]
    linarith
  -- the volume integral on `L ∩ {φ > s}`
  set I : ℝ → ℝ := fun s => ∫ x in L ∩ {x | s < φ x}, B s x with hIdef
  -- (i) the inequality for each `s` and each cut-off
  have hcore : ∀ s ε, 0 < ε → ∫ x in L, fluxG g ψ ψ' φ (w s) τ c σ lam s ε x ≤
      (∫ x in L, fluxA g ψ ψ' φ (w s) τ c σ lam s ε x) + I s := by
    intro s ε hε
    have h1 := h.core_eps hφ.smooth hU hLU (hws s) hlam (hNs s) (hBs s) (hB0 s) (hdiv s) s hε
    have h2 : 0 ≤ ∫ x in L, chi ψ ψ' φ τ c s ε x * N s x :=
      setIntegral_nonneg hLm fun x hx => mul_nonneg (chi_nonneg _ _ _ _ _ _ _ _) (hN0 s x hx)
    linarith
  -- (ii) integrability on the product `[s₁, s₂] × L`
  set FG : ℝ → ℝ × E n → ℝ := fun ε p => fluxG g ψ ψ' φ (w p.1) τ c σ lam p.1 ε p.2
    with hFGdef
  have hwTc : ContinuousOn (fun p : ℝ × E n => wT g ψ (w p.1) σ lam φ p.2) (Icc s₁ s₂ ×ˢ L) :=
    (h.family_continuousOn_wT hU hW σ lam hφ.smooth).mono hsub
  have hFGc : ∀ ε, ContinuousOn (FG ε) (Icc s₁ s₂ ×ˢ L) := by
    intro ε
    simp only [hFGdef, fluxG_def]
    exact (((continuous_cutoff.comp_continuousOn ((continuousOn_const.sub (hsnd hψc)).div_const
      _)).mul (continuous_cutoff.comp_continuousOn (((hsnd hψ'c).sub continuousOn_const).div_const
        _))).mul ((continuous_cutoffDeriv.comp_continuousOn (((hsnd hφc).sub
          continuousOn_fst).div_const _)).mul continuousOn_const)).mul hwTc
  have hFGi : ∀ ε, Integrable (FG ε) ((volume.restrict (Icc s₁ s₂)).prod (volume.restrict L)) := by
    intro ε; rw [measure_prod_restrict_eq]; exact (hFGc ε).integrableOn_compact hKc
  set O : Set (ℝ × E n) := {p | p.2 ∈ V ∧ p.1 < φ p.2} with hOdef
  have hO : IsOpen O := by
    have hc : ContinuousOn (fun p : ℝ × E n => φ p.2 - p.1) (univ ×ˢ V) :=
      (hφc.comp continuousOn_snd fun p hp => hp.2).sub continuousOn_fst
    have := hc.isOpen_inter_preimage (isOpen_univ.prod h.isOpen) (isOpen_Ioi (a := (0 : ℝ)))
    convert this using 1
    ext p; simp [hOdef, sub_pos]
  set FI : ℝ × E n → ℝ := O.indicator fun p => B p.1 p.2 with hFIdef
  have hFIi : Integrable FI ((volume.restrict (Icc s₁ s₂)).prod (volume.restrict L)) := by
    rw [measure_prod_restrict_eq]
    exact (hBc.integrableOn_compact hKc).indicator hO.measurableSet
  have hFI_slice : ∀ s, ∫ x in L, FI (s, x) = I s := by
    intro s
    have : (fun x => FI (s, x)) = (V ∩ φ ⁻¹' Ioi s).indicator (B s) := by
      ext x
      by_cases hx : x ∈ V ∧ s < φ x
      · rw [hFIdef, indicator_of_mem (show (s, x) ∈ O from hx),
          indicator_of_mem (show x ∈ V ∩ φ ⁻¹' Ioi s from hx)]
      · rw [hFIdef, indicator_of_notMem (show (s, x) ∉ O from hx),
          indicator_of_notMem (show x ∉ V ∩ φ ⁻¹' Ioi s from hx)]
    rw [this]
    exact h.setIntegral_indicator_superlevel hφc s (B s)
  have hIi : IntegrableOn I (Icc s₁ s₂) :=
    hFIi.integral_prod_left.congr (Eventually.of_forall fun s => hFI_slice s)
  have hGi : ∀ ε, IntegrableOn (fun s => ∫ x in L, FG ε (s, x)) (Icc s₁ s₂) := fun ε =>
    (hFGi ε).integral_prod_left
  -- (iii) the integrated inequality for small `ε`
  have hint_ineq : ∀ η > 0, ∃ ε₁ > 0, ∀ ε, 0 < ε → ε ≤ ε₁ →
      ∫ x in L, ∫ s in Icc s₁ s₂, FG ε (s, x) ≤ η * (s₂ - s₁) + ∫ s in Icc s₁ s₂, I s := by
    intro η hη
    obtain ⟨ε₁, hε₁, hA⟩ := h.exists_fluxA_small_uniform (σ := σ) hφ.smooth hU hLU hW hlam s₁
      s₂ hvan' hη
    refine ⟨ε₁, hε₁, fun ε hε hεε₁ => ?_⟩
    rw [← integral_integral_swap (f := fun s x => FG ε (s, x)) (hFGi ε)]
    calc ∫ s in Icc s₁ s₂, ∫ x in L, FG ε (s, x)
        ≤ ∫ s in Icc s₁ s₂, (η + I s) := by
          refine setIntegral_mono_on (hGi ε) ((integrableOn_const (by simp)).add hIi)
            measurableSet_Icc fun s hs' => ?_
          have h1 := hcore s ε hε
          have h2 := hA ε hε hεε₁ s hs'
          rw [← hLdef] at h2
          simp only [hFGdef]
          linarith
      _ = η * (s₂ - s₁) + ∫ s in Icc s₁ s₂, I s := by
          rw [integral_add (f := fun _ => η) (g := I) (integrableOn_const (by simp)) hIi,
            setIntegral_const,
            Real.volume_real_Icc_of_le hs, smul_eq_mul, mul_comm]
  -- (iv) the limit `ε → 0`: the mollifier in `s` evaluates at `s = φ(x)`
  set Fw : ℝ × E n → ℝ := fun p => wT g ψ (w p.1) σ lam φ p.2 with hFwdef
  obtain ⟨M, hM0, hM⟩ := exists_abs_le_of_continuousOn hKc hwTc
  have hFwx : ∀ x ∈ L, ContinuousOn (fun s => Fw (s, x)) (Icc s₁ s₂) := fun x hx =>
    hwTc.comp (continuousOn_id.prodMk continuousOn_const) fun s hs' => ⟨hs', hx⟩
  have hrepr : ∀ ε, ∀ x ∈ L, ∫ s in Icc s₁ s₂, FG ε (s, x) =
      cutoff ((τ - ψ x) / ε) * cutoff ((ψ' x - c) / ε) *
        ∫ s in s₁..s₂, moll ε (φ x) s * Fw (s, x) := by
    intro ε x _
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs,
      ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [hFGdef, hFwdef, fluxG_def, moll_def]
    ring
  set lim : E n → ℝ := fun x => if s₁ < φ x ∧ φ x ≤ s₂ then Fw (φ x, x) else 0 with hlimdef
  have hlim : Tendsto (fun k : ℕ => ∫ x in L, ∫ s in Icc s₁ s₂, FG (1 / ((k : ℝ) + 1)) (s, x))
      atTop (𝓝 (∫ x in L, lim x)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => M) (fun k => ?_)
      (integrableOn_const (hLc.measure_lt_top.ne)) (fun k => ?_) ?_
    · exact (hFGi _).integral_prod_right.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem hLm] with x hx
      rw [hrepr _ x hx, Real.norm_eq_abs, abs_mul]
      have h1 : |cutoff ((τ - ψ x) / (1 / ((k : ℝ) + 1))) *
          cutoff ((ψ' x - c) / (1 / ((k : ℝ) + 1)))| ≤ 1 := by
        rw [abs_of_nonneg (mul_nonneg (cutoff_nonneg _) (cutoff_nonneg _))]
        exact (mul_le_of_le_one_left (cutoff_nonneg _) (cutoff_le_one _)).trans (cutoff_le_one _)
      have h2 := integral_moll_mul_le (ε := 1 / ((k : ℝ) + 1)) (by positivity) (φ x) hs
        (hFwx x hx)
        (M := M) fun s hs' => hM (s, x) ⟨hs', hx⟩
      calc _ ≤ 1 * M := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
        _ = M := one_mul M
    · filter_upwards [h.ae_lens_ne, ae_restrict_mem hLm] with x hx hxL
      have hτ : 0 < τ - ψ x := sub_pos.2 (lt_of_le_of_ne (mem_lens.1 hxL).2.1 hx.1)
      have hc : 0 < ψ' x - c := sub_pos.2 (lt_of_le_of_ne (mem_lens.1 hxL).2.2 (Ne.symm hx.2))
      have h1 := tendsto_cutoff_div (τ - ψ x)
      have h2 := tendsto_cutoff_div (ψ' x - c)
      have h3 := tendsto_integral_moll hs (hFwx x hxL) (φ x)
      simp only [hτ, hc, ↓reduceIte] at h1 h2
      have := (h1.mul h2).mul h3
      rw [one_mul, one_mul] at this
      refine this.congr fun k => ?_
      rw [hrepr _ x hxL]
  -- identification of the limit
  have hnull := volume_levelSet_eq_zero h.isOpen hLV (hφ.smooth.of_le (by simp))
    (fun x hx => hφ.ne_zero x hx) s₁
  set S := L ∩ φ ⁻¹' Icc s₁ s₂ with hSdef
  have hSm : MeasurableSet S :=
    ((hφc.mono hLV).preimage_isClosed_of_isClosed hLc.isClosed isClosed_Icc).measurableSet
  have hSeq : L ∩ {x | s₁ ≤ φ x ∧ φ x ≤ s₂} = S := by
    ext x; simp [hSdef]
  have hlim_eq : ∫ x in L, lim x = ∫ x in S, Fw (φ x, x) := by
    have hLS : L ∩ S = S := inter_eq_right.2 inter_subset_left
    conv_rhs => rw [← hLS, ← setIntegral_indicator hSm]
    refine setIntegral_congr_ae hLm ?_
    have : ∀ᵐ x ∂volume, x ∈ L → φ x ≠ s₁ := by
      rw [ae_iff]
      refine measure_mono_null (fun x hx => ?_) hnull
      simp only [mem_ofPred_eq, not_imp, not_not] at hx
      exact ⟨hx.1, hx.2⟩
    filter_upwards [this] with x hx hxL
    by_cases h1 : s₁ < φ x ∧ φ x ≤ s₂
    · rw [hlimdef]
      simp only [h1, and_self, ↓reduceIte]
      rw [indicator_of_mem (show x ∈ S from ⟨hxL, h1.1.le, h1.2⟩)]
    · have h2 : x ∉ S := by
        rintro ⟨-, h3, h4⟩
        exact h1 ⟨lt_of_le_of_ne h3 (Ne.symm (hx hxL)), h4⟩
      rw [hlimdef]
      simp only [h1, ↓reduceIte]
      rw [indicator_of_notMem h2]
  -- (v) the inequality in the limit
  have hmainineq : ∫ x in S, Fw (φ x, x) ≤ ∫ s in Icc s₁ s₂, I s := by
    refine le_of_forall_pos_le_add fun η hη => ?_
    obtain ⟨ε₁, hε₁, hineq⟩ := hint_ineq (η / (s₂ - s₁ + 1)) (by
      have : 0 < s₂ - s₁ + 1 := by linarith
      positivity)
    obtain ⟨N₀, hN₀⟩ := exists_nat_one_div_lt hε₁
    rw [← hlim_eq]
    refine le_of_tendsto hlim (eventually_atTop.2 ⟨N₀, fun k hk => ?_⟩)
    have h1 := hineq _ (by positivity) (hN₀ k hk).le
    have h2 : η / (s₂ - s₁ + 1) * (s₂ - s₁) ≤ η := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  -- (vi) the lower bound for the flux density at `s = φ(x)`
  have hcomp : ContinuousOn (fun x => (φ x, x)) L := (hφc.mono hLV).prodMk continuousOn_id
  have hmap : MapsTo (fun x => (φ x, x)) L (univ ×ˢ (U ∩ V)) :=
    fun x hx => ⟨mem_univ _, hLUV hx⟩
  have hmap' : MapsTo (fun x => (φ x, x)) L (univ ×ˢ U) := fun x hx => ⟨mem_univ _, hLU hx⟩
  have hFwφ : ContinuousOn (fun x => Fw (φ x, x)) L := by
    have := (h.family_continuousOn_wT hU hW σ lam hφ.smooth).comp hcomp hmap
    exact this
  have hcb : Continuous fun q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ × (Fin (n + 1) → ℝ) ×
      (Fin (n + 1) → ℝ) => bil q.1 q.2.1 q.2.2 := by
    simp only [bil, Matrix.toLinearMap₂'_apply, smul_eq_mul]
    fun_prop
  have hdw : ContinuousOn (fun x => d (w (φ x)) x) L :=
    continuousOn_pi.2 fun k => (family_continuousOn_d hU hW k).comp hcomp hmap'
  have hww : ContinuousOn (fun x => w (φ x) x) L := hW.continuousOn.comp hcomp hmap'
  have hbilc : ContinuousOn (fun x => bil (g x)⁻¹ (d φ x) (d (w (φ x)) x)) L := by
    have := hcb.comp_continuousOn ((h.continuousOn_ginv.mono hLV).prodMk
      (((continuousOn_d h.isOpen (hφ.smooth.of_le (by simp))).mono hLV).prodMk
        hdw))
    exact this
  have hZc : ContinuousOn (fun x => Real.exp (2 * σ * ψ x) *
      (bil (g x)⁻¹ (d φ x) (d (w (φ x)) x) ^ 2 + σ ^ 2 * w (φ x) x ^ 2)) L :=
    (hE.mono hLV).mul ((hbilc.pow 2).add (continuousOn_const.mul (hww.pow 2)))
  have hZeq : ∀ x ∈ L, Real.exp (2 * σ * ψ x) *
      (fderiv ℝ (w (φ x)) x (-grad g φ x) ^ 2 + σ ^ 2 * w (φ x) x ^ 2) =
      Real.exp (2 * σ * ψ x) *
        (bil (g x)⁻¹ (d φ x) (d (w (φ x)) x) ^ 2 + σ ^ 2 * w (φ x) x ^ 2) := by
    intro x hx
    rw [sq_fderiv_neg_grad (h.lorentzian x (hLV hx))]
  have hJ : c₃ * ∫ x in S, Real.exp (2 * σ * ψ x) *
      (fderiv ℝ (w (φ x)) x (-grad g φ x) ^ 2 + σ ^ 2 * w (φ x) x ^ 2) ≤
      ∫ x in S, Fw (φ x, x) := by
    rw [setIntegral_congr_fun hSm fun x hx => hZeq x hx.1, ← integral_const_mul]
    refine setIntegral_mono_on (((hZc.integrableOn_compact hLc).mono_set
      inter_subset_left).const_mul _) ((hFwφ.integrableOn_compact hLc).mono_set
        inter_subset_left) hSm fun x hx => hlow σ (w (φ x)) x hx.1
  -- (vii) the right-hand side
  have hIeq : ∫ s in Icc s₁ s₂, I s = b / σ * ∫ s in s₁..s₂, ∫ x in L ∩ {x | s < φ x},
      Real.exp (2 * σ * ψ x) * box g (w s) x ^ 2 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs,
      ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [hIdef, hBdef]
    rw [integral_const_mul]
  rw [hSeq]
  set J := ∫ x in S, Real.exp (2 * σ * ψ x) *
      (fderiv ℝ (w (φ x)) x (-grad g φ x) ^ 2 + σ ^ 2 * w (φ x) x ^ 2)
  set R := ∫ s in s₁..s₂, ∫ x in L ∩ {x | s < φ x}, Real.exp (2 * σ * ψ x) * box g (w s) x ^ 2
  have hfin : c₃ * J ≤ b / σ * R := by linarith
  have e1 : σ * J = σ / c₃ * (c₃ * J) := by field_simp
  have e2 : b / c₃ * R = σ / c₃ * (b / σ * R) := by field_simp
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left hfin (by positivity)

end EnergySetting

end

end LorentzianCalderon
