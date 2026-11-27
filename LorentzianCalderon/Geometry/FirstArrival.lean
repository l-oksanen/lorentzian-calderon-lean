module

public import LorentzianCalderon.Geometry.Conjugate

public section

/-!
# First-arrival geodesics

Blueprint, Lemmas `lem_first_arrival` and `lem_open_directions`.
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Set Filter

variable {n : ℕ} {g : MatrixField n} {Y : E n → E n}

/-- The velocity of `r ↦ exp_{γ t} (r k γ'(t))` at `r = 1`. -/
theorem IsGeodesic.fderiv_expMap_smul_deriv (hg : IsSpacetime g Y) {γ : ℝ → E n} {I : Set ℝ}
    (hγ : IsGeodesic g γ I) {t k : ℝ} (h : Icc 0 1 ⊆ (fun τ => k * τ + t) ⁻¹' I) :
    fderiv ℝ (expMap g (γ t)) (k • deriv γ t) (k • deriv γ t) = k • deriv γ (k + t) := by
  obtain ⟨ε, hε, hεI⟩ := exists_Icc_subset_of_isOpen ((hγ.comp_affine k t).isOpen)
    zero_le_one h
  have hloc : ∀ r ∈ Ioo (0 - ε) (1 + ε), InExpDomain g (γ t) (r • k • deriv γ t) ∧
      expMap g (γ t) (r • k • deriv γ t) = γ (k * r + t) := fun r hr =>
    hγ.expMap_smul_smul_deriv hg fun τ hτ => hεI
      ((uIcc_subset_Icc ⟨by linarith, by linarith⟩ (Ioo_subset_Icc_self hr)) hτ)
  have h1 : (1 : ℝ) ∈ Ioo (0 - ε) (1 + ε) := ⟨by linarith, by linarith⟩
  have hdom : InExpDomain g (γ t) (k • deriv γ t) := by simpa using (hloc 1 h1).1
  have hA := hasDerivAt_expMap_smul_one hg hdom
  have hev : (fun r : ℝ => expMap g (γ t) (r • k • deriv γ t)) =ᶠ[𝓝 1]
      fun r => γ (k * r + t) := eventually_of_mem (isOpen_Ioo.mem_nhds h1) fun r hr =>
    (hloc r hr).2
  have hB := hγ.hasDerivAt_comp_affine (c := k) (d := t) (s := 1)
    (by simpa using h ⟨zero_le_one, le_rfl⟩)
  rw [mul_one] at hB
  exact hA.unique (hB.congr_of_eventuallyEq hev)

/-! ### First arrival -/

/-- Along a future causal geodesic `σ` with `σ 1 ∉ I⁺(σ 0)`, the only future causal vector `w`
at `σ ta`, `0 < ta < 1`, with `exp_{σ ta} w = σ 1` is `(1 - ta) σ'(ta)`. -/
theorem eq_sub_smul_of_expMap_eq (hg : IsSpacetime g Y) {σ : ℝ → E n} {J : Set ℝ}
    (hσ : IsGeodesic g σ J) (hJ : Icc 0 1 ⊆ J) (hfut : IsFutureCausal g Y (σ 0) (deriv σ 0))
    (hnot : ¬ ChronLT g Y (σ 0) (σ 1)) {ta : ℝ} (hta : ta ∈ Ioo 0 1) {w : E n}
    (hwf : IsFutureCausal g Y (σ ta) w) (hwd : InExpDomain g (σ ta) w)
    (hwe : expMap g (σ ta) w = σ 1) : w = (1 - ta) • deriv σ ta := by
  have hfta : IsFutureCausal g Y (σ ta) (deriv σ ta) := hσ.isFutureCausal hg hJ
    ordConnected_Icc (left_mem_Icc.2 zero_le_one) hfut ⟨hta.1.le, hta.2.le⟩
  set y₀ := σ ta
  set v := deriv σ ta
  set p₀ := σ 1
  obtain ⟨ε', hε', hcgeo, -, hc0, hc0'⟩ := hwd.isGeodesic_expMap_smul hg
  obtain ⟨κ, hκ, hjun⟩ := exists_pos_smul_of_not_chronLT hg hσ hcgeo (a₁ := 0) (b₁ := ta)
    (a₂ := 0) (b₂ := 1) hta.1 zero_lt_one ((Icc_subset_Icc le_rfl hta.2.le).trans hJ)
    (fun r hr => ⟨by linarith [hr.1], by linarith [hr.2]⟩) hfut (by rw [hc0, hc0']; exact hwf)
    hc0.symm (by simpa only [one_smul, hwe] using hnot)
  rw [hc0'] at hjun
  have hw' : w = κ⁻¹ • v := by
    have : v = κ • w := hjun
    rw [this, smul_smul, inv_mul_cancel₀ hκ.ne', one_smul]
  obtain ⟨hc₂, hc₂0⟩ := isGeodesic_expMap_smul hg y₀ v
  set D₂ := { r : ℝ | InExpDomain g y₀ (r • v) }
  have hD₁ : ∀ s ∈ Icc 0 κ⁻¹, s ∈ D₂ := fun s hs => by
    have hκi := inv_pos.2 hκ
    have := hwd.smul hg (r := s / κ⁻¹) ⟨div_nonneg hs.1 hκi.le, (div_le_one hκi).2 hs.2⟩
    rwa [hw', smul_smul, div_mul_cancel₀ _ hκi.ne'] at this
  have hD₂ : ∀ s ∈ Icc 0 (1 - ta), s ∈ D₂ ∧ expMap g y₀ (s • v) = σ (s + ta) := fun s hs => by
    have := hσ.expMap_smul_smul_deriv hg (t := ta) (k := 1) (s := s) fun τ hτ => by
      rw [uIcc_of_le hs.1] at hτ
      exact hJ ⟨by linarith [hτ.1, hta.1], by linarith [hτ.2, hs.2]⟩
    simp only [one_smul, one_mul] at this
    exact this
  have hκeq : κ⁻¹ = 1 - ta := by
    by_contra hne
    set a := min κ⁻¹ (1 - ta)
    set b := max κ⁻¹ (1 - ta)
    have hab : a < b := min_lt_max.2 hne
    have hb : Icc 0 b ⊆ D₂ := fun s hs => by
      rcases le_total κ⁻¹ (1 - ta) with h | h
      · exact (hD₂ s ⟨hs.1, by simpa [b, h] using hs.2⟩).1
      · exact hD₁ s ⟨hs.1, by simpa [b, h] using hs.2⟩
    have ha0 : 0 ≤ a := le_min (inv_pos.2 hκ).le (by linarith [hta.2])
    have h0b : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, ha0.trans hab.le⟩
    have hfut₂ : IsFutureCausal g Y (expMap g y₀ ((0 : ℝ) • v))
        (deriv (fun r : ℝ => expMap g y₀ (r • v)) 0) := by
      rw [hc₂0, zero_smul, expMap_zero hg]
      exact hfta
    have hfa := hc₂.isFutureCausal hg hb ordConnected_Icc h0b hfut₂ ⟨ha0, hab.le⟩
    refine hc₂.apply_ne_of_isFutureCausal hg hab ((Icc_subset_Icc ha0 le_rfl).trans hb) hfa ?_
    have e₁ : expMap g y₀ (κ⁻¹ • v) = p₀ := by rw [← hw', hwe]
    have e₂ : expMap g y₀ ((1 - ta) • v) = p₀ := by
      rw [(hD₂ (1 - ta) ⟨by linarith [hta.2], le_rfl⟩).2, sub_add_cancel]
    rcases le_total κ⁻¹ (1 - ta) with h | h
    · simp only [a, b, min_eq_left h, max_eq_right h]
      rw [e₁, e₂]
    · simp only [a, b, min_eq_right h, max_eq_left h]
      rw [e₁, e₂]
  rw [hw', hκeq]

/-- Blueprint, proof of `lem_first_arrival`, Step 2: a null geodesic from `σ 0` to `σ 1` that is
not chronological can be continued beyond `σ 1` without entering the chronological future of a
later initial point `σ t_a`. -/
theorem exists_not_chronLT_extension (hg : IsSpacetime g Y) {σ : ℝ → E n} {J : Set ℝ}
    {ε₀ : ℝ} (hσ : IsGeodesic g σ J) (hε₀ : 0 < ε₀) (hJ : Icc (0 - ε₀) (1 + ε₀) ⊆ J)
    (hnull : form (g (σ 0)) (deriv σ 0) (deriv σ 0) = 0)
    (hfut : IsFutureCausal g Y (σ 0) (deriv σ 0)) (hnot : ¬ ChronLT g Y (σ 0) (σ 1))
    {ta : ℝ} (hta : ta ∈ Ioo 0 1) : ∃ ε ∈ Ioo 0 ε₀, ¬ ChronLT g Y (σ ta) (σ (1 + ε)) := by
  set K := Icc (0 - ε₀) (1 + ε₀)
  have h0K : (0 : ℝ) ∈ K := ⟨by linarith, by linarith⟩
  have hf : ∀ t ∈ K, IsFutureCausal g Y (σ t) (deriv σ t) := fun t ht =>
    hσ.isFutureCausal hg hJ ordConnected_Icc h0K hfut ht
  have hnullt : ∀ t ∈ K, form (g (σ t)) (deriv σ t) (deriv σ t) = 0 := fun t ht =>
    (hσ.form_deriv_eq hg hJ ordConnected_Icc ht h0K).trans hnull
  have htaK : ta ∈ K := ⟨by linarith [hta.1], by linarith [hta.2]⟩
  have hsubK : ∀ a b, 0 - ε₀ ≤ a → b ≤ 1 + ε₀ → Icc a b ⊆ J := fun a b ha hb =>
    (Icc_subset_Icc ha hb).trans hJ
  by_contra hall
  push Not at hall
  set y₀ := σ ta with hy₀
  set v := deriv σ ta with hv
  set p₀ := σ 1 with hp₀
  have h1K : (1 : ℝ) ∈ K := ⟨by linarith, by linarith⟩
  have hne₀ : y₀ ≠ p₀ := hσ.apply_ne_of_isFutureCausal hg hta.2
    (hsubK _ _ (by linarith [hta.1]) (by linarith)) (hf ta htaK)
  have hD₂ : ∀ s ∈ Icc 0 (1 + ε₀ - ta), InExpDomain g y₀ (s • v) ∧
      expMap g y₀ (s • v) = σ (s + ta) := fun s hs => by
    have := hσ.expMap_smul_smul_deriv hg (t := ta) (k := 1) (s := s) fun τ hτ => by
      rw [uIcc_of_le hs.1] at hτ
      exact hsubK ta (1 + ε₀) (by linarith [hta.1]) le_rfl ⟨by linarith [hτ.1],
        by linarith [hτ.2, hs.2]⟩
    simp only [one_smul, one_mul] at this
    exact this
  set w' := (1 - ta) • v with hw'
  have hw'de := hD₂ (1 - ta) ⟨by linarith [hta.2], by linarith⟩
  rw [sub_add_cancel] at hw'de
  have hw'd : InExpDomain g y₀ w' := hw'de.1
  have hw'e : expMap g y₀ w' = p₀ := hw'de.2
  have hw'f : IsFutureCausal g Y y₀ w' := (hf ta htaK).smul (by linarith [hta.2])
  have hy₀p₀ : ¬ ChronLT g Y y₀ p₀ := fun h => hnot ((hσ.causalLE hta.1.le
    (hsubK _ _ (by linarith) (by linarith [hta.2])) fun t ht =>
      hf t ⟨by linarith [ht.1], by linarith [ht.2, hta.2]⟩).trans_chronLT hg h)
  have hconj : IsConjugateAt g y₀ w' := by
    refine isConjugateAt_iff.2 fun hbij => ?_
    have hYc : Continuous Y := hg.globallyHyperbolic.timeOrientation.continuous
    set A := { p : E n × E n | form (g p.1) p.2 (Y p.1) < 0 }
    have hA : IsOpen A := isOpen_lt ((continuous_form hg).comp
      (continuous_fst.prodMk (continuous_snd.prodMk (hYc.comp continuous_fst))))
      continuous_const
    set D := { p : E n × E n | InExpDomain g p.1 p.2 } ∩ A
    have hD : IsOpen D := (isOpen_expDomain hg).inter hA
    have hKD : ({(y₀, w')} : Set (E n × E n)) ⊆ D := by
      rintro _ rfl
      exact ⟨hw'd, hw'f.future⟩
    have hder : ∀ p ∈ ({(y₀, w')} : Set (E n × E n)), ∃ f' : (E n × E n) ≃L[ℝ] (E n × E n),
        HasFDerivAt (expPair g) (f' : _ →L[ℝ] _) p := by
      rintro _ rfl
      exact exists_hasFDerivAt_expPair hg hw'd hbij
    obtain ⟨U₀, hU₀, hKU₀, hU₀D, hinj, himg, -, h, hh, hhf⟩ :=
      exists_injOn_contDiffOn_inverse (K := {(y₀, w')}) hD
        ((contDiffOn_expPair hg).mono inter_subset_left) isCompact_singleton hKD
        (injOn_singleton _ _) hder
    have hw'U₀ : (y₀, w') ∈ U₀ := hKU₀ rfl
    have hev : ∀ᶠ q in 𝓝 (y₀, p₀), CausalLE g Y q.1 q.2 → ¬ ChronLT g Y q.1 q.2 →
        ∃ w, (q.1, w) ∈ U₀ ∧ IsFutureCausal g Y q.1 w ∧ expMap g q.1 w = q.2 := by
      have hne : ∀ᶠ q in 𝓝 (y₀, p₀), q.1 ≠ q.2 :=
        (isClosed_diagonal (X := E n)).isOpen_compl.mem_nhds hne₀
      by_contra hcon
      obtain ⟨q, hq, hbad⟩ :=
        exists_seq_forall_of_frequently ((not_eventually.1 hcon).and_eventually hne)
      push Not at hbad
      obtain ⟨w, Φ, w'', hΦ, hw, hwΦ, hw''f, hw''d, hw''e⟩ := exists_tendsto_of_causalLE hg hne₀
        hq (fun k => (hbad k).1.1) (fun k => (hbad k).1.2.1) (fun k => (hbad k).2)
      have heq : w'' = w' := eq_sub_smul_of_expMap_eq hg hσ (hsubK 0 1 (by linarith)
        (by linarith)) hfut hnot hta hw''f hw''d hw''e
      rw [heq] at hwΦ
      have hyΦ : Tendsto (fun k => (q (Φ k)).1) atTop (𝓝 y₀) :=
        ((continuous_fst.tendsto _).comp hq).comp hΦ.tendsto_atTop
      obtain ⟨k, hk⟩ := ((hyΦ.prodMk_nhds hwΦ).eventually (hU₀.mem_nhds hw'U₀)).exists
      exact (hbad (Φ k)).1.2.2 _ hk (hw _).1 (hw _).2.2
    obtain ⟨V', hV'P, hV'o, hV'mem⟩ := eventually_nhds_iff.1 hev
    set O := expPair g '' U₀ ∩ V'
    have hO : IsOpen O := himg.inter hV'o
    set W : E n × E n → E n := fun q => (h q).2
    have hpre : ∀ q ∈ O, (q.1, W q) ∈ U₀ ∧ expPair g (q.1, W q) = q := by
      rintro q ⟨⟨p, hp, rfl⟩, -⟩
      simp only [W, hhf p hp]
      rw [expPair_fst]
      exact ⟨hp, rfl⟩
    have hdom : ∀ q ∈ O, InExpDomain g q.1 (W q) := fun q hq => (hU₀D (hpre q hq).1).1
    have hexp : ∀ q ∈ O, expMap g q.1 (W q) = q.2 := fun q hq => by
      simpa only [expPair_snd] using congrArg Prod.snd (hpre q hq).2
    have hfutO : ∀ q ∈ O, form (g q.1) (W q) (W q) ≤ 0 → IsFutureCausal g Y q.1 (W q) := by
      intro q hq hQ
      have hA' : form (g q.1) (W q) (Y q.1) < 0 := (hU₀D (hpre q hq).1).2
      refine ⟨fun h0 => ?_, hQ, hA'⟩
      rw [h0, form_zero_left] at hA'
      exact lt_irrefl _ hA'
    have hhor : ∀ q ∈ O, CausalLE g Y q.1 q.2 → ¬ ChronLT g Y q.1 q.2 →
        form (g q.1) (W q) (W q) ≤ 0 := by
      intro q hq hc hnc
      obtain ⟨w, hw, hwf, hwe⟩ := hV'P q hq.2 hc hnc
      have : (q.1, w) = (q.1, W q) :=
        hinj hw (hpre q hq).1 (by rw [(hpre q hq).2]; simp [expPair_def, hwe])
      have hw : w = W q := (Prod.ext_iff.1 this).2
      rw [← hw]
      exact hwf.causal
    have hp₀O : (y₀, p₀) ∈ O := ⟨⟨(y₀, w'), hw'U₀, by simp [expPair_def, hw'e]⟩, hV'mem⟩
    have hWs : DifferentiableOn ℝ W O :=
      (contDiff_snd.comp_contDiffOn (hh.mono inter_subset_left)).differentiableOn (by simp)
    have hneg := eventually_chronLT_imp_form_neg hg hO hWs hdom hexp hfutO hhor hp₀O hy₀p₀
    have hσc : ContinuousAt σ 1 := (hσ.hasDerivAt (hJ h1K)).continuousAt
    have hq : Tendsto (fun ε : ℝ => (y₀, σ (1 + ε))) (𝓝[>] 0) (𝓝 (y₀, p₀)) := by
      refine tendsto_const_nhds.prodMk_nhds (hσc.tendsto.comp ?_)
      have : Continuous fun ε : ℝ => 1 + ε := by fun_prop
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    have hŵ : Tendsto (fun ε : ℝ => (y₀, (1 + ε - ta) • v)) (𝓝[>] 0) (𝓝 (y₀, w')) := by
      refine tendsto_const_nhds.prodMk_nhds ?_
      have : Continuous fun ε : ℝ => (1 + ε - ta) • v := by fun_prop
      simpa [w'] using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    obtain ⟨ε, hε1, hε2, hε3⟩ := ((hq.eventually hneg).and ((hŵ.eventually
      (hU₀.mem_nhds hw'U₀)).and (Ioo_mem_nhdsGT hε₀))).exists
    have he := hD₂ (1 + ε - ta) ⟨by linarith [hta.2, hε3.1], by linarith [hε3.2]⟩
    rw [sub_add_cancel] at he
    have hWε : W (y₀, σ (1 + ε)) = (1 + ε - ta) • v := by
      have := hhf _ hε2
      simp only [expPair_def, he.2] at this
      simp [W, this]
    have := hε1 (hall ε hε3)
    rw [hWε, form_smul_left, form_smul_right, hnullt ta htaK] at this
    simp at this
  have hrev := hconj.reverse hg hw'd
  have hw'p : expMap g y₀ w' = p₀ := hw'e
  have hvel : fderiv ℝ (expMap g y₀) w' w' = (1 - ta) • deriv σ 1 := by
    rw [hw']
    have := hσ.fderiv_expMap_smul_deriv hg (t := ta) (k := 1 - ta) fun τ hτ =>
      hsubK ta 1 (by linarith [hta.1]) (by linarith) ⟨by nlinarith [hτ.1, hta.2],
        by nlinarith [hτ.2, hta.1, hta.2]⟩
    rwa [sub_add_cancel] at this
  rw [hw'p, hvel] at hrev
  have hρ := hσ.comp_affine (-1) 1
  have hρI : Icc 0 1 ⊆ (fun s : ℝ => -1 * s + 1) ⁻¹' J := fun s hs =>
    hsubK 0 1 (by linarith) (by linarith) ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hρ0 : deriv (fun s : ℝ => σ (-1 * s + 1)) 0 = -deriv σ 1 := by
    rw [hσ.deriv_comp_affine (c := -1) (d := 1) (s := 0) (by simpa using hJ h1K)]
    simp
  have hfutρ : IsFutureCausal g (-Y) ((fun s : ℝ => σ (-1 * s + 1)) 0)
      (deriv (fun s : ℝ => σ (-1 * s + 1)) 0) := by
    rw [hρ0, isFutureCausal_neg_iff, neg_neg]
    simpa using hf 1 h1K
  have hnullρ : form (g ((fun s : ℝ => σ (-1 * s + 1)) 0))
      (deriv (fun s : ℝ => σ (-1 * s + 1)) 0) (deriv (fun s : ℝ => σ (-1 * s + 1)) 0) = 0 := by
    rw [hρ0]
    simpa using hnullt 1 h1K
  have hconjρ : IsConjugateAt g ((fun s : ℝ => σ (-1 * s + 1)) 0)
      ((1 - ta) • deriv (fun s : ℝ => σ (-1 * s + 1)) 0) := by
    rw [hρ0, smul_neg]
    simpa using hrev
  have := Facts.chronLT_of_conjugate hg.neg hρ hρI hnullρ hfutρ
    ⟨by linarith [hta.2], by linarith [hta.1]⟩ hconjρ
  rw [chronLT_neg_iff] at this
  exact hnot (by simpa using this)

/-- Blueprint, Lemma `lem_first_arrival`: through every point `p₀ ∉ O` reached from a point
`y ∈ O ∩ E⁻(p₀)` passes a first-arrival null geodesic `σ` on `[0, b]`, `b > 1`, with
`σ 1 = p₀`, `σ(b) ∉ I⁺(σ 0)`, an initial piece in `O`, and `y ≤ σ 0`. -/
theorem exists_firstArrival (hg : IsSpacetime g Y) {O : Set (E n)} (hO : IsOpen O) {p₀ : E n}
    (hp₀ : p₀ ∉ O) {y : E n} (hy : y ∈ O) (hyp : CausalLE g Y y p₀)
    (hnot : ¬ ChronLT g Y y p₀) :
    ∃ (σ : ℝ → E n) (I : Set ℝ) (b t₁ : ℝ), IsGeodesic g σ I ∧ Icc 0 b ⊆ I ∧ 1 < b ∧
      t₁ ∈ Ioo 0 1 ∧ form (g (σ 0)) (deriv σ 0) (deriv σ 0) = 0 ∧
      IsFutureCausal g Y (σ 0) (deriv σ 0) ∧ σ 1 = p₀ ∧ ¬ ChronLT g Y (σ 0) (σ b) ∧
      σ '' Icc 0 t₁ ⊆ O ∧ CausalLE g Y y (σ 0) := by
  have hne : y ≠ p₀ := fun h => hp₀ (h ▸ hy)
  obtain ⟨σ', J, hσ', hJ, h0, h1, hcf, hnullJ⟩ := Facts.exists_causal_geodesic hg hyp hne hnot
  have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hnull : form (g (σ' 0)) (deriv σ' 0) (deriv σ' 0) = 0 := hnullJ 0 (hJ h01)
  obtain ⟨ε₀, hε₀, hε₀J⟩ := exists_Icc_subset_of_isOpen hσ'.isOpen zero_le_one hJ
  have hcont : ContinuousAt σ' 0 := (hσ'.hasDerivAt (hJ h01)).continuousAt
  obtain ⟨δ, hδ, hδO⟩ :=
    Metric.mem_nhds_iff.1 (hcont.preimage_mem_nhds (hO.mem_nhds (h0 ▸ hy)))
  obtain ⟨tb, htb0, htb1, htbδ⟩ : ∃ tb : ℝ, 0 < tb ∧ tb ≤ 1 / 2 ∧ tb < δ :=
    ⟨min (δ / 2) (1 / 2), lt_min (by linarith) (by norm_num), min_le_right _ _,
      (min_le_left _ _).trans_lt (by linarith)⟩
  set ta := tb / 2 with hta_def
  have hta : ta ∈ Ioo 0 1 := ⟨by positivity, by linarith⟩
  have hO' : ∀ t ∈ Icc 0 tb, σ' t ∈ O := fun t ht => hδO (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    constructor <;> linarith [ht.1, ht.2])
  obtain ⟨ε, hε, hεnot⟩ := exists_not_chronLT_extension hg hσ' hε₀ hε₀J hnull (hcf 0 h01)
    (by rwa [h0, h1]) hta
  set k := 1 - ta with hk_def
  have hk : 0 < k := by linarith [hta.2]
  have hK : ∀ t, 0 - ε₀ ≤ t → t ≤ 1 + ε₀ → t ∈ J := fun t h₁ h₂ => hε₀J ⟨h₁, h₂⟩
  have htaJ : k * 0 + ta ∈ J := hK _ (by linarith [hta.1]) (by linarith [hta.2])
  have hfta : IsFutureCausal g Y (σ' ta) (deriv σ' ta) := hσ'.isFutureCausal hg hε₀J
    ordConnected_Icc ⟨by linarith, by linarith⟩ (hcf 0 h01)
    ⟨by linarith [hta.1], by linarith [hta.2]⟩
  have hnta : form (g (σ' ta)) (deriv σ' ta) (deriv σ' ta) = 0 :=
    (hσ'.form_deriv_eq hg hε₀J ordConnected_Icc ⟨by linarith [hta.1], by linarith [hta.2]⟩
      ⟨by linarith, by linarith⟩).trans hnull
  have hd0 : deriv (fun t => σ' (k * t + ta)) 0 = k • deriv σ' ta := by
    rw [hσ'.deriv_comp_affine htaJ]
    simp
  have hkε : k * (1 + ε / k) + ta = 1 + ε := by
    field_simp
    ring
  refine ⟨fun t => σ' (k * t + ta), _, 1 + ε / k, (tb - ta) / k, hσ'.comp_affine k ta,
    fun t ht => ?_, by linarith [div_pos hε.1 hk], ⟨div_pos (by linarith) hk,
      (div_lt_one hk).2 (by linarith)⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1' : k * t ≤ k * (1 + ε / k) := mul_le_mul_of_nonneg_left ht.2 hk.le
    exact hK _ (by nlinarith [ht.1, hta.1]) (by linarith [hε.2])
  · simp only [mul_zero, zero_add]
    rw [hd0, form_smul_left, form_smul_right, hnta, mul_zero, mul_zero]
  · simp only [mul_zero, zero_add]
    rw [hd0]
    exact hfta.smul hk
  · simp only [mul_one, hk_def, sub_add_cancel]
    exact h1
  · simp only [mul_zero, zero_add, hkε]
    exact hεnot
  · rintro _ ⟨t, ht, rfl⟩
    have h1' : k * t ≤ tb - ta := by
      have := mul_le_mul_of_nonneg_left ht.2 hk.le
      rwa [mul_div_cancel₀ _ hk.ne'] at this
    exact hO' _ ⟨by nlinarith [ht.1, hta.1], by linarith⟩
  · simp only [mul_zero, zero_add]
    rw [← h0]
    exact hσ'.causalLE hta.1.le (hJ.trans' (Icc_subset_Icc le_rfl hta.2.le)) fun t ht =>
      hcf t ⟨ht.1, ht.2.trans hta.2.le⟩

/-! ### Admissible directions -/

/-- `ζ` is an admissible direction at `p₀` (the set `𝒱(p₀)` of the blueprint): `ζ` is
future-directed null, and `σ_ζ(t) = exp_{p₀}((t - 1) ζ)` is defined on `[0, b]` for some `b > 1`,
with `σ_ζ(b) ∉ I⁺(σ_ζ(0))` and `σ_ζ([0, t₁]) ⊆ O` for some `t₁ ∈ (0, 1)`. -/
def IsAdmissibleDirection (g : MatrixField n) (Y : E n → E n) (O : Set (E n)) (p₀ ζ : E n) :
    Prop :=
  IsFutureCausal g Y p₀ ζ ∧ form (g p₀) ζ ζ = 0 ∧ ∃ b > (1 : ℝ), ∃ t₁ ∈ Ioo (0 : ℝ) 1,
    (∀ t ∈ Icc 0 b, InExpDomain g p₀ ((t - 1) • ζ)) ∧
    ¬ ChronLT g Y (expMap g p₀ ((0 - 1 : ℝ) • ζ)) (expMap g p₀ ((b - 1) • ζ)) ∧
    ∀ t ∈ Icc 0 t₁, expMap g p₀ ((t - 1) • ζ) ∈ O

theorem isAdmissibleDirection_iff {g : MatrixField n} {Y : E n → E n} {O : Set (E n)} {p₀ ζ : E n} :
    IsAdmissibleDirection g Y O p₀ ζ ↔
      IsFutureCausal g Y p₀ ζ ∧ form (g p₀) ζ ζ = 0 ∧ ∃ b > (1 : ℝ), ∃ t₁ ∈ Ioo (0 : ℝ) 1,
        (∀ t ∈ Icc 0 b, InExpDomain g p₀ ((t - 1) • ζ)) ∧
        ¬ ChronLT g Y (expMap g p₀ ((0 - 1 : ℝ) • ζ)) (expMap g p₀ ((b - 1) • ζ)) ∧
        ∀ t ∈ Icc 0 t₁, expMap g p₀ ((t - 1) • ζ) ∈ O := Iff.rfl

/-- The geodesic `σ_ζ(t) = exp_{p₀}((t - 1) ζ)`, with `σ_ζ(1) = p₀` and `σ_ζ'(1) = ζ`. -/
theorem isGeodesic_expMap_sub_one_smul (hg : IsSpacetime g Y) (p₀ ζ : E n) :
    IsGeodesic g (fun t : ℝ => expMap g p₀ ((t - 1) • ζ))
      { t : ℝ | InExpDomain g p₀ ((t - 1) • ζ) } ∧
      deriv (fun t : ℝ => expMap g p₀ ((t - 1) • ζ)) 1 = ζ := by
  obtain ⟨hc, hc0⟩ := isGeodesic_expMap_smul hg p₀ ζ
  have h := hc.comp_affine 1 (-1)
  have heq : ∀ t : ℝ, 1 * t + -1 = t - 1 := fun t => by ring
  simp only [heq] at h
  refine ⟨h, ?_⟩
  have h0 : (1 : ℝ) * 1 + -1 ∈ { r : ℝ | InExpDomain g p₀ (r • ζ) } := by
    simpa using inExpDomain_zero (g := g) p₀
  have := hc.deriv_comp_affine h0
  simp only [heq, sub_self, one_smul] at this
  rwa [hc0] at this

theorem deriv_expMap_sub_one_smul_zero (hg : IsSpacetime g Y) {p₀ ζ : E n}
    (h : InExpDomain g p₀ ((0 - 1 : ℝ) • ζ)) :
    deriv (fun t : ℝ => expMap g p₀ ((t - 1) • ζ)) 0 =
      fderiv ℝ (fun z : E n × E n => expMap g z.1 z.2) (p₀, (0 - 1 : ℝ) • ζ) (0, ζ) := by
  have hL := hasFDerivAt_expMap_prod hg (p := (p₀, (0 - 1 : ℝ) • ζ)) h
  have hin : HasDerivAt (fun t : ℝ => (p₀, (t - 1) • ζ)) ((0 : E n), (1 : ℝ) • ζ) 0 :=
    (hasDerivAt_const 0 p₀).prodMk (((hasDerivAt_id 0).sub_const 1).smul_const ζ)
  have := hL.comp_hasDerivAt (0 : ℝ) hin
  rw [one_smul] at this
  exact this.deriv

/-- Blueprint, Lemma `lem_open_directions`: the admissible directions form an open subset of the
future null cone at `p₀`. -/
theorem IsAdmissibleDirection.eventually (hg : IsSpacetime g Y) {O : Set (E n)}
    (hO : IsOpen O) {p₀ ζ₀ : E n} (h : IsAdmissibleDirection g Y O p₀ ζ₀) :
    ∀ᶠ ζ in 𝓝 ζ₀, IsFutureCausal g Y p₀ ζ → form (g p₀) ζ ζ = 0 →
      IsAdmissibleDirection g Y O p₀ ζ := by
  obtain ⟨hf₀, hn₀, b, hb, t₁, ht₁, hdom, hnot, hO₀⟩ := h
  obtain ⟨hσ, hσ1⟩ := isGeodesic_expMap_sub_one_smul hg p₀ ζ₀
  set σ := fun t : ℝ => expMap g p₀ ((t - 1) • ζ₀) with hσ_def
  set I := { t : ℝ | InExpDomain g p₀ ((t - 1) • ζ₀) }
  have hI : Icc 0 b ⊆ I := fun t ht => hdom t ht
  have h1 : (1 : ℝ) ∈ Icc 0 b := ⟨zero_le_one, hb.le⟩
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, by linarith⟩
  have hσp : σ 1 = p₀ := by simp [σ, expMap_zero hg]
  have hfut1 : IsFutureCausal g Y (σ 1) (deriv σ 1) := by rw [hσp, hσ1]; exact hf₀
  have hfut : IsFutureCausal g Y (σ 0) (deriv σ 0) :=
    hσ.isFutureCausal hg hI ordConnected_Icc h1 hfut1 h0
  have hnull : form (g (σ 0)) (deriv σ 0) (deriv σ 0) = 0 := by
    rw [hσ.form_deriv_eq hg hI ordConnected_Icc h0 h1, hσp, hσ1, hn₀]
  obtain ⟨t₂, ht₂⟩ : ∃ t₂ : ℝ, 1 < t₂ ∧ t₂ < b := ⟨(1 + b) / 2, by linarith, by linarith⟩
  obtain ⟨U, U', W, hc, hKU, -, hfutU, hiff⟩ := exists_worldFunction hg hσ hI hnull hfut hnot
    ht₁.1 ht₂.2
  have hD : IsOpen { z : E n × ℝ | InExpDomain g p₀ ((z.2 - 1) • z.1) } :=
    (isOpen_expDomain hg).preimage (f := fun z : E n × ℝ => (p₀, (z.2 - 1) • z.1))
      (by fun_prop)
  have hE1 : ∀ᶠ ζ in 𝓝 ζ₀, ∀ t ∈ Icc 0 t₂, InExpDomain g p₀ ((t - 1) • ζ) :=
    isCompact_Icc.eventually_forall_of_forall_eventually fun t ht =>
      hD.mem_nhds (show (ζ₀, t) ∈ _ from hdom t ⟨ht.1, ht.2.trans ht₂.2.le⟩)
  have hDO : IsOpen { z : E n × ℝ | InExpDomain g p₀ ((z.2 - 1) • z.1) ∧
      expMap g p₀ ((z.2 - 1) • z.1) ∈ O } := by
    have hcont : ContinuousOn (fun z : E n × ℝ => expMap g p₀ ((z.2 - 1) • z.1))
        { z : E n × ℝ | InExpDomain g p₀ ((z.2 - 1) • z.1) } :=
      (continuousOn_expMap hg).comp (f := fun z : E n × ℝ => (p₀, (z.2 - 1) • z.1))
        (by fun_prop) fun z hz => hz
    exact hcont.isOpen_inter_preimage hD hO
  have hE2 : ∀ᶠ ζ in 𝓝 ζ₀, ∀ t ∈ Icc 0 t₁, InExpDomain g p₀ ((t - 1) • ζ) ∧
      expMap g p₀ ((t - 1) • ζ) ∈ O :=
    isCompact_Icc.eventually_forall_of_forall_eventually fun t ht =>
      hDO.mem_nhds (show (ζ₀, t) ∈ _ from
        ⟨hdom t ⟨ht.1, ht.2.trans (ht₁.2.trans hb).le⟩, hO₀ t ht⟩)
  set L := fderiv ℝ (fun z : E n × E n => expMap g z.1 z.2)
  set F : E n → E n × E n := fun ζ =>
    (expMap g p₀ ((0 - 1 : ℝ) • ζ), t₂ • L (p₀, (0 - 1 : ℝ) • ζ) (0, ζ))
  have hdom0 : InExpDomain g p₀ ((0 - 1 : ℝ) • ζ₀) := hdom 0 h0
  have hF : ContinuousAt F ζ₀ := by
    have hpt : ContinuousAt (fun ζ : E n => (p₀, (0 - 1 : ℝ) • ζ)) ζ₀ := by fun_prop
    have hmem : (p₀, (0 - 1 : ℝ) • ζ₀) ∈ { p : E n × E n | InExpDomain g p.1 p.2 } := hdom0
    have hexp : ContinuousAt (fun ζ : E n => expMap g p₀ ((0 - 1 : ℝ) • ζ)) ζ₀ :=
      ContinuousAt.comp (g := fun p : E n × E n => expMap g p.1 p.2)
        (f := fun ζ : E n => (p₀, (0 - 1 : ℝ) • ζ))
        ((continuousOn_expMap hg).continuousAt ((isOpen_expDomain hg).mem_nhds hmem)) hpt
    have hLc : ContinuousAt L (p₀, (0 - 1 : ℝ) • ζ₀) :=
      ((contDiffOn_expMap hg).continuousOn_fderiv_of_isOpen (isOpen_expDomain hg)
        (by simp)).continuousAt ((isOpen_expDomain hg).mem_nhds hmem)
    have happ : ContinuousAt (fun ζ : E n => L (p₀, (0 - 1 : ℝ) • ζ) (0, ζ)) ζ₀ :=
      (ContinuousAt.comp (g := L) (f := fun ζ : E n => (p₀, (0 - 1 : ℝ) • ζ)) hLc hpt).clm_apply
        (f := fun ζ : E n => L (p₀, (0 - 1 : ℝ) • ζ)) (g := fun ζ : E n => ((0 : E n), ζ))
        (by fun_prop)
    exact hexp.prodMk (happ.const_smul t₂)
  have hF₀ : F ζ₀ = (σ 0, t₂ • deriv σ 0) := by
    simp only [F, σ]
    rw [deriv_expMap_sub_one_smul_zero hg hdom0]
  have hE3 : ∀ᶠ ζ in 𝓝 ζ₀, F ζ ∈ U :=
    hF.eventually (hc.isOpen.mem_nhds (hF₀ ▸ hKU t₂ ⟨by linarith [ht₁.2], le_rfl⟩))
  filter_upwards [hE1, hE2, hE3] with ζ hζ1 hζ2 hζ3 hfζ hnζ
  refine ⟨hfζ, hnζ, t₂, ht₂.1, t₁, ht₁, hζ1, ?_, fun t ht => (hζ2 t ht).2⟩
  obtain ⟨hσζ, hσζ1⟩ := isGeodesic_expMap_sub_one_smul hg p₀ ζ
  set σζ := fun t : ℝ => expMap g p₀ ((t - 1) • ζ)
  have hIζ : Icc 0 t₂ ⊆ { t : ℝ | InExpDomain g p₀ ((t - 1) • ζ) } := fun t ht => hζ1 t ht
  have h1' : (1 : ℝ) ∈ Icc 0 t₂ := ⟨zero_le_one, ht₂.1.le⟩
  have h0' : (0 : ℝ) ∈ Icc 0 t₂ := ⟨le_rfl, by linarith⟩
  have hσζp : σζ 1 = p₀ := by simp [σζ, expMap_zero hg]
  have hnullζ : form (g (σζ 0)) (deriv σζ 0) (deriv σζ 0) = 0 := by
    rw [hσζ.form_deriv_eq hg hIζ ordConnected_Icc h0' h1', hσζp, hσζ1, hnζ]
  have hd0 : deriv σζ 0 = L (p₀, (0 - 1 : ℝ) • ζ) (0, ζ) :=
    deriv_expMap_sub_one_smul_zero hg (hζ1 0 h0')
  have hpU : (σζ 0, t₂ • deriv σζ 0) ∈ U := by
    rw [hd0]
    exact hζ3
  have hq := (hiff _ (hc.mapsTo _ hpU)).2
  rw [hc.inv_expPair _ hpU] at hq
  simp only [expPair_def, form_smul_left, form_smul_right, hnullζ, mul_zero, lt_irrefl,
    iff_false] at hq
  have he := (hσζ.expMap_smul_eq hg
    ((uIcc_of_le (show (0 : ℝ) ≤ t₂ by linarith [ht₂.1])).symm ▸ hIζ)).2
  rw [he] at hq
  exact hq

/-- Blueprint, Lemma `lem_open_directions`, nonemptiness. -/
theorem exists_isAdmissibleDirection (hg : IsSpacetime g Y) {O : Set (E n)} (hO : IsOpen O)
    {p₀ : E n} (hp₀ : p₀ ∉ O) {y : E n} (hy : y ∈ O) (hyp : CausalLE g Y y p₀)
    (hnot : ¬ ChronLT g Y y p₀) : ∃ ζ, IsAdmissibleDirection g Y O p₀ ζ := by
  obtain ⟨σ, I, b, t₁, hσ, hI, hb, ht₁, hnull, hfut, hσ1, hfirst, hO', -⟩ :=
    exists_firstArrival hg hO hp₀ hy hyp hnot
  have h1 : (1 : ℝ) ∈ Icc 0 b := ⟨zero_le_one, hb.le⟩
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, by linarith⟩
  have hexp : ∀ t ∈ Icc 0 b, InExpDomain g p₀ ((t - 1) • deriv σ 1) ∧
      expMap g p₀ ((t - 1) • deriv σ 1) = σ t := fun t ht => by
    have := hσ.expMap_smul_smul_deriv hg (t := 1) (k := 1) (s := t - 1) fun τ hτ => by
      refine hI ⟨?_, ?_⟩
      · rcases le_total 0 (t - 1) with h | h
        · rw [uIcc_of_le h] at hτ; linarith [hτ.1]
        · rw [uIcc_of_ge h] at hτ; linarith [hτ.1, ht.1]
      · rcases le_total 0 (t - 1) with h | h
        · rw [uIcc_of_le h] at hτ; linarith [hτ.2, ht.2]
        · rw [uIcc_of_ge h] at hτ; linarith [hτ.2]
    simp only [one_smul, one_mul, sub_add_cancel, hσ1] at this
    exact this
  refine ⟨deriv σ 1, ?_, ?_, b, hb, t₁, ht₁, fun t ht => (hexp t ht).1, ?_, fun t ht => ?_⟩
  · rw [← hσ1]
    exact hσ.isFutureCausal hg hI ordConnected_Icc h0 hfut h1
  · rw [← hσ1, hσ.form_deriv_eq hg hI ordConnected_Icc h1 h0, hnull]
  · rw [(hexp 0 h0).2, (hexp b ⟨by linarith, le_rfl⟩).2]
    exact hfirst
  · rw [(hexp t ⟨ht.1, ht.2.trans ht₁.2.le |>.trans hb.le⟩).2]
    exact hO' ⟨t, ht, rfl⟩

end

end LorentzianCalderon
