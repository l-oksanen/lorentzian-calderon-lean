module

public import LorentzianCalderon.Geometry.Imprison
public import LorentzianCalderon.Geometry.Junction
public import LorentzianCalderon.Geometry.InverseFunction
public import LorentzianCalderon.Geometry.ConjugateChron
public import LorentzianCalderon.Geometry.Crossing

public section

/-!
# The local world function along a first-arrival geodesic

Blueprint, Lemma `lem_world_function`.
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Set Filter

variable {n : ℕ} {g : MatrixField n} {Y : E n → E n}

theorem continuousOn_expMap (hg : IsSpacetime g Y) :
    ContinuousOn (fun p : E n × E n => expMap g p.1 p.2) { p | InExpDomain g p.1 p.2 } :=
  (contDiffOn_expMap hg).continuousOn

theorem tendsto_expMap (hg : IsSpacetime g Y) {y w : E n} (h : InExpDomain g y w) :
    Tendsto (fun p : E n × E n => expMap g p.1 p.2) (𝓝 (y, w)) (𝓝 (expMap g y w)) :=
  (continuousOn_expMap hg).continuousAt ((isOpen_expDomain hg).mem_nhds h)

/-- Limits of exponentials along converging rays stay in a closed set. -/
theorem expMap_smul_mem_of_tendsto (hg : IsSpacetime g Y) {y : ℕ → E n} {u : ℕ → E n}
    {y₀ u₀ : E n} (hy : Tendsto y atTop (𝓝 y₀)) (hu : Tendsto u atTop (𝓝 u₀)) {len : ℕ → ℝ}
    {K : Set (E n)} (hK : IsClosed K)
    (hmem : ∀ᶠ k in atTop, ∀ r ∈ Icc 0 (len k), expMap g (y k) (r • u k) ∈ K) {r : ℝ}
    (hr : 0 ≤ r) (hdom : InExpDomain g y₀ (r • u₀)) (hfreq : ∃ᶠ k in atTop, r ≤ len k) :
    expMap g y₀ (r • u₀) ∈ K := by
  have ht : Tendsto (fun k => (y k, r • u k)) atTop (𝓝 (y₀, r • u₀)) :=
    hy.prodMk_nhds (hu.const_smul r)
  refine hK.mem_of_frequently_of_tendsto ?_ ((tendsto_expMap hg hdom).comp ht)
  exact (hfreq.and_eventually hmem).mono fun k hk => hk.2 r ⟨hr, hk.1⟩

/-- Compactness of null geodesics: for causally but not chronologically related pairs `q k`
converging to `(y₀, x₀)`, `y₀ ≠ x₀`, the initial vectors of joining null geodesics have a
subsequence converging to a future-directed causal vector `w∞` in the domain of `exp_{y₀}` with
`exp_{y₀} w∞ = x₀`. -/
theorem exists_tendsto_of_causalLE (hg : IsSpacetime g Y) {y₀ x₀ : E n} (hne₀ : y₀ ≠ x₀)
    {q : ℕ → E n × E n} (hq : Tendsto q atTop (𝓝 (y₀, x₀)))
    (hc : ∀ k, CausalLE g Y (q k).1 (q k).2) (hnc : ∀ k, ¬ ChronLT g Y (q k).1 (q k).2)
    (hne : ∀ k, (q k).1 ≠ (q k).2) :
    ∃ (w : ℕ → E n) (Φ : ℕ → ℕ) (w' : E n), StrictMono Φ ∧
      (∀ k, IsFutureCausal g Y (q k).1 (w k) ∧ InExpDomain g (q k).1 (w k) ∧
        expMap g (q k).1 (w k) = (q k).2) ∧
      Tendsto (w ∘ Φ) atTop (𝓝 w') ∧ IsFutureCausal g Y y₀ w' ∧ InExpDomain g y₀ w' ∧
      expMap g y₀ w' = x₀ := by
  have hy : Tendsto (fun k => (q k).1) atTop (𝓝 y₀) := (continuous_fst.tendsto _).comp hq
  have hp : Tendsto (fun k => (q k).2) atTop (𝓝 x₀) := (continuous_snd.tendsto _).comp hq
  have hgeo : ∀ k, ∃ w, IsFutureCausal g Y (q k).1 w ∧ InExpDomain g (q k).1 w ∧
      expMap g (q k).1 w = (q k).2 ∧ ∀ s ∈ Icc (0 : ℝ) 1,
        CausalLE g Y (q k).1 (expMap g (q k).1 (s • w)) ∧
        CausalLE g Y (expMap g (q k).1 (s • w)) (q k).2 := by
    intro k
    obtain ⟨c, J, hcJ, hJ, hc0, hc1, hcf, -⟩ :=
      Facts.exists_causal_geodesic hg (hc k) (hne k) (hnc k)
    refine ⟨deriv c 0, hc0 ▸ hcf 0 ⟨le_rfl, zero_le_one⟩, hc0 ▸ hcJ.inExpDomain hJ,
      by rw [← hc0, hcJ.expMap_eq hg hJ, hc1], fun s hs => ?_⟩
    have hsub : uIcc 0 s ⊆ J := (uIcc_subset_Icc ⟨le_rfl, zero_le_one⟩ hs).trans hJ
    have he := (hcJ.expMap_smul_eq hg hsub).2
    rw [hc0] at he
    rw [he]
    constructor
    · rw [← hc0]
      exact hcJ.causalLE hs.1 ((Icc_subset_Icc le_rfl hs.2).trans hJ) fun r hr =>
        hcf r ⟨hr.1, hr.2.trans hs.2⟩
    · rw [← hc1]
      exact hcJ.causalLE hs.2 ((Icc_subset_Icc hs.1 le_rfl).trans hJ) fun r hr =>
        hcf r ⟨hs.1.trans hr.1, hr.2⟩
  choose w hwf hwd hwe hws using hgeo
  set len : ℕ → ℝ := fun k => ‖w k‖ with hlen_def
  set u : ℕ → E n := fun k => (len k)⁻¹ • w k with hu_def
  have hlen : ∀ k, 0 < len k := fun k => norm_pos_iff.2 (hwf k).ne_zero
  have hwu : ∀ k, w k = len k • u k := fun k => by simp [u, smul_smul, (hlen k).ne']
  have hu1 : ∀ k, u k ∈ Metric.sphere (0 : E n) 1 := fun k => by
    simp [u, norm_smul, (hlen k).ne', len]
  have hu : ∀ k, u k = (len k)⁻¹ • w k := fun k => rfl
  clear_value u len
  obtain ⟨û, hû, φ, hφ, huφ⟩ := (isCompact_sphere (0 : E n) 1).tendsto_subseq hu1
  have hû0 : û ≠ 0 := by
    rintro rfl
    simp at hû
  have hyφ : Tendsto (fun k => (q (φ k)).1) atTop (𝓝 y₀) := hy.comp hφ.tendsto_atTop
  have hpφ : Tendsto (fun k => (q (φ k)).2) atTop (𝓝 x₀) := hp.comp hφ.tendsto_atTop
  obtain ⟨K, hK, hKsub⟩ := exists_isCompact_superset_causalFutureSet_inter_causalPastSet hg
    (isCompact_closedBall y₀ 1) (isCompact_closedBall x₀ 1)
  have hmem : ∀ᶠ k in atTop, ∀ r ∈ Icc 0 (len (φ k)),
      expMap g (q (φ k)).1 (r • u (φ k)) ∈ K := by
    filter_upwards [hyφ.eventually (Metric.closedBall_mem_nhds y₀ one_pos),
      hpφ.eventually (Metric.closedBall_mem_nhds x₀ one_pos)] with k hk1 hk2 r hr
    have hl := hlen (φ k)
    have hs : r / len (φ k) ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hr.1 hl.le, (div_le_one hl).2 hr.2⟩
    have hru : r • u (φ k) = (r / len (φ k)) • w (φ k) := by
      rw [hu, smul_smul]
      congr 1
    obtain ⟨h1, h2⟩ := hws (φ k) _ hs
    rw [hru]
    exact hKsub ⟨mem_causalFutureSet.2 ⟨_, hk1, mem_causalFuture.2 h1⟩,
      mem_causalPastSet.2 ⟨_, hk2, mem_causalPast.2 h2⟩⟩
  have hform : Tendsto (fun k => form (g (q (φ k)).1) (u (φ k)) (u (φ k))) atTop
      (𝓝 (form (g y₀) û û)) := by
    have h3 : Tendsto (fun k => ((q (φ k)).1, u (φ k), u (φ k))) atTop (𝓝 (y₀, û, û)) :=
      hyφ.prodMk_nhds (huφ.prodMk_nhds huφ)
    have h4 := ((continuous_form hg).tendsto (y₀, û, û)).comp h3
    simp only [Function.comp_def] at h4
    exact h4
  have hcaus : form (g y₀) û û ≤ 0 := by
    refine le_of_tendsto' hform fun k => ?_
    have hl := (inv_pos.2 (hlen (φ k))).le
    rw [hu, form_smul_left, form_smul_right]
    exact mul_nonpos_of_nonneg_of_nonpos hl (mul_nonpos_of_nonneg_of_nonpos hl (hwf _).causal)
  have hYc : Continuous Y := hg.globallyHyperbolic.timeOrientation.continuous
  have hformY : Tendsto (fun k => form (g (q (φ k)).1) (u (φ k)) (Y (q (φ k)).1)) atTop
      (𝓝 (form (g y₀) û (Y y₀))) := by
    have h3 : Tendsto (fun k => ((q (φ k)).1, u (φ k), Y (q (φ k)).1)) atTop
        (𝓝 (y₀, û, Y y₀)) :=
      hyφ.prodMk_nhds (huφ.prodMk_nhds ((hYc.tendsto _).comp hyφ))
    have h4 := ((continuous_form hg).tendsto (y₀, û, Y y₀)).comp h3
    simp only [Function.comp_def] at h4
    exact h4
  have hfutle : form (g y₀) û (Y y₀) ≤ 0 := by
    refine le_of_tendsto' hformY fun k => ?_
    rw [hu, form_smul_left]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_pos.2 (hlen (φ k))).le (hwf (φ k)).future.le
  have hûf : IsFutureCausal g Y y₀ û := ⟨hû0, hcaus, lt_of_le_of_ne hfutle fun h =>
    (hg.lorentzian y₀).form_ne_zero hcaus hû0
      (hg.globallyHyperbolic.timeOrientation.timelike y₀) h⟩
  obtain ⟨r, hr0, hrdom, hrK⟩ : ∃ r : ℝ, 0 ≤ r ∧ InExpDomain g y₀ (r • û) ∧
      expMap g y₀ (r • û) ∉ K := by
    by_contra! h
    exact not_forall_expMap_smul_mem hg hûf hK h
  have hbdd : ∀ᶠ k in atTop, len (φ k) < r := by
    by_contra h
    rw [not_eventually] at h
    exact hrK (expMap_smul_mem_of_tendsto hg hyφ huφ hK.isClosed hmem hr0 hrdom
      (h.mono fun k hk => not_lt.1 hk))
  obtain ⟨l, hl, ψ, hψ, hlψ⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := r)).tendsto_subseq'
    (hbdd.mono fun k hk => ⟨(hlen (φ k)).le, hk.le⟩).frequently
  have hΦ : StrictMono (φ ∘ ψ) := hφ.comp hψ
  have hyΦ : Tendsto (fun k => (q ((φ ∘ ψ) k)).1) atTop (𝓝 y₀) := hy.comp hΦ.tendsto_atTop
  have hwΦ : Tendsto (fun k => w ((φ ∘ ψ) k)) atTop (𝓝 (l • û)) := by
    have := hlψ.smul (huφ.comp hψ.tendsto_atTop)
    refine this.congr fun k => ?_
    simp only [Function.comp_apply]
    exact (hwu _).symm
  have hrpos : 0 < r := by
    obtain ⟨k, hk⟩ := hbdd.exists
    exact (hlen (φ k)).trans hk
  have hdom : InExpDomain g y₀ (l • û) := by
    have := hrdom.smul hg (r := l / r) ⟨div_nonneg hl.1 hrpos.le, (div_le_one hrpos).2 hl.2⟩
    rwa [smul_smul, div_mul_cancel₀ _ hrpos.ne'] at this
  have hexp : expMap g y₀ (l • û) = x₀ := by
    have h1 := (tendsto_expMap hg hdom).comp (hyΦ.prodMk_nhds hwΦ)
    have h2 : Tendsto (fun k => (q ((φ ∘ ψ) k)).2) atTop (𝓝 x₀) := hp.comp hΦ.tendsto_atTop
    refine tendsto_nhds_unique h1 (h2.congr fun k => ?_)
    simp only [Function.comp_apply]
    exact (hwe _).symm
  have hlpos : 0 < l := by
    rcases hl.1.lt_or_eq with h | h
    · exact h
    · rw [← h, zero_smul, expMap_zero hg] at hexp
      exact absurd hexp hne₀
  exact ⟨w, φ ∘ ψ, l • û, hΦ, fun k => ⟨hwf k, hwd k, hwe k⟩, hwΦ, hûf.smul hlpos,
    hdom, hexp⟩

/-- Sequences of causally but not chronologically related pairs converging to `(σ 0, σ t)`,
along a first-arrival geodesic `σ`, are eventually joined by causal geodesics with initial
vectors near `t σ'(0)`. -/
theorem exists_mem_of_tendsto (hg : IsSpacetime g Y) {σ : ℝ → E n} {I : Set ℝ} {b : ℝ}
    (hσ : IsGeodesic g σ I) (hI : Icc 0 b ⊆ I) (hfut : IsFutureCausal g Y (σ 0) (deriv σ 0))
    (hfirst : ¬ ChronLT g Y (σ 0) (σ b)) {t : ℝ} (ht : t ∈ Ioo 0 b) {N : Set (E n × E n)}
    (hN : IsOpen N) (htN : (σ 0, t • deriv σ 0) ∈ N) {q : ℕ → E n × E n}
    (hq : Tendsto q atTop (𝓝 (σ 0, σ t))) (hc : ∀ k, CausalLE g Y (q k).1 (q k).2)
    (hnc : ∀ k, ¬ ChronLT g Y (q k).1 (q k).2) (hne : ∀ k, (q k).1 ≠ (q k).2) :
    ∃ k w, ((q k).1, w) ∈ N ∧ IsFutureCausal g Y (q k).1 w ∧ InExpDomain g (q k).1 w ∧
      expMap g (q k).1 w = (q k).2 := by
  have hne₀ : σ 0 ≠ σ t := hσ.apply_ne_of_isFutureCausal hg ht.1
    ((Icc_subset_Icc le_rfl ht.2.le).trans hI) hfut
  obtain ⟨w, Φ, w', hΦ, hw, hwΦ, hw'f, hw'd, hw'e⟩ :=
    exists_tendsto_of_causalLE hg hne₀ hq hc hnc hne
  have heq := eq_smul_of_expMap_eq hg hσ hI hfut hfirst ht hw'f hw'd hw'e
  rw [heq] at hwΦ
  have hyΦ : Tendsto (fun k => (q (Φ k)).1) atTop (𝓝 (σ 0)) :=
    ((continuous_fst.tendsto _).comp hq).comp hΦ.tendsto_atTop
  obtain ⟨k, hk⟩ := ((hyΦ.prodMk_nhds hwΦ).eventually (hN.mem_nhds htN)).exists
  exact ⟨_, _, hk, (hw _).1, (hw _).2.1, (hw _).2.2⟩

/-- The eventual form of `exists_mem_of_tendsto`. -/
theorem eventually_exists_mem (hg : IsSpacetime g Y) {σ : ℝ → E n} {I : Set ℝ} {b : ℝ}
    (hσ : IsGeodesic g σ I) (hI : Icc 0 b ⊆ I) (hfut : IsFutureCausal g Y (σ 0) (deriv σ 0))
    (hfirst : ¬ ChronLT g Y (σ 0) (σ b)) {t : ℝ} (ht : t ∈ Ioo 0 b) {N : Set (E n × E n)}
    (hN : IsOpen N) (htN : (σ 0, t • deriv σ 0) ∈ N) :
    ∀ᶠ q in 𝓝 (σ 0, σ t), CausalLE g Y q.1 q.2 → ¬ ChronLT g Y q.1 q.2 → ∃ w, (q.1, w) ∈ N ∧
      IsFutureCausal g Y q.1 w ∧ InExpDomain g q.1 w ∧ expMap g q.1 w = q.2 := by
  have hne₀ : σ 0 ≠ σ t := hσ.apply_ne_of_isFutureCausal hg ht.1
    ((Icc_subset_Icc le_rfl ht.2.le).trans hI) hfut
  have hne : ∀ᶠ q in 𝓝 (σ 0, σ t), q.1 ≠ q.2 :=
    (isClosed_diagonal (X := E n)).isOpen_compl.mem_nhds hne₀
  by_contra h
  obtain ⟨q, hq, hbad⟩ := exists_seq_forall_of_frequently ((not_eventually.1 h).and_eventually hne)
  push Not at hbad
  obtain ⟨k, w, hw⟩ := exists_mem_of_tendsto hg hσ hI hfut hfirst ht hN htN hq
    (fun k => (hbad k).1.1) (fun k => (hbad k).1.2.1) (fun k => (hbad k).2)
  exact (hbad k).1.2.2 w hw.1 hw.2.1 hw.2.2.1 hw.2.2.2

/-- Blueprint, Lemma `lem_world_function` (a): along a first-arrival null geodesic `σ` on
`[0, b]`, `exp_{σ 0}` is nonsingular at `t σ'(0)` for `0 < t < b`, and `t σ'(0)` is the only
future-directed causal vector `w` with `exp_{σ 0} w = σ t`. -/
theorem not_isConjugateAt_and_eq_smul (hg : IsSpacetime g Y) {σ : ℝ → E n} {I : Set ℝ} {b : ℝ}
    (hσ : IsGeodesic g σ I) (hI : Icc 0 b ⊆ I)
    (hnull : form (g (σ 0)) (deriv σ 0) (deriv σ 0) = 0)
    (hfut : IsFutureCausal g Y (σ 0) (deriv σ 0)) (hfirst : ¬ ChronLT g Y (σ 0) (σ b))
    {t : ℝ} (ht : t ∈ Ioo 0 b) :
    ¬ IsConjugateAt g (σ 0) (t • deriv σ 0) ∧
      ∀ w, IsFutureCausal g Y (σ 0) w → InExpDomain g (σ 0) w → expMap g (σ 0) w = σ t →
        w = t • deriv σ 0 :=
  ⟨fun hc => hfirst (Facts.chronLT_of_conjugate hg hσ hI hnull hfut ht hc),
    fun _ hw hdom hexp => eq_smul_of_expMap_eq hg hσ hI hfut hfirst ht hw hdom hexp⟩

/-! ### The world function -/

/-- `𝐞 : U → U'` is a diffeomorphism with inverse `(y, p) ↦ (y, W (y, p))`, and `exp_y` is
nonsingular on `U`. -/
structure IsExpChart (g : MatrixField n) (U U' : Set (E n × E n)) (W : E n × E n → E n) :
    Prop where
  isOpen : IsOpen U
  isOpen' : IsOpen U'
  inExpDomain : ∀ p ∈ U, InExpDomain g p.1 p.2
  mapsTo : ∀ p ∈ U, expPair g p ∈ U'
  inv_mem : ∀ q ∈ U', (q.1, W q) ∈ U
  inv_expPair : ∀ p ∈ U, W (expPair g p) = p.2
  expMap_inv : ∀ q ∈ U', expMap g q.1 (W q) = q.2
  smooth : ContDiffOn ℝ ∞ W U'
  bijective : ∀ p ∈ U, Function.Bijective (fderiv ℝ (expMap g p.1) p.2)

lemma IsExpChart.inv_apply {U U' : Set (E n × E n)} {W : E n × E n → E n}
    (h : IsExpChart g U U' W) {q : E n × E n} (hq : q ∈ U') : expPair g (q.1, W q) = q := by
  simp [expPair_def, h.expMap_inv q hq]

theorem IsExpChart.restrict (hg : IsSpacetime g Y) {U U' V' : Set (E n × E n)}
    {W : E n × E n → E n} (h : IsExpChart g U U' W) (hV' : IsOpen V') (hsub : V' ⊆ U') :
    IsExpChart g (U ∩ expPair g ⁻¹' V') V' W where
  isOpen := ((contDiffOn_expPair hg).continuousOn.mono fun p hp =>
    h.inExpDomain p hp).isOpen_inter_preimage h.isOpen hV'
  isOpen' := hV'
  inExpDomain p hp := h.inExpDomain p hp.1
  mapsTo p hp := hp.2
  inv_mem q hq := ⟨h.inv_mem q (hsub hq), by
    show expPair g (q.1, W q) ∈ V'
    rw [h.inv_apply (hsub hq)]
    exact hq⟩
  inv_expPair p hp := h.inv_expPair p hp.1
  expMap_inv q hq := h.expMap_inv q (hsub hq)
  smooth := h.smooth.mono hsub
  bijective p hp := h.bijective p hp.1

/-- Blueprint, Lemma `lem_world_function` (b): along a first-arrival null geodesic `σ`, the map
`𝐞(y, w) = (y, exp_y w)` is a diffeomorphism from a neighbourhood `U` of
`{(σ 0, t σ'(0)) : t ∈ [t₁, t₂]}` onto a neighbourhood `U'` of `{(σ 0, σ t)}`, and
`Q(y, p) = g_y(w, w)`, `(y, w) = 𝐞⁻¹(y, p)`, describes the causal and chronological relations
on `U'`. -/
theorem exists_worldFunction (hg : IsSpacetime g Y) {σ : ℝ → E n} {I : Set ℝ} {b : ℝ}
    (hσ : IsGeodesic g σ I) (hI : Icc 0 b ⊆ I)
    (hnull : form (g (σ 0)) (deriv σ 0) (deriv σ 0) = 0)
    (hfut : IsFutureCausal g Y (σ 0) (deriv σ 0)) (hfirst : ¬ ChronLT g Y (σ 0) (σ b))
    {t₁ t₂ : ℝ} (ht₁ : 0 < t₁) (ht₂ : t₂ < b) :
    ∃ U U' W, IsExpChart g U U' W ∧
      (∀ t ∈ Icc t₁ t₂, (σ 0, t • deriv σ 0) ∈ U) ∧
      (∀ t ∈ Icc t₁ t₂, (σ 0, σ t) ∈ U') ∧
      (∀ p ∈ U, p.2 ≠ 0 ∧ (form (g p.1) p.2 p.2 ≤ 0 → IsFutureCausal g Y p.1 p.2)) ∧
      ∀ q ∈ U', (CausalLE g Y q.1 q.2 ↔ form (g q.1) (W q) (W q) ≤ 0) ∧
        (ChronLT g Y q.1 q.2 ↔ form (g q.1) (W q) (W q) < 0) := by
  set y₀ := σ 0 with hy₀
  set v₀ := deriv σ 0 with hv₀
  have hIoo : ∀ t ∈ Icc t₁ t₂, t ∈ Ioo 0 b := fun t ht =>
    ⟨ht₁.trans_le ht.1, ht.2.trans_lt ht₂⟩
  have hexp : ∀ t ∈ Ioo 0 b, InExpDomain g y₀ (t • v₀) ∧ expMap g y₀ (t • v₀) = σ t :=
    fun t ht => hσ.expMap_smul_eq hg
      ((uIcc_subset_Icc ⟨le_rfl, ht.1.le.trans ht.2.le⟩ ⟨ht.1.le, ht.2.le⟩).trans hI)
  have hYc : Continuous Y := hg.globallyHyperbolic.timeOrientation.continuous
  set K := (fun t : ℝ => (y₀, t • v₀)) '' Icc t₁ t₂
  have hK : IsCompact K := isCompact_Icc.image (by fun_prop)
  set A := { p : E n × E n | form (g p.1) p.2 (Y p.1) < 0 }
  have hA : IsOpen A := isOpen_lt ((continuous_form hg).comp
    (continuous_fst.prodMk (continuous_snd.prodMk (hYc.comp continuous_fst)))) continuous_const
  set D := { p : E n × E n | InExpDomain g p.1 p.2 } ∩ A
  have hD : IsOpen D := (isOpen_expDomain hg).inter hA
  have hKD : K ⊆ D := by
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨(hexp t (hIoo t ht)).1, ?_⟩
    show form (g y₀) (t • v₀) (Y y₀) < 0
    rw [form_smul_left]
    exact mul_neg_of_pos_of_neg (ht₁.trans_le ht.1) hfut.future
  have hinjK : InjOn (expPair g) K := by
    rintro _ ⟨t, ht, rfl⟩ _ ⟨t', ht', rfl⟩ h
    simp only [expPair_def, Prod.mk.injEq, true_and] at h
    rw [(hexp t (hIoo t ht)).2, (hexp t' (hIoo t' ht')).2] at h
    have := eq_smul_of_expMap_eq hg hσ hI hfut hfirst (hIoo t' ht')
      (hfut.smul (ht₁.trans_le ht.1)) (hexp t (hIoo t ht)).1 ((hexp t (hIoo t ht)).2.trans h)
    simp only [Prod.mk.injEq, true_and]
    exact this
  have hderK : ∀ p ∈ K, ∃ f' : (E n × E n) ≃L[ℝ] (E n × E n),
      HasFDerivAt (expPair g) (f' : _ →L[ℝ] _) p := by
    rintro _ ⟨t, ht, rfl⟩
    refine exists_hasFDerivAt_expPair hg (hexp t (hIoo t ht)).1 ?_
    by_contra hcon
    exact hfirst (Facts.chronLT_of_conjugate hg hσ hI hnull hfut (hIoo t ht)
      (isConjugateAt_iff.2 hcon))
  obtain ⟨U₀, hU₀, hKU₀, hU₀D, hinj, himg, hder₀, h, hh, hhf⟩ :=
    exists_injOn_contDiffOn_inverse hD ((contDiffOn_expPair hg).mono inter_subset_left) hK hKD
      hinjK hderK
  have hev : ∀ t ∈ Icc t₁ t₂, ∃ V, (∀ q ∈ V, CausalLE g Y q.1 q.2 → ¬ ChronLT g Y q.1 q.2 →
      ∃ w, (q.1, w) ∈ U₀ ∧ IsFutureCausal g Y q.1 w ∧ InExpDomain g q.1 w ∧
        expMap g q.1 w = q.2) ∧ IsOpen V ∧ (y₀, σ t) ∈ V := fun t ht =>
    eventually_nhds_iff.1 (eventually_exists_mem hg hσ hI hfut hfirst (hIoo t ht) hU₀
      (hKU₀ ⟨t, ht, rfl⟩))
  choose! V hVP hVo hVmem using hev
  set U'₁ := expPair g '' U₀ ∩ ⋃ t ∈ Icc t₁ t₂, V t
  have hU'₁ : IsOpen U'₁ := himg.inter (isOpen_biUnion fun t ht => hVo t ht)
  set U₁ := U₀ ∩ expPair g ⁻¹' U'₁
  have hU₁ : IsOpen U₁ := ((contDiffOn_expPair hg).continuousOn.mono
    (hU₀D.trans inter_subset_left)).isOpen_inter_preimage hU₀ hU'₁
  set W : E n × E n → E n := fun q => (h q).2
  have hpre : ∀ q ∈ U'₁, ∃ p ∈ U₁, expPair g p = q ∧ (q.1, W q) = p := by
    rintro q hq
    obtain ⟨p, hp, rfl⟩ := hq.1
    refine ⟨p, ⟨hp, hq⟩, rfl, ?_⟩
    show ((expPair g p).1, (h (expPair g p)).2) = p
    rw [hhf p hp, expPair_fst]
  have hUA : ∀ p ∈ U₁, p ∈ A := fun p hp => (hU₀D hp.1).2
  have hfutU : ∀ p ∈ U₁, p.2 ≠ 0 ∧ (form (g p.1) p.2 p.2 ≤ 0 → IsFutureCausal g Y p.1 p.2) := by
    intro p hp
    have hpA : form (g p.1) p.2 (Y p.1) < 0 := hUA p hp
    have hne : p.2 ≠ 0 := by
      intro h0
      rw [h0, form_zero_left] at hpA
      exact lt_irrefl _ hpA
    exact ⟨hne, fun hc => ⟨hne, hc, hpA⟩⟩
  have chart₁ : IsExpChart g U₁ U'₁ W := by
    refine ⟨hU₁, hU'₁, fun p hp => (hU₀D hp.1).1, fun p hp => hp.2, ?_, ?_, ?_, ?_, ?_⟩
    · intro q hq
      obtain ⟨p, hp, -, hpq⟩ := hpre q hq
      rw [hpq]
      exact hp
    · intro p hp
      simp only [W, hhf p hp.1]
    · intro q hq
      obtain ⟨p, hp, hpq, hqp⟩ := hpre q hq
      have h1 : q.1 = p.1 := by rw [← hpq, expPair_fst]
      have h2 : W q = p.2 := (Prod.ext_iff.1 hqp).2
      rw [h1, h2, ← hpq, expPair_snd]
    · exact contDiff_snd.comp_contDiffOn (hh.mono inter_subset_left)
    · intro p hp
      obtain ⟨f', hf'⟩ := hder₀ p hp.1
      exact bijective_fderiv_expMap hg (hU₀D hp.1).1 hf'
  have hKU₁ : ∀ t ∈ Icc t₁ t₂, (y₀, t • v₀) ∈ U₁ := by
    intro t ht
    refine ⟨hKU₀ ⟨t, ht, rfl⟩, ⟨_, hKU₀ ⟨t, ht, rfl⟩, rfl⟩, mem_iUnion₂.2 ⟨t, ht, ?_⟩⟩
    simp only [expPair_def]
    rw [(hexp t (hIoo t ht)).2]
    exact hVmem t ht
  have hσU'₁ : ∀ t ∈ Icc t₁ t₂, (y₀, σ t) ∈ U'₁ := fun t ht => by
    have := chart₁.mapsTo _ (hKU₁ t ht)
    simpa [expPair_def, (hexp t (hIoo t ht)).2] using this
  have hhor : ∀ q ∈ U'₁, CausalLE g Y q.1 q.2 → ¬ ChronLT g Y q.1 q.2 →
      form (g q.1) (W q) (W q) ≤ 0 := by
    intro q hq hc hnc
    obtain ⟨p, hp, hpq, hqp⟩ := hpre q hq
    have hWq : W q = p.2 := (Prod.ext_iff.1 hqp).2
    obtain ⟨t, ht, hqV⟩ := mem_iUnion₂.1 hq.2
    obtain ⟨w, hw, hwf, -, hwe⟩ := hVP t ht q hqV hc hnc
    have : (q.1, w) = p := hinj hw hp.1 (by rw [hpq]; simp [expPair_def, hwe])
    rw [hWq, ← this]
    exact hwf.causal
  have hfut₁ : ∀ q ∈ U'₁, form (g q.1) (W q) (W q) ≤ 0 → IsFutureCausal g Y q.1 (W q) :=
    fun q hq hQ => (hfutU _ (chart₁.inv_mem q hq)).2 hQ
  have hnotσ : ∀ t ∈ Icc t₁ t₂, ¬ ChronLT g Y y₀ (σ t) := fun t ht hch => by
    have ht' := hIoo t ht
    have h0b : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, (ht'.1.trans ht'.2).le⟩
    exact hfirst (hch.trans_causalLE hg (hσ.causalLE ht'.2.le
      ((Icc_subset_Icc ht'.1.le le_rfl).trans hI) fun s hs =>
        hσ.isFutureCausal hg hI ordConnected_Icc h0b hfut ⟨ht'.1.le.trans hs.1, hs.2⟩))
  have hB : ∀ t ∈ Icc t₁ t₂, ∃ B, (∀ q ∈ B, ChronLT g Y q.1 q.2 →
      form (g q.1) (W q) (W q) < 0) ∧ IsOpen B ∧ (y₀, σ t) ∈ B := fun t ht =>
    eventually_nhds_iff.1 (eventually_chronLT_imp_form_neg hg hU'₁
      (chart₁.smooth.differentiableOn (by simp))
      (fun q hq => chart₁.inExpDomain _ (chart₁.inv_mem q hq)) chart₁.expMap_inv hfut₁ hhor
      (hσU'₁ t ht) (hnotσ t ht))
  choose! B hBP hBo hBmem using hB
  set U' := U'₁ ∩ ⋃ t ∈ Icc t₁ t₂, B t
  have hU' : IsOpen U' := hU'₁.inter (isOpen_biUnion fun t ht => hBo t ht)
  have chart : IsExpChart g (U₁ ∩ expPair g ⁻¹' U') U' W :=
    chart₁.restrict hg hU' inter_subset_left
  refine ⟨_, U', W, chart, fun t ht => ⟨hKU₁ t ht, ?_⟩, fun t ht =>
    ⟨hσU'₁ t ht, mem_iUnion₂.2 ⟨t, ht, hBmem t ht⟩⟩, fun p hp => hfutU p hp.1,
    fun q hq => ⟨⟨fun hc => ?_, fun hQ => ?_⟩, ⟨fun hch => ?_, fun hQ => ?_⟩⟩⟩
  · refine ⟨chart₁.mapsTo _ (hKU₁ t ht), mem_iUnion₂.2 ⟨t, ht, ?_⟩⟩
    rw [expPair_def, (hexp t (hIoo t ht)).2]
    exact hBmem t ht
  · by_cases hch : ChronLT g Y q.1 q.2
    · obtain ⟨t, ht, hqB⟩ := mem_iUnion₂.1 hq.2
      exact (hBP t ht q hqB hch).le
    · exact hhor q hq.1 hc hch
  · have := (chart.inExpDomain _ (chart.inv_mem q hq)).causalLE hg (hfut₁ q hq.1 hQ)
    rwa [chart.expMap_inv q hq] at this
  · obtain ⟨t, ht, hqB⟩ := mem_iUnion₂.1 hq.2
    exact hBP t ht q hqB hch
  · have := (chart.inExpDomain _ (chart.inv_mem q hq)).chronLT hg
      ⟨hQ, (hfut₁ q hq.1 hQ.le).future⟩
    rwa [chart.expMap_inv q hq] at this

end

end LorentzianCalderon
