module

public import LorentzianCalderon.Causal.Basic

public section

/-!
# Openness of the chronological future

Being future-directed timelike is an open condition on pairs of a point and a vector
(`eventually_isFutureTimelike`). Hence `I⁺(p)` is open (`Facts.isOpen_chronFuture`): near the
end `q` of a timelike curve from `p`, straight segments from a point of the curve shortly before
`q` are timelike. Every point lies in the chronological future and past of some point, so
`J⁺(K) ∩ J⁻(K')` lies in a finite union of causal diamonds for compact `K, K'`
(`exists_isCompact_superset_causalFutureSet_inter_causalPastSet`).
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Set Filter

variable {n : ℕ} {g : MatrixField n} {Y : E n → E n}

/-- Being future-directed timelike is an open condition on the point and the vector. -/
theorem eventually_isFutureTimelike (hg : IsSpacetime g Y) {q w : E n}
    (hw : IsFutureTimelike g Y q w) :
    ∀ᶠ p : E n × E n in 𝓝 (q, w), IsFutureTimelike g Y p.1 p.2 := by
  have hY := hg.globallyHyperbolic.timeOrientation.continuous
  have h1 : Continuous fun p : E n × E n => form (g p.1) p.2 p.2 :=
    (continuous_form hg).comp (continuous_fst.prodMk (continuous_snd.prodMk continuous_snd))
  have h2 : Continuous fun p : E n × E n => form (g p.1) p.2 (Y p.1) :=
    (continuous_form hg).comp
      (continuous_fst.prodMk (continuous_snd.prodMk (hY.comp continuous_fst)))
  filter_upwards [(h1.tendsto (q, w)).eventually (eventually_lt_nhds hw.timelike),
    (h2.tendsto (q, w)).eventually (eventually_lt_nhds hw.future)] with p hp1 hp2
  exact ⟨hp1, hp2⟩

/-- A radius `ε` such that vectors `ε`-close to a future-directed timelike vector, at points
`ε`-close to its base point, are future-directed timelike. -/
theorem exists_isFutureTimelike_of_dist_lt (hg : IsSpacetime g Y) {q w : E n}
    (hw : IsFutureTimelike g Y q w) :
    ∃ ε > 0, ∀ x v, dist x q < ε → dist v w < ε → IsFutureTimelike g Y x v := by
  obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.1 (eventually_isFutureTimelike hg hw)
  exact ⟨ε, hε, fun x v hx hv => h (y := (x, v)) (by rw [Prod.dist_eq]; exact max_lt hx hv)⟩

/-- `I⁺(p)` is open. O'Neill, Semi-Riemannian geometry, Lemma 14.3, p. 403. -/
theorem Facts.isOpen_chronFuture (hg : IsSpacetime g Y) (p : E n) :
    IsOpen (chronFuture g Y p) := by
  classical
  rw [Metric.isOpen_iff]
  intro q hq
  obtain ⟨γ, hγ, hγ0, hγ1⟩ := chronLT_iff.1 (mem_chronFuture.1 hq)
  obtain ⟨-, F, hF⟩ := isPathOn_iff.1 hγ
  set F' := insert 0 (F.filter (· < 1))
  have hne : F'.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
  set x₀ := F'.max' hne
  have hx₀ : x₀ < 1 := (Finset.max'_lt_iff _ hne).2 fun z hz => by
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact one_pos
    · exact (Finset.mem_filter.1 hz).2
  have hx₀0 : 0 ≤ x₀ := Finset.le_max' _ _ (Finset.mem_insert_self _ _)
  obtain ⟨hsm, hvel⟩ := isPathPiece_iff.1 <| hF x₀ 1 hx₀0 hx₀ le_rfl fun z hz hzI =>
    (not_lt.2 (Finset.le_max' F' z
      (Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hz, hzI.2⟩)))) hzI.1
  have h1 : (1 : ℝ) ∈ Icc x₀ 1 := ⟨hx₀.le, le_rfl⟩
  set w := derivWithin γ (Icc x₀ 1) 1
  have hw : IsFutureTimelike g Y q w := hγ1 ▸ hvel 1 h1
  have hd : HasDerivWithinAt γ w (Icc x₀ 1) 1 :=
    (hsm.differentiableOn (by simp) 1 h1).hasDerivWithinAt
  obtain ⟨ε, hε, hεP⟩ := exists_isFutureTimelike_of_dist_lt hg hw
  have hle : 𝓝[<] (1 : ℝ) ≤ 𝓝[Icc x₀ 1 \ {1}] 1 :=
    nhdsWithin_le_of_mem (mem_of_superset (Ioo_mem_nhdsLT hx₀)
      fun t ht => ⟨⟨ht.1.le, ht.2.le⟩, ht.2.ne⟩)
  have hslope := (hasDerivWithinAt_iff_tendsto_slope.1 hd).mono_left hle
  have hcont : Tendsto γ (𝓝[<] 1) (𝓝 q) :=
    hγ1 ▸ hd.continuousWithinAt.tendsto.mono_left (hle.trans (nhdsWithin_mono _ sdiff_subset))
  obtain ⟨t, ⟨hts, htγ⟩, htI⟩ := ((hslope.eventually (Metric.ball_mem_nhds w (half_pos hε))).and
    (hcont.eventually (Metric.ball_mem_nhds q (half_pos hε)))).and
    (Ioo_mem_nhdsLT hx₀) |>.exists

  set δ := 1 - t
  have hδ : 0 < δ := sub_pos.2 htI.2
  have hδ1 : δ ≤ 1 := by simp only [δ]; linarith [htI.1]
  set a := γ t
  have hslope_eq : slope γ 1 t = δ⁻¹ • (q - a) := by
    rw [slope_def_module, hγ1, show t - 1 = -δ by ring, inv_neg, neg_smul, ← smul_neg, neg_sub]
  rw [hslope_eq] at hts
  refine ⟨δ * ε / 2, by positivity, fun q' hq' => ?_⟩
  rw [Metric.mem_ball] at hq'
  have hq'ε : dist q' q < ε / 2 := hq'.trans_le (by nlinarith)
  have hpa : ChronLT g Y p a := by
    have := chronLT_of_isPathOn (hγ.restrict le_rfl (hx₀0.trans_lt htI.1) htI.2.le)
    rwa [hγ0] at this
  have hline : IsPathOn (IsFutureTimelike g Y) 0 1 fun s : ℝ => a + s • (q' - a) := by
    refine isPathOn_line zero_lt_one fun s hs => ?_
    rw [← isFutureTimelike_smul_iff (inv_pos.2 hδ)]
    refine hεP _ _ ?_ ?_
    · have heq : a + s • (q' - a) - q = (1 - s) • (a - q) + s • (q' - q) := by
        simp only [smul_sub, sub_smul, one_smul]
        abel
      rw [dist_eq_norm, heq]
      have h1 : ‖(1 - s) • (a - q)‖ ≤ (1 - s) * (ε / 2) := by
        rw [norm_smul, Real.norm_of_nonneg (by linarith [hs.2])]
        exact mul_le_mul_of_nonneg_left (by rw [← dist_eq_norm]; exact htγ.le)
          (by linarith [hs.2])
      have h2 : ‖s • (q' - q)‖ ≤ s * (ε / 2) := by
        rw [norm_smul, Real.norm_of_nonneg hs.1]
        exact mul_le_mul_of_nonneg_left (by rw [← dist_eq_norm]; exact hq'ε.le) hs.1
      linarith [norm_add_le ((1 - s) • (a - q)) (s • (q' - q))]
    · have heq : δ⁻¹ • (q' - a) - w = (δ⁻¹ • (q - a) - w) + δ⁻¹ • (q' - q) := by
        simp only [smul_sub]
        abel
      rw [dist_eq_norm, heq]
      have h2 : ‖δ⁻¹ • (q' - q)‖ < ε / 2 := by
        rw [norm_smul, Real.norm_of_nonneg (inv_pos.2 hδ).le, ← dist_eq_norm,
          inv_mul_lt_iff₀ hδ]
        linarith
      have h1 : ‖δ⁻¹ • (q - a) - w‖ < ε / 2 := by rwa [← dist_eq_norm]
      linarith [norm_add_le (δ⁻¹ • (q - a) - w) (δ⁻¹ • (q' - q))]
  have haq' : ChronLT g Y a q' := by simpa using chronLT_of_isPathOn hline
  exact mem_chronFuture.2 (hpa.trans haq')

theorem isOpen_chronPast (hg : IsSpacetime g Y) (q : E n) : IsOpen (chronPast g Y q) := by
  rw [← chronFuture_neg]
  exact Facts.isOpen_chronFuture hg.neg q

/-- Every point lies in the chronological future of some point. -/
theorem exists_chronLT_left (hg : IsSpacetime g Y) (x : E n) : ∃ p, ChronLT g Y p x := by
  have hYt := hg.globallyHyperbolic.timeOrientation.timelike x
  obtain ⟨ε, hε, hεP⟩ := exists_isFutureTimelike_of_dist_lt hg (w := Y x) ⟨hYt, hYt⟩
  set s := ε / (2 * (‖Y x‖ + 1))
  have hs : 0 < s := by positivity
  have hsY : s * ‖Y x‖ < ε := by
    have : s * (‖Y x‖ + 1) = ε / 2 := by
      simp only [s]
      field_simp
    nlinarith [norm_nonneg (Y x)]
  refine ⟨x - s • Y x, ?_⟩
  have := chronLT_of_isPathOn (isPathOn_line (x := x - s • Y x) (v := Y x) hs fun r hr =>
    hεP _ _ ?_ (by simpa using hε))
  · simpa using this
  · rw [dist_eq_norm, show x - s • Y x + r • Y x - x = (r - s) • Y x by
      simp only [sub_smul]; abel, norm_smul, Real.norm_of_nonpos (by linarith [hr.2])]
    nlinarith [norm_nonneg (Y x), hr.1]

/-- Every point lies in the chronological past of some point. -/
theorem exists_chronLT_right (hg : IsSpacetime g Y) (x : E n) : ∃ q, ChronLT g Y x q := by
  obtain ⟨q, hq⟩ := exists_chronLT_left hg.neg x
  exact ⟨q, chronLT_neg_iff.1 hq⟩

/-- `J⁺(K) ∩ J⁻(K')` lies in a finite union of causal diamonds for compact `K, K'`. -/
theorem exists_isCompact_superset_causalFutureSet_inter_causalPastSet (hg : IsSpacetime g Y)
    {K K' : Set (E n)} (hK : IsCompact K) (hK' : IsCompact K') :
    ∃ C, IsCompact C ∧ causalFutureSet g Y K ∩ causalPastSet g Y K' ⊆ C := by
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun p => chronFuture g Y p)
    (fun p => Facts.isOpen_chronFuture hg p)
    fun x _ => mem_iUnion.2 ((exists_chronLT_left hg x).imp fun _ h => mem_chronFuture.2 h)
  obtain ⟨t', ht'⟩ := hK'.elim_finite_subcover (fun q => chronPast g Y q)
    (fun q => isOpen_chronPast hg q)
    fun x _ => mem_iUnion.2 ((exists_chronLT_right hg x).imp fun _ h => mem_chronPast.2 h)
  refine ⟨⋃ p ∈ t, ⋃ q ∈ t', causalFuture g Y p ∩ causalPast g Y q,
    t.isCompact_biUnion fun p _ => t'.isCompact_biUnion fun q _ =>
      hg.globallyHyperbolic.compact_diamond p q, ?_⟩
  rintro x ⟨hx, hx'⟩
  obtain ⟨k, hk, hkx⟩ := mem_causalFutureSet.1 hx
  obtain ⟨k', hk', hxk'⟩ := mem_causalPastSet.1 hx'
  obtain ⟨p, hp, hpk⟩ := mem_iUnion₂.1 (ht hk)
  obtain ⟨q, hq, hk'q⟩ := mem_iUnion₂.1 (ht' hk')
  exact mem_iUnion₂.2 ⟨p, hp, mem_iUnion₂.2 ⟨q, hq,
    mem_causalFuture.2 ((ChronLT.causalLE (mem_chronFuture.1 hpk)).trans
      (mem_causalFuture.1 hkx)),
    mem_causalPast.2 ((mem_causalPast.1 hxk').trans (ChronLT.causalLE (mem_chronPast.1 hk'q)))⟩⟩

end

end LorentzianCalderon
