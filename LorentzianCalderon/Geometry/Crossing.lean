module

public import LorentzianCalderon.Geometry.Horismos
public import LorentzianCalderon.Geometry.ExpDeriv

public section

/-!
# Chronological pairs in an exponential chart

Let `W` invert `(y, w) ↦ (y, exp_y w)` on an open set `O` of pairs, with `W q` future causal
where it is causal, and `g(W q, W q) ≤ 0` for pairs in the horismos (`q.1 ≤ q.2`, not
`q.1 ≪ q.2`). Near a pair `p ∈ O` with `p.1 ≪ p.2` false, chronological pairs then have
`g(W q, W q) < 0` (`eventually_chronLT_imp_form_neg`). Proof: move `q.2` to the past along the
line `s ↦ q.2 - s Y(q.2)` until it leaves `I⁺(q.1)`; the exit point is in the horismos of `q.1`,
as `J⁺(q.1)` is closed. Along the line, `f(s) = g(W, W)` has positive derivative where it
vanishes (Gauss lemma), so it cannot pass from a positive value at `s = 0` to a nonpositive one.
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Set Filter

variable {n : ℕ} {g : MatrixField n} {Y : E n → E n}

/-- A function with positive derivative at `x` is smaller than `f x` just left of `x`. -/
theorem HasDerivAt.eventually_lt_left {f : ℝ → ℝ} {f' x : ℝ} (h : HasDerivAt f f' x)
    (hf : 0 < f') : ∀ᶠ s in 𝓝[<] x, f s < f x := by
  filter_upwards [(hasDerivAt_iff_tendsto_slope_left_right.1 h).1.eventually (lt_mem_nhds hf),
    self_mem_nhdsWithin] with s hs hsx
  rw [slope_def_field] at hs
  have := (lt_div_iff_of_neg (sub_neg.2 (show s < x from hsx))).1 hs
  rw [zero_mul] at this
  linarith

/-- A function with positive derivative at `x` is larger than `f x` just right of `x`. -/
theorem HasDerivAt.eventually_gt_right {f : ℝ → ℝ} {f' x : ℝ} (h : HasDerivAt f f' x)
    (hf : 0 < f') : ∀ᶠ s in 𝓝[>] x, f x < f s := by
  filter_upwards [(hasDerivAt_iff_tendsto_slope_left_right.1 h).2.eventually (lt_mem_nhds hf),
    self_mem_nhdsWithin] with s hs hsx
  rw [slope_def_field] at hs
  have := (lt_div_iff₀ (sub_pos.2 (show x < s from hsx))).1 hs
  rw [zero_mul] at this
  linarith

/-- A function with positive derivative at its zeros stays positive after a nonnegative
value. -/
theorem pos_of_hasDerivAt {f f' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hd : ∀ s ∈ Icc a b, HasDerivAt f (f' s) s) (hz : ∀ s ∈ Icc a b, f s = 0 → 0 < f' s)
    (ha : 0 ≤ f a) : 0 < f b := by
  have hc : ContinuousOn f (Icc a b) := fun s hs => (hd s hs).continuousAt.continuousWithinAt
  have haI : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hright : ∀ᶠ s in 𝓝[>] a, 0 < f s := by
    rcases ha.lt_or_eq with ha | ha
    · exact ((hd a haI).continuousAt.tendsto.eventually (lt_mem_nhds ha)).filter_mono
        nhdsWithin_le_nhds
    · filter_upwards [HasDerivAt.eventually_gt_right (hd a haI) (hz a haI ha.symm)] with s hs
      rwa [← ha] at hs
  obtain ⟨u, hu, hua⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hright
  set a₁ := min ((a + u) / 2) ((a + b) / 2)
  have hu' : a < u := hu
  have ha₁ : a < a₁ := lt_min (by linarith) (by linarith)
  have ha₁u : a₁ < u := (min_le_left _ _).trans_lt (by linarith)
  have ha₁b : a₁ < b := (min_le_right _ _).trans_lt (by linarith)
  have hpos₁ : ∀ s ∈ Ioc a a₁, 0 < f s := fun s hs => hua ⟨hs.1, hs.2.trans_lt ha₁u⟩
  by_contra hb
  push Not at hb
  set T := {s ∈ Icc a₁ b | f s ≤ 0}
  have hT : IsClosed T := (hc.mono (Icc_subset_Icc ha₁.le le_rfl)).preimage_isClosed_of_isClosed
    isClosed_Icc isClosed_Iic
  have hTb : BddBelow T := ⟨a₁, fun s hs => hs.1.1⟩
  set s₀ := sInf T
  have hs₀ : s₀ ∈ T := hT.csInf_mem ⟨b, ⟨ha₁b.le, le_rfl⟩, hb⟩ hTb
  have hs₀a₁ : a₁ < s₀ := lt_of_le_of_ne hs₀.1.1 fun e => by
    have := hpos₁ a₁ ⟨ha₁, le_rfl⟩
    rw [e] at this
    linarith [hs₀.2]
  have hpos : ∀ s ∈ Ioo a s₀, 0 < f s := by
    intro s hs
    by_cases h : s ≤ a₁
    · exact hpos₁ s ⟨hs.1, h⟩
    · by_contra h'
      push Not at h'
      exact absurd (csInf_le hTb ⟨⟨(not_le.1 h).le, hs.2.le.trans hs₀.1.2⟩, h'⟩)
        (not_le.2 hs.2)
  have hs₀I : s₀ ∈ Icc a b := ⟨ha₁.le.trans hs₀.1.1, hs₀.1.2⟩
  have hneg : ∀ᶠ s in 𝓝[<] s₀, f s < 0 := by
    rcases hs₀.2.lt_or_eq with hlt | heq
    · exact ((hd s₀ hs₀I).continuousAt.tendsto.eventually (gt_mem_nhds hlt)).filter_mono
        nhdsWithin_le_nhds
    · filter_upwards [HasDerivAt.eventually_lt_left (hd s₀ hs₀I) (hz s₀ hs₀I heq)] with s hs
      rwa [heq] at hs
  obtain ⟨s, hs1, hs2⟩ := (hneg.and (Ioo_mem_nhdsLT hs₀a₁)).exists
  exact absurd (hpos s ⟨ha₁.trans hs2.1, hs2.2⟩) (not_lt.2 hs1.le)

/-- Along the line `r ↦ (a, x - r v)` with `v` future timelike, `r ↦ g_a(W, W)` is
differentiable, with positive derivative where it vanishes (Gauss lemma). -/
theorem exists_hasDerivAt_form_inv (hg : IsSpacetime g Y) {O : Set (E n × E n)}
    (hO : IsOpen O) {W : E n × E n → E n} (hWs : DifferentiableOn ℝ W O)
    (hdom : ∀ q ∈ O, InExpDomain g q.1 (W q)) (hexp : ∀ q ∈ O, expMap g q.1 (W q) = q.2)
    (hfut : ∀ q ∈ O, form (g q.1) (W q) (W q) ≤ 0 → IsFutureCausal g Y q.1 (W q))
    {a x v : E n} {s : ℝ} (hs : (a, x - s • v) ∈ O)
    (hv : IsFutureTimelike g Y (x - s • v) v) :
    ∃ f', HasDerivAt (fun r : ℝ => form (g a) (W (a, x - r • v)) (W (a, x - r • v))) f' s ∧
      (form (g a) (W (a, x - s • v)) (W (a, x - s • v)) = 0 → 0 < f') := by
  have hline : HasDerivAt (fun r : ℝ => x - r • v) (-v) s := by
    simpa using ((hasDerivAt_id s).smul_const v).const_sub x
  have hc : HasDerivAt (fun r : ℝ => (a, x - r • v)) ((0 : E n), -v) s :=
    (hasDerivAt_const s a).prodMk hline
  have hW : HasFDerivAt W (fderiv ℝ W (a, x - s • v)) (a, x - s • v) :=
    (hWs.differentiableAt (hO.mem_nhds hs)).hasFDerivAt
  set u := fderiv ℝ W (a, x - s • v) ((0 : E n), -v)
  have hΦ : HasDerivAt (fun r : ℝ => W (a, x - r • v)) u s := hW.comp_hasDerivAt s hc
  set w := W (a, x - s • v)
  have hdw : InExpDomain g a w := hdom _ hs
  have hew : expMap g a w = x - s • v := hexp _ hs
  set D := fderiv ℝ (expMap g a) w
  have hD : HasFDerivAt (expMap g a) D w :=
    (hasFDerivAt_expMap hg (p := (a, w)) hdw).differentiableAt.hasFDerivAt
  have hDu : D u = -v := by
    have h1 := hD.comp_hasDerivAt s hΦ
    rw [Function.comp_def] at h1
    have hev : (fun r : ℝ => expMap g a (W (a, x - r • v))) =ᶠ[𝓝 s] fun r => x - r • v := by
      filter_upwards [hc.continuousAt.preimage_mem_nhds (hO.mem_nhds hs)] with r hr
      exact hexp _ hr
    exact h1.unique (hline.congr_of_eventuallyEq hev)
  refine ⟨2 * form (g a) w u, hasDerivWithinAt_univ.1
    (HasDerivWithinAt.form_self (hg.symm a) (hΦ.hasDerivWithinAt (s := univ))), fun h0 => ?_⟩
  have hwf : IsFutureCausal g Y a w := hfut _ hs h0.le
  have hgauss := form_fderiv_expMap_radial hg hdw u
  have hDw := hdw.isFutureCausal_fderiv hg hwf
  rw [hDu, hew] at hgauss
  rw [hew] at hDw
  have hneg := IsFutureTimelike.form_neg (hg.lorentzian _)
    (hg.globallyHyperbolic.timeOrientation.timelike _) hv hDw
  rw [← hgauss, form_neg_right, form_comm (hg.symm _)]
  linarith

/-- In an exponential chart `W` on `O` that is future causal where causal and causal on the
horismos, pairs near a pair `p ∈ O` with `p.1 ≪ p.2` false are chronological only where
`g(W, W) < 0`. -/
theorem eventually_chronLT_imp_form_neg (hg : IsSpacetime g Y) {O : Set (E n × E n)}
    (hO : IsOpen O) {W : E n × E n → E n} (hWs : DifferentiableOn ℝ W O)
    (hdom : ∀ q ∈ O, InExpDomain g q.1 (W q)) (hexp : ∀ q ∈ O, expMap g q.1 (W q) = q.2)
    (hfut : ∀ q ∈ O, form (g q.1) (W q) (W q) ≤ 0 → IsFutureCausal g Y q.1 (W q))
    (hhor : ∀ q ∈ O, CausalLE g Y q.1 q.2 → ¬ ChronLT g Y q.1 q.2 →
      form (g q.1) (W q) (W q) ≤ 0)
    {p : E n × E n} (hp : p ∈ O) (hnot : ¬ ChronLT g Y p.1 p.2) :
    ∀ᶠ q in 𝓝 p, ChronLT g Y q.1 q.2 → form (g q.1) (W q) (W q) < 0 := by
  have hYc : Continuous Y := hg.globallyHyperbolic.timeOrientation.continuous
  set P : (E n × E n) × ℝ → Prop := fun z => (z.1.1, z.1.2 - z.2 • Y z.1.2) ∈ O ∧
    IsFutureTimelike g Y (z.1.2 - z.2 • Y z.1.2) (Y z.1.2) with hP_def
  have hPo : IsOpen {z | P z} := by
    have hT : IsOpen {pv : E n × E n | IsFutureTimelike g Y pv.1 pv.2} :=
      isOpen_iff_mem_nhds.2 fun pv h => eventually_isFutureTimelike hg h
    have h1 : Continuous fun z : (E n × E n) × ℝ => (z.1.1, z.1.2 - z.2 • Y z.1.2) := by
      fun_prop
    have h2 : Continuous fun z : (E n × E n) × ℝ => (z.1.2 - z.2 • Y z.1.2, Y z.1.2) := by
      fun_prop
    exact (hO.preimage h1).inter (hT.preimage h2)
  have hP0 : P (p, 0) := by
    have hYt := hg.globallyHyperbolic.timeOrientation.timelike p.2
    simp only [P, zero_smul, sub_zero]
    exact ⟨hp, hYt, hYt⟩
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.isOpen_iff.1
    (hPo.preimage (continuous_const.prodMk continuous_id : Continuous fun s : ℝ => (p, s))) 0 hP0
  set δ := δ₀ / 2 with hδ_def
  have hδ : 0 < δ := half_pos hδ₀
  have hPs : ∀ s ∈ Icc 0 δ, P (p, s) := fun s hs => hball (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hs.1]
    linarith [hs.2, hδ_def])
  have hend : ¬ CausalLE g Y p.1 (p.2 - δ • Y p.2) := by
    intro h
    refine hnot (h.trans_chronLT hg ?_)
    have := chronLT_of_isPathOn (isPathOn_line (P := IsFutureTimelike g Y)
      (x := p.2 - δ • Y p.2) (v := Y p.2) hδ fun t ht => ?_)
    · simpa using this
    · have := (hPs (δ - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩).2
      convert this using 2
      rw [sub_smul]
      abel
  have hN1 : ∀ᶠ q in 𝓝 p, ∀ s ∈ Icc 0 δ, P (q, s) :=
    isCompact_Icc.eventually_forall_of_forall_eventually fun s hs => hPo.mem_nhds (hPs s hs)
  have hN2 : ∀ᶠ q in 𝓝 p, ¬ CausalLE g Y q.1 (q.2 - δ • Y q.2) := by
    have hcont : Continuous fun q : E n × E n => (q.1, q.2 - δ • Y q.2) := by fun_prop
    exact hcont.continuousAt.preimage_mem_nhds
      ((Facts.isClosed_causalLE hg).isOpen_compl.mem_nhds hend)
  have hle : ∀ q : E n × E n, (∀ s ∈ Icc 0 δ, P (q, s)) →
      ¬ CausalLE g Y q.1 (q.2 - δ • Y q.2) → ChronLT g Y q.1 q.2 →
      form (g q.1) (W q) (W q) ≤ 0 := by
    intro q hq hqe hch
    by_contra hpos
    push Not at hpos
    have hcc : Continuous fun s : ℝ => q.2 - s • Y q.2 := by fun_prop
    set T := {s ∈ Icc 0 δ | ¬ ChronLT g Y q.1 (q.2 - s • Y q.2)}
    have hT : IsClosed T := by
      have : T = Icc 0 δ ∩ ((fun s => q.2 - s • Y q.2) ⁻¹' (chronFuture g Y q.1)ᶜ) := by
        ext s
        simp [T, mem_chronFuture]
      rw [this]
      exact isClosed_Icc.inter ((Facts.isOpen_chronFuture hg q.1).isClosed_compl.preimage hcc)
    have hTb : BddBelow T := ⟨0, fun s hs => hs.1.1⟩
    set s₀ := sInf T
    have hs₀ : s₀ ∈ T := hT.csInf_mem ⟨δ, ⟨hδ.le, le_rfl⟩, fun h => hqe h.causalLE⟩ hTb
    have hs₀pos : 0 < s₀ := lt_of_le_of_ne hs₀.1.1 fun e => hs₀.2 (by rw [← e]; simpa using hch)
    have hchron : ∀ s ∈ Ico 0 s₀, ChronLT g Y q.1 (q.2 - s • Y q.2) := fun s hs => by
      by_contra h
      exact absurd (csInf_le hTb ⟨⟨hs.1, hs.2.le.trans hs₀.1.2⟩, h⟩) (not_le.2 hs.2)
    have hcaus : CausalLE g Y q.1 (q.2 - s₀ • Y q.2) := by
      refine mem_causalFuture.1 <| (isClosed_causalFuture hg q.1).mem_of_tendsto
        (hcc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds :
          Tendsto (fun s : ℝ => q.2 - s • Y q.2) (𝓝[<] s₀) _) ?_
      filter_upwards [Ioo_mem_nhdsLT hs₀pos] with s hs
      exact mem_causalFuture.2 (hchron s ⟨hs.1.le, hs.2⟩).causalLE
    have hf₀ := hhor _ (hq s₀ hs₀.1).1 hcaus hs₀.2
    have hd : ∀ s ∈ Icc 0 s₀, ∃ f', HasDerivAt (fun r : ℝ =>
        form (g q.1) (W (q.1, q.2 - r • Y q.2)) (W (q.1, q.2 - r • Y q.2))) f' s ∧
        (form (g q.1) (W (q.1, q.2 - s • Y q.2)) (W (q.1, q.2 - s • Y q.2)) = 0 → 0 < f') :=
      fun s hs => exists_hasDerivAt_form_inv hg hO hWs hdom hexp hfut
        (hq s ⟨hs.1, hs.2.trans hs₀.1.2⟩).1 (hq s ⟨hs.1, hs.2.trans hs₀.1.2⟩).2
    choose! f' hf' hf'z using hd
    have := pos_of_hasDerivAt hs₀pos hf' hf'z (by simpa using hpos.le)
    exact absurd hf₀ (not_le.2 this)
  obtain ⟨N, hNsub, hNo, hpN⟩ := eventually_nhds_iff.1 (hN1.and hN2)
  filter_upwards [hNo.mem_nhds hpN] with q hqN hch
  refine lt_of_le_of_ne (hle q (hNsub q hqN).1 (hNsub q hqN).2 hch) fun heq => ?_
  have hq0 := (hNsub q hqN).1 0 ⟨le_rfl, hδ.le⟩
  obtain ⟨f', hf', hf'z⟩ := exists_hasDerivAt_form_inv hg hO hWs hdom hexp hfut hq0.1 hq0.2
  have h0 : form (g q.1) (W (q.1, q.2 - (0 : ℝ) • Y q.2)) (W (q.1, q.2 - (0 : ℝ) • Y q.2)) = 0 := by
    simpa using heq
  have hline : Tendsto (fun s : ℝ => q.2 - s • Y q.2) (𝓝[>] 0) (𝓝 q.2) := by
    have : Continuous fun s : ℝ => q.2 - s • Y q.2 := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hpair : Tendsto (fun s : ℝ => (q.1, q.2 - s • Y q.2)) (𝓝[>] 0) (𝓝 q) :=
    tendsto_const_nhds.prodMk_nhds hline
  obtain ⟨s, hs1, hs2, hs3⟩ := ((HasDerivAt.eventually_gt_right hf' (hf'z h0)).and
    ((hpair.eventually (hNo.mem_nhds hqN)).and
      (hline.eventually ((Facts.isOpen_chronFuture hg q.1).mem_nhds
        (mem_chronFuture.2 hch))))).exists
  rw [h0] at hs1
  exact absurd (hle _ (hNsub _ hs2).1 (hNsub _ hs2).2 (mem_chronFuture.1 hs3)) (not_le.2 hs1)

end

end LorentzianCalderon
