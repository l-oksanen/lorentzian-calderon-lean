module

public import LorentzianCalderon.Green.Lens
public import LorentzianCalderon.Causal.Chron

public section

/-!
# Support of solutions for narrowed metrics

`support_subset_of_narrow`: for a standard time `ψ` there is `ε₀ > 0` such that for
`0 < ε ≤ ε₀`, a `C²` function `V` with `□_{g_ε} V = 0` off `J⁺(K)` that vanishes on `{ψ < t₀}`
is supported in `J⁺(K)`, for `g_ε = g + ε dψ ⊗ dψ` (`narrow`). No compactness of `K` and no
closedness of `J⁺(K)` is needed.

The proof is a sweep in `ψ`. Fix `y ∉ J⁺(K)`; then `I⁻(y) ∩ J⁺(K) = ∅`, so `□_{g_ε} V = 0` on
`I⁻(y)`. The points of `I⁻(y) ∩ {ψ ≥ t₀}` lie in a closed ball `B` (steepness of `ψ`), and
`exists_frozen_radius` gives a radius `r` of frozen cones uniform on `B`; let `δ = κ r / 8`.
If `V = 0` on `I⁻(y) ∩ {ψ < τ}` and `w ∈ I⁻(y)` has `τ ≤ ψ w < τ + δ`, take `y' = w + η N(w)`
in `I⁻(y)` and the frozen lens `L = {p ∈ U | ψ p ≥ τ - δ, Q p ≥ Q(w)/2}` with
`Q(p) = -ǧ(y' - p, y' - p)` (`eq_zero_of_frozenLens`). Straight segments from `L` to `y'` are
`g`-timelike, so `L ⊆ I⁻(y') ⊆ I⁻(y)` and `L ⊆ B(y', r/4)`, its bottom lies in
`I⁻(y) ∩ {ψ < τ}`, and the lens lemma for `g_ε` with the past orientation `-N` gives
`V(w) = 0`. Finitely many steps give `V = 0` on `I⁻(y)`, and `y ∈ closure I⁻(y)`.
-/

namespace LorentzianCalderon

noncomputable section
open Set Matrix WithLp Filter Metric
open scoped ContDiff Topology

variable {n : ℕ} {g : MatrixField n} {Y : E n → E n} {ψ : E n → ℝ} {ε : ℝ}

/-- A frozen comparison on `B(w, r)`, the conclusion of `exists_frozen_radius` at `w`. -/
def FrozenAt (g : MatrixField n) (ψ : E n → ℝ) (ε : ℝ) (w : E n) (r : ℝ) : Prop :=
  ∀ p, dist p w < r → ∀ v, v ≠ 0 → form (narrow g ψ (ε / 2) w) v v ≤ 0 →
    0 ≤ fderiv ℝ ψ w v →
    coform (narrow g ψ ε) p (narrow g ψ (ε / 2) w *ᵥ ofLp v)
        (narrow g ψ (ε / 2) w *ᵥ ofLp v) < 0 ∧
      form (narrow g ψ (ε / 2) w) v (-grad g ψ p) < 0 ∧
      form (g p) v v < 0 ∧ 0 < fderiv ℝ ψ p v

/-- Straight segments in `B(w, r)` along future causal vectors of `ǧ` are `g`-timelike. -/
theorem FrozenAt.isPathOn (hg : IsSpacetime g Y) (hψ : IsStandardTime g Y ψ) {w : E n} {r : ℝ}
    (hfr : FrozenAt g ψ ε w r) {p y : E n} (hp : dist p w < r) (hy : dist y w < r)
    (hv0 : y - p ≠ 0) (hvv : form (narrow g ψ (ε / 2) w) (y - p) (y - p) ≤ 0)
    (hvf : 0 ≤ fderiv ℝ ψ w (y - p)) :
    IsPathOn (IsFutureTimelike g Y) 0 1 (fun t => p + t • (y - p)) := by
  refine isPathOn_line zero_lt_one fun t ht => ?_
  have hq : dist (p + t • (y - p)) w < r :=
    (convex_ball w r).add_smul_sub_mem (mem_ball.2 hp) (mem_ball.2 hy) ht
  obtain ⟨-, -, h3, h4⟩ := hfr _ hq _ hv0 hvv hvf
  refine (hψ.past_gradient _).of_form_neg_left (hg.lorentzian _)
    (hg.globallyHyperbolic.timeOrientation.timelike _) h3 ?_
  rw [form_neg_grad_left (hg.lorentzian _)]
  linarith

/-- **The frozen lens step.** If `□_{g_ε} V = 0` on `I⁻(y)` and `V = 0` on
`I⁻(y) ∩ {ψ < τ}`, then `V(w) = 0` for `w ∈ I⁻(y)` with `τ ≤ ψ(w) < τ + κ r / 8`, given frozen
cones on `B(w, r)` and the steepness constant `κ`. -/
theorem eq_zero_of_frozenLens (hg : IsSpacetime g Y) (hψ : IsStandardTime g Y ψ) (hε : 0 < ε)
    (hε1 : ∀ x, 1 / 2 ≤ 1 + ε * coform g x (d ψ x) (d ψ x)) {κ : ℝ} (hκ : 0 < κ)
    (hsteep : ∀ x v, IsFutureCausal g Y x v → κ * ‖v‖ ≤ fderiv ℝ ψ x v)
    {w : E n} {r : ℝ} (hr : 0 < r) (hfr : FrozenAt g ψ ε w r)
    {V : E n → ℝ} (hV : ContDiff ℝ 2 V) {y : E n} {τ : ℝ}
    (hbox : ∀ p, ChronLT g Y p y → box (narrow g ψ ε) V p = 0)
    (hO : ∀ p, ChronLT g Y p y → ψ p < τ → V p = 0)
    (hwy : ChronLT g Y w y) (hτw : τ ≤ ψ w) (hwδ : ψ w < τ + κ * r / 8) : V w = 0 := by
  set δ := κ * r / 8 with hδ_def
  have hδ : 0 < δ := by positivity
  set N : E n → E n := fun x => -grad g ψ x with hN_def
  have hψ1 : ContDiff ℝ 1 ψ := hψ.smooth.of_le (by simp)
  have hs : ∀ x, coform g x (d ψ x) (d ψ x) < 0 := fun x =>
    coform_self_neg_of_future (hg.lorentzian x) (hψ.past_gradient x)
  have h1 : ∀ x, 0 < 1 + ε * coform g x (d ψ x) (d ψ x) := fun x => by linarith [hε1 x]
  have hL := hg.lorentzian w
  set G := narrow g ψ (ε / 2) w with hG_def
  have hGL : IsLorentzian G :=
    isLorentzian_narrow hL (hs w) (by nlinarith [hε1 w, hs w])
  -- the apex `y' = w + η N(w)`
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ChronLT g Y (w + t • N w) y ∧
      dist (w + t • N w) w < r / 4 ∧ ψ (w + t • N w) < τ + δ := by
    have hc : Continuous fun t : ℝ => w + t • N w := by fun_prop
    have ht : Tendsto (fun t : ℝ => w + t • N w) (𝓝 0) (𝓝 w) := by
      simpa using hc.tendsto 0
    have hw : ∀ᶠ q in 𝓝 w, ChronLT g Y q y ∧ dist q w < r / 4 ∧ ψ q < τ + δ := by
      filter_upwards [(isOpen_chronPast hg y).mem_nhds (mem_chronPast.2 hwy),
        ball_mem_nhds w (by positivity : (0 : ℝ) < r / 4),
        hψ.smooth.continuous.continuousAt.eventually (gt_mem_nhds hwδ)] with q h1 h2 h3
      exact ⟨(mem_chronPast.1 h1), h2, h3⟩
    exact ht.eventually hw
  obtain ⟨ρ, hρ, hρP⟩ := Metric.eventually_nhds_iff.1 hev
  set η := ρ / 2
  have hη : 0 < η := by positivity
  obtain ⟨hy'y, hy'w, hy'ψ⟩ := hρP (y := η) (by
    rw [Real.dist_eq, sub_zero, abs_of_pos hη]
    exact half_lt_self hρ)
  set y' := w + η • N w with hy'_def
  have hy'r : dist y' w < r := by linarith
  set Q := frozenQ G y' with hQ_def
  -- the open set of the lens
  set U := {p | dist p w < r ∧ 0 < Q p ∧ 0 < fderiv ℝ ψ w (y' - p)} with hU_def
  have hcond : ∀ p, 0 < Q p → y' - p ≠ 0 ∧ form G (y' - p) (y' - p) ≤ 0 := by
    intro p hp
    have hneg : form G (y' - p) (y' - p) < 0 := by simp only [Q, frozenQ_def] at hp; linarith
    refine ⟨fun h0 => ?_, hneg.le⟩
    rw [h0] at hneg
    simp [form_def] at hneg
  have hchron : ∀ p ∈ U, ChronLT g Y p y := by
    intro p hp
    obtain ⟨hv0, hvv⟩ := hcond p hp.2.1
    have := chronLT_of_isPathOn (hfr.isPathOn hg hψ hp.1 hy'r hv0 hvv hp.2.2.le)
    simp only [zero_smul, add_zero, one_smul, add_sub_cancel] at this
    exact this.trans hy'y
  have hheight : ∀ p ∈ U, κ * ‖y' - p‖ ≤ ψ y' - ψ p := by
    intro p hp
    obtain ⟨hv0, hvv⟩ := hcond p hp.2.1
    have := ((hfr.isPathOn hg hψ hp.1 hy'r hv0 hvv hp.2.2.le).mono
      fun _ _ h => h.isFutureCausal).norm_sub_le hψ1 hκ (fun x _ v hv => hsteep x v hv)
      (K := univ) fun _ _ => mem_univ _
    simpa using this
  -- `Q(w) > 0`
  have hQw : 0 < Q w := by
    have : form G (N w) (N w) < 0 := by
      rw [hG_def, form_narrow_neg_grad hL]
      exact mul_neg_of_neg_of_pos (hs w) (by nlinarith [hε1 w, hs w])
    simp only [Q, frozenQ_def, hy'_def, add_sub_cancel_left, form_smul_left, form_smul_right]
    nlinarith [mul_pos hη hη]
  have hwU : w ∈ U := by
    refine ⟨by simpa using hr, hQw, ?_⟩
    simp only [hy'_def, add_sub_cancel_left, map_smul, smul_eq_mul, N]
    rw [fderiv_neg_grad_self hL]
    exact mul_pos hη (neg_pos.2 (hs w))
  -- the setting
  set c := Q w / 2
  have hNc : Continuous N := (hg.continuous_grad hψ1).neg
  have hset : EnergySetting U (narrow g ψ ε) (-N) (fun x => -ψ x) Q (-(τ - δ)) c := by
    refine ⟨?_, fun i j => (contDiff_narrow hg.smooth hψ.smooth ε i j).contDiffOn,
      fun x _ => isLorentzian_narrow (hg.lorentzian x) (hs x) (h1 x), hNc.neg.continuousOn,
      fun x _ => ?_, hψ.smooth.neg.contDiffOn, (contDiff_frozenQ G y').contDiffOn,
      fun x _ => ?_, fun x hx => ?_, ?_⟩
    · exact (isOpen_lt (continuous_id.dist continuous_const) continuous_const).inter
        ((isOpen_lt continuous_const (contDiff_frozenQ G y').continuous).inter
          (isOpen_lt continuous_const
            ((fderiv ℝ ψ w).continuous.comp (continuous_const.sub continuous_id))))
    · rw [Pi.neg_apply, form_neg_left, form_neg_right, neg_neg]
      exact (hψ.isTimeOrientation_narrow hg h1).timelike x
    · rw [grad_neg, neg_neg, isFutureTimelike_neg_iff]
      exact isFutureTimelike_narrow (hg.lorentzian x) (hs x) (h1 x)
    · obtain ⟨hv0, hvv⟩ := hcond x hx.2.1
      obtain ⟨F1, F2, -, -⟩ := hfr x hx.1 _ hv0 hvv hx.2.2.le
      have hLx := isLorentzian_narrow (ε := ε) (hg.lorentzian x) (hs x) (h1 x)
      refine ⟨?_, ?_⟩
      · rw [form_neg_grad hLx, d_frozenQ hGL.symm, coform_eq_bil]
        rw [coform_eq_bil] at F1
        simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
        nlinarith
      · rw [Pi.neg_apply, form_neg_right, form_neg_grad_left hLx, neg_neg,
          fderiv_frozenQ_apply hGL.symm]
        nlinarith
    · have hsub : lens U (fun x => -ψ x) Q (-(τ - δ)) c =
          ((closedBall y' (r / 4) ∩ {p | τ - δ ≤ ψ p}) ∩ {p | c ≤ Q p}) ∩
            {p | 0 ≤ fderiv ℝ ψ w (y' - p)} := by
        ext p
        constructor
        · intro hp
          obtain ⟨hpU, hpψ, hpQ⟩ := mem_lens.1 hp
          refine ⟨⟨⟨?_, by simp only [mem_ofPred_eq]; linarith⟩, hpQ⟩, hpU.2.2.le⟩
          have := hheight p hpU
          rw [mem_closedBall, dist_eq_norm, norm_sub_rev]
          have h8 : κ * ‖y' - p‖ ≤ κ * (r / 4) := by
            simp only [neg_le_neg_iff] at hpψ
            nlinarith
          exact le_of_mul_le_mul_left h8 hκ
        · rintro ⟨⟨⟨hpB, hpψ⟩, hpQ⟩, hpf⟩
          have hQp : 0 < Q p := by
            have h : Q w / 2 ≤ Q p := hpQ
            linarith
          obtain ⟨hv0, hvv⟩ := hcond p hQp
          have hpw : dist p w < r := by
            have := dist_triangle p y' w
            rw [mem_closedBall] at hpB
            linarith
          refine mem_lens.2 ⟨⟨hpw, hQp, (frozen_pointwise hg hψ hε hε1 hv0 hvv hpf).2.2.2⟩,
            by simp only [mem_ofPred_eq] at hpψ ⊢; linarith, hpQ⟩
      rw [hsub]
      refine (isCompact_closedBall y' (r / 4)).inter_right ?_ |>.inter_right ?_ |>.inter_right ?_
      · exact isClosed_le continuous_const hψ.smooth.continuous
      · exact isClosed_le continuous_const (contDiff_frozenQ G y').continuous
      · exact isClosed_le continuous_const
          ((fderiv ℝ ψ w).continuous.comp (continuous_const.sub continuous_id))
  -- the lens lemma
  have hO' : IsOpen {p | ChronLT g Y p y ∧ ψ p < τ} := by
    have e : {p | ChronLT g Y p y ∧ ψ p < τ} = chronPast g Y y ∩ {p | ψ p < τ} := by
      ext p
      simp only [mem_ofPred_eq, mem_inter_iff, mem_chronPast]
    rw [e]
    exact (isOpen_chronPast hg y).inter (isOpen_lt hψ.smooth.continuous continuous_const)
  refine hset.eq_zero_of_box isOpen_univ (subset_univ _) hV.contDiffOn
    (fun x hx => hbox x (hchron x (mem_lens.1 hx).1)) (fun x hx hxτ => ?_) w hwU
    (show -ψ w < -(τ - δ) by linarith) (half_lt_self hQw)
  have hxτ' : ψ x < τ := by simp only [neg_inj] at hxτ; linarith
  have hev0 : V =ᶠ[𝓝 x] fun _ => 0 :=
    eventually_of_mem (hO'.mem_nhds ⟨hchron x (mem_lens.1 hx).1, hxτ'⟩) fun p hp => hO p hp.1 hp.2
  exact ⟨hev0.eq_of_nhds, by rw [hev0.fderiv_eq]; simp⟩

/-- A point is a limit of its chronological past. -/
theorem mem_closure_chronPast (hg : IsSpacetime g Y) (y : E n) :
    y ∈ closure (chronPast g Y y) := by
  obtain ⟨p, hp⟩ := exists_chronLT_left hg y
  obtain ⟨γ, hγ, -, hγ1⟩ := chronLT_iff.1 hp
  have hle : 𝓝[<] (1 : ℝ) ≤ 𝓝[Icc 0 1] 1 :=
    nhdsWithin_le_of_mem (mem_of_superset (Ioo_mem_nhdsLT zero_lt_one) Ioo_subset_Icc_self)
  have ht : Tendsto γ (𝓝[<] 1) (𝓝 y) :=
    hγ1 ▸ ((hγ.continuousOn 1 ⟨zero_le_one, le_rfl⟩).tendsto.mono_left hle)
  refine mem_closure_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with t htI
  have := chronLT_of_isPathOn (hγ.restrict htI.1.le htI.2 le_rfl)
  rw [hγ1] at this
  exact mem_chronPast.2 this

/-- **Support for narrowed metrics.** For a standard time `ψ` there is `ε₀ > 0` such that for
`0 < ε ≤ ε₀`, every `C²` function `V` that solves `□_{g_ε} V = 0` off `J⁺(K)` and vanishes on
`{ψ < t₀}` is supported in `J⁺(K)`. -/
theorem support_subset_of_narrow (hg : IsSpacetime g Y) (hψ : IsStandardTime g Y ψ) :
    ∃ ε₀ > 0, ∀ ε ∈ Ioc 0 ε₀, ∀ {K : Set (E n)} {V : E n → ℝ} {t₀ : ℝ}, ContDiff ℝ 2 V →
      (∀ x ∉ causalFutureSet g Y K, box (narrow g ψ ε) V x = 0) →
      (∀ x, ψ x < t₀ → V x = 0) → Function.support V ⊆ causalFutureSet g Y K := by
  obtain ⟨ε₀, hε₀, hε1⟩ := hψ.exists_narrow_le hg
  obtain ⟨κ, hκ, hsteep⟩ := hψ.exists_steep hg
  refine ⟨ε₀, hε₀, fun ε hε K V t₀ hV hbox hV0 y hy => ?_⟩
  by_contra hyK
  apply hy
  have hε1' := hε1 ε ⟨hε.1.le, hε.2⟩
  have hψ1 : ContDiff ℝ 1 ψ := hψ.smooth.of_le (by simp)
  have hboxI : ∀ p, ChronLT g Y p y → box (narrow g ψ ε) V p = 0 := fun p hp =>
    hbox p fun hpK => hyK (by
      obtain ⟨k, hk, hkp⟩ := mem_causalFutureSet.1 hpK
      exact mem_causalFutureSet.2
        ⟨k, hk, mem_causalFuture.2 (CausalLE.trans (mem_causalFuture.1 hkp) hp.causalLE)⟩)
  set R := (ψ y - t₀) / κ
  have hbd : ∀ w, ChronLT g Y w y → t₀ ≤ ψ w → w ∈ closedBall y R := by
    intro w hw hwt
    obtain ⟨γ, hγ, rfl, rfl⟩ := chronLT_iff.1 hw
    have := (hγ.mono fun _ _ h => h.isFutureCausal).norm_sub_le hψ1 hκ
      (fun x _ v hv => hsteep x v hv) (K := univ) fun _ _ => mem_univ _
    rw [mem_closedBall, dist_eq_norm, norm_sub_rev, le_div_iff₀ hκ]
    linarith
  obtain ⟨r, hr, hfr⟩ := exists_frozen_radius hg hψ hε.1 hε1' (isCompact_closedBall y R)
  set δ := κ * r / 8 with hδ_def
  have hδ : 0 < δ := by positivity
  have hstep : ∀ k : ℕ, ∀ p, ChronLT g Y p y → ψ p < t₀ + k * δ → V p = 0 := by
    intro k
    induction k with
    | zero => exact fun p _ hp => hV0 p (by simpa using hp)
    | succ k ih =>
      intro w hw hwk
      by_cases hlt : ψ w < t₀ + k * δ
      · exact ih w hw hlt
      · push Not at hlt
        have hk0 : (0 : ℝ) ≤ k * δ := by positivity
        exact eq_zero_of_frozenLens hg hψ hε.1 hε1' hκ hsteep hr
          (hfr w (hbd w hw (by linarith))) hV hboxI ih hw hlt
          (by push_cast at hwk; linarith [hδ_def])
  have hI : ∀ p ∈ chronPast g Y y, V p = 0 := fun p hp => by
    obtain ⟨k, hk⟩ := exists_nat_gt ((ψ p - t₀) / δ)
    rw [div_lt_iff₀ hδ] at hk
    exact hstep k p (mem_chronPast.1 hp) (by linarith)
  exact closure_minimal hI (isClosed_eq hV.continuous continuous_const)
    (mem_closure_chronPast hg y)

end

end LorentzianCalderon
