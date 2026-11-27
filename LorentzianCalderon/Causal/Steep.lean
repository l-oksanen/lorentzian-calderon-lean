module

public import LorentzianCalderon.Causal.StandardTime
public import LorentzianCalderon.Causal.Imprisonment
public import LorentzianCalderon.Geometry.CausalClosed

public section

/-!
# Standard time functions are steep and Cauchy

A standard time function `ψ` grows at least like `κ ‖v‖` in all future causal directions `v`,
globally (`IsStandardTime.exists_steep`): on a compact set by `exists_pos_mul_norm_le_fderiv`, and
outside it `dψ = σ dx⁰` while future causal vectors of the Minkowski exterior satisfy
`‖v‖ ≤ √2 |v⁰|`. So `ψ → ∞` along future-inextendible causal curves (a bounded `ψ` would make
the curve Cauchy), and with the intermediate value theorem every level set of `ψ` is a Cauchy
hypersurface (`IsStandardTime.isCauchyTemporal`). Hence `J⁺(K) ∩ {ψ ≤ c}` is bounded, so compact,
and `ψ` strictly increases along causal relations between distinct points.
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Topology
open Set Filter

variable {n : ℕ} {g : MatrixField n} {Y : E n → E n} {ψ : E n → ℝ}

/-- A standard time function is steep: `κ ‖v‖ ≤ dψ(v)` for all future causal `v`. -/
theorem IsStandardTime.exists_steep (hg : IsSpacetime g Y) (hψ : IsStandardTime g Y ψ) :
    ∃ κ > 0, ∀ x v, IsFutureCausal g Y x v → κ * ‖v‖ ≤ fderiv ℝ ψ x v := by
  obtain ⟨C, σ', A, hC, hσ', hψC⟩ := hψ.exterior
  obtain ⟨T, σ, hσ, hext⟩ := hg.exterior
  have hY := hg.globallyHyperbolic.timeOrientation
  have hK := hC.union (isCompact_M0 (n := n) T)
  obtain ⟨κ, hκ, hψK⟩ := exists_pos_mul_norm_le_fderiv hg (hψ.smooth.of_le (by simp))
    hψ.past_gradient hK
  refine ⟨min κ (1 / 2), lt_min hκ (by norm_num), fun x v hv => ?_⟩
  by_cases hx : x ∈ C ∪ M0 n T
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg v)).trans (hψK x hx v hv)
  · rw [mem_union, not_or] at hx
    have hpos := fderiv_pos_of_isFutureCausal (hg.lorentzian x) (hY.timelike x)
      (hψ.past_gradient x) hv
    have hloc : ψ =ᶠ[𝓝 x] fun y => σ' * y 0 + A :=
      Filter.eventually_of_mem (hC.isClosed.isOpen_compl.mem_nhds hx.1) fun y hy => hψC y hy
    have hd : fderiv ℝ ψ x v = σ' * v 0 := by
      rw [hloc.fderiv_eq, (((hasFDerivAt_coord x).const_mul σ').add_const A).fderiv]
      simp
    have h2 := (isFutureCausal_exterior (hg.lorentzian x) (hY.timelike x) hσ (hext x hx.2) hv).2
    have hσ2 : (σ' * v 0) ^ 2 = v 0 ^ 2 := by
      rcases hσ' with rfl | rfl <;> ring
    rw [hd] at hpos ⊢
    have hsq : (1 / 2 * ‖v‖) ^ 2 ≤ (σ' * v 0) ^ 2 := by nlinarith [norm_nonneg v]
    exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg v)).trans
      (le_of_pow_le_pow_left₀ two_ne_zero hpos.le hsq)

/-- Along a future-inextendible causal curve, a steep function tends to `∞`. -/
theorem tendsto_atTop_of_steep (hψs : ContDiff ℝ 1 ψ) {κ : ℝ} (hκ : 0 < κ)
    (hψ : ∀ x v, IsFutureCausal g Y x v → κ * ‖v‖ ≤ fderiv ℝ ψ x v) {c : ℝ → E n}
    (hc : IsInextendibleRay (IsFutureCausal g Y) c) : Tendsto (fun t => ψ (c t)) atTop atTop := by
  have hmono : ∀ s t, 0 ≤ s → s ≤ t → ψ (c s) ≤ ψ (c t) := by
    intro s t hs hst
    rcases hst.lt_or_eq with hst | rfl
    · have := ((hc.path t (hs.trans_lt hst)).restrict hs hst le_rfl).norm_sub_le
        (K := univ) hψs hκ (fun x _ => hψ x) fun _ _ => mem_univ _
      nlinarith [norm_nonneg (c t - c s)]
    · exact le_rfl
  rw [tendsto_atTop_atTop]
  intro M
  by_contra h
  push Not at h
  refine hc.not_forall_le (K := univ) hψs hκ (fun x _ => hψ x) (fun _ _ => mem_univ _) M
    fun t ht => ?_
  obtain ⟨a, hta, ha⟩ := h t
  exact (hmono t a ht hta).trans ha.le

/-- A standard time function is a Cauchy temporal function. -/
theorem IsStandardTime.isCauchyTemporal (hg : IsSpacetime g Y) (hψ : IsStandardTime g Y ψ) :
    IsCauchyTemporal g Y ψ := by
  obtain ⟨κ, hκ, hsteep⟩ := hψ.exists_steep hg
  have hψ1 : ContDiff ℝ 1 ψ := hψ.smooth.of_le (by simp)
  refine ⟨hψ.smooth, hψ.past_gradient, fun v => isCauchyHypersurface_iff.2 fun c hc => ?_⟩
  set f := fun t => ψ (c t)
  have hcaus : ∀ x w, IsFutureTimelike g Y x w → IsFutureCausal g Y x w :=
    fun _ _ h => h.isFutureCausal
  have hmono : StrictMono f := fun a b hab =>
    lt_of_isPathOn hg (hψ1.differentiable one_ne_zero) hψ.past_gradient
      ((hc.path a b hab).mono hcaus)
  have hcont : Continuous f := by
    refine hψ.smooth.continuous.comp (continuous_iff_continuousAt.2 fun t => ?_)
    exact ((hc.path (t - 1) (t + 1) (by linarith)).continuousOn).continuousAt
      (Icc_mem_nhds (by linarith) (by linarith))
  have htop : Tendsto f atTop atTop :=
    tendsto_atTop_of_steep hψ1 hκ hsteep
      ⟨fun a ha => (hc.path 0 a ha).mono hcaus, hc.no_limit_atTop⟩
  have hray : IsInextendibleRay (IsFutureCausal g (-Y)) fun t => c (-t) := by
    refine ⟨fun a ha => ?_, fun x hx => hc.no_limit_atBot x ?_⟩
    · have h := (show IsPathOn (IsFutureTimelike g Y) (0 - a) (0 - 0) c by
        simpa using hc.path (-a) 0 (by linarith)).comp_reflect (Q := IsFutureCausal g (-Y))
        fun x w hw => isFutureCausal_neg_iff.2 (by simpa using hw.isFutureCausal)
      exact h.congr fun t _ => by simp
    · simpa [Function.comp_def] using hx.comp tendsto_neg_atBot_atTop
  have hsteep' : ∀ x w, IsFutureCausal g (-Y) x w → κ * ‖w‖ ≤ fderiv ℝ (fun y => -ψ y) x w := by
    intro x w hw
    have := hsteep x (-w) (isFutureCausal_neg_iff.1 hw)
    rw [norm_neg, map_neg] at this
    rw [fderiv_fun_neg]
    simpa using this
  have hbot' := tendsto_atTop_of_steep (hψ1.neg) hκ hsteep' hray
  have hbot : Tendsto f atBot atBot := by
    have := (tendsto_neg_atTop_atBot.comp hbot').comp tendsto_neg_atBot_atTop
    simpa [Function.comp_def, f] using this
  obtain ⟨t, ht⟩ := hcont.surjective htop hbot v
  exact ⟨t, ht, fun s hs => hmono.injective (hs.trans ht.symm)⟩

/-- A standard time function strictly increases along causal relations between distinct
points. -/
theorem exists_lt_of_causalLE (hg : IsSpacetime g Y) :
    ∃ ψ : E n → ℝ, ∀ p q, CausalLE g Y p q → p ≠ q → ψ p < ψ q := by
  obtain ⟨ψ, hψ⟩ := exists_standardTime hg
  obtain ⟨κ, hκ, hsteep⟩ := hψ.exists_steep hg
  have hψ1 : ContDiff ℝ 1 ψ := hψ.smooth.of_le (by simp)
  refine ⟨ψ, fun p q hpq hne => ?_⟩
  obtain ⟨γ, hγ, rfl, rfl⟩ := CausalLE.exists_isPathOn hpq hne zero_lt_one
  have := hγ.norm_sub_le (K := univ) hψ1 hκ (fun x _ => hsteep x) fun _ _ => mem_univ _
  have hpos : 0 < ‖γ 1 - γ 0‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hne))
  nlinarith

/-- For a standard time function `ψ` and compact `K`, `J⁺(K) ∩ {ψ ≤ c}` is compact: it is
closed, and within distance `(c - min_K ψ) / κ` of `K` for the steepness constant `κ`. -/
theorem IsStandardTime.isCompact_causalFutureSet_inter_le (hg : IsSpacetime g Y)
    {ψ : E n → ℝ} (hψ : IsStandardTime g Y ψ) {K : Set (E n)} (hK : IsCompact K) (c : ℝ) :
    IsCompact (causalFutureSet g Y K ∩ {x | ψ x ≤ c}) := by
  obtain ⟨κ, hκ, hsteep⟩ := hψ.exists_steep hg
  have hψ1 : ContDiff ℝ 1 ψ := hψ.smooth.of_le (by simp)
  obtain ⟨m, hm⟩ := hK.bddBelow_image hψ.smooth.continuous.continuousOn
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  refine Metric.isCompact_of_isClosed_isBounded ((isClosed_causalFutureSet hg hK).inter
    (isClosed_le hψ.smooth.continuous continuous_const))
    ((Metric.isBounded_closedBall (x := 0) (r := R + (c - m) / κ)).subset ?_)
  rintro x ⟨hx, hxc⟩
  obtain ⟨p, hp, hpx⟩ := mem_causalFutureSet.1 hx
  have hmp : m ≤ ψ p := hm ⟨p, hp, rfl⟩
  have hdist : κ * ‖x - p‖ ≤ ψ x - ψ p := by
    by_cases hpx' : p = x
    · subst hpx'
      simp
    · obtain ⟨γ, hγ, rfl, rfl⟩ := CausalLE.exists_isPathOn (mem_causalFuture.1 hpx) hpx' zero_lt_one
      exact hγ.norm_sub_le (K := univ) hψ1 hκ (fun x _ => hsteep x) fun _ _ => mem_univ _
  have hpR : ‖p‖ ≤ R := by simpa using hR hp
  have hxp : ‖x - p‖ ≤ (c - m) / κ := by
    rw [le_div_iff₀ hκ]
    linarith [show ψ x ≤ c from hxc]
  rw [Metric.mem_closedBall, dist_zero_right]
  linarith [norm_le_norm_add_norm_sub' x p]

end

end LorentzianCalderon
