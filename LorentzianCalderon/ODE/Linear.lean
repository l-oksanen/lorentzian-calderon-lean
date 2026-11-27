module

public import LorentzianCalderon.ODE.Smooth

public section

/-!
# Global solutions of linear equations with parameters

For `ż = M(l, t) z + f(l, t)` in a finite-dimensional space `W`, with `M`, `f` smooth in the
parameter `l` and the time `t`, there is a solution defined for all times, smooth in `(l, t)`
jointly, and vanishing for `t ≤ t₀` when `f` does (`exists_linear_ode`). A second order equation
`ẍ = M(l, t)(x, ẋ) + f` is the case `W = E × E`.

The equation is made autonomous with the state `(z, t, l)` (`linField`), so that the flow of
`ODE/Basic.lean` and its smoothness (`ODE/Smooth.lean`) apply. The flow is global: Picard–Lindelöf
gives an existence time that depends only on a bound of `M` on a compact time interval, not on
the initial point, since the field grows linearly (`linField_local`).
-/

namespace LorentzianCalderon.ODEFlow

noncomputable section
open Set Function Metric
open scoped ContDiff NNReal Topology

section General

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {F : V → V}

/-- A flow defined for all times is differentiable in time, with the field as derivative. -/
theorem hasDerivAt_flow_of_lipschitz (hF : LocallyLipschitzOn univ F) (hdom : ∀ p, p ∈ dom F univ) (s : ℝ)
    (w : V) : HasDerivAt (fun r => flow F univ (r, w)) (F (flow F univ (s, w))) s := by
  set w' := flow F univ (s, w)
  have h1 := (isSol_flow hF (hdom (1, w'))).deriv 0 left_mem_uIcc
  have h2 := (isSol_flow hF (hdom (-1, w'))).deriv 0 left_mem_uIcc
  simp only [flow_zero hF (mem_univ w')] at h1 h2
  have hn : uIcc (0 : ℝ) 1 ∪ uIcc 0 (-1) ∈ 𝓝 (0 : ℝ) := by
    refine Filter.mem_of_superset (Icc_mem_nhds (show (-1 : ℝ) < 0 by norm_num) one_pos) ?_
    intro x hx
    rcases le_total 0 x with h | h
    · exact Or.inl (by rw [uIcc_of_le zero_le_one]; exact ⟨h, hx.2⟩)
    · exact Or.inr (by rw [uIcc_of_ge (by norm_num)]; exact ⟨hx.1, h⟩)
  have h3 := (show HasDerivAt (fun r => flow F univ (r, w')) (F w') (s - s) by
    rw [sub_self]; exact (h1.union h2).hasDerivAt hn).comp_sub_const s s
  refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
  simp only
  have := (flow_add hF (hdom (s, w)) (hdom (u - s, w'))).2
  rwa [add_sub_cancel] at this

end General

variable {W Λ : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup Λ] [NormedSpace ℝ Λ]
  {M : Λ → ℝ → W →L[ℝ] W} {f : Λ → ℝ → W}

/-- The autonomous field of `ż = M(l, t) z + f(l, t)` on the states `(z, t, l)`. -/
def linField (M : Λ → ℝ → W →L[ℝ] W) (f : Λ → ℝ → W) (q : W × ℝ × Λ) : W × ℝ × Λ :=
  (M q.2.2 q.2.1 q.1 + f q.2.2 q.2.1, 1, 0)

theorem contDiff_linField (hM : ContDiff ℝ ∞ fun q : Λ × ℝ => M q.1 q.2)
    (hf : ContDiff ℝ ∞ fun q : Λ × ℝ => f q.1 q.2) : ContDiff ℝ ∞ (linField M f) := by
  have hπ : ContDiff ℝ ∞ fun q : W × ℝ × Λ => (q.2.2, q.2.1) := by fun_prop
  exact (((hM.comp hπ).clm_apply contDiff_fst).add (hf.comp hπ)).prodMk contDiff_const

/-- Existence for a time `h` from any state `(z, τ, l)`, where `h` depends only on bounds of `M`
and `f` near `τ`: the field is affine in `z`, so the radius of the Picard–Lindelöf ball can grow
with `‖z‖`. -/
theorem linField_local [FiniteDimensional ℝ W] (hG : LocallyLipschitzOn univ (linField M f))
    (hM : Continuous fun q : Λ × ℝ => M q.1 q.2) (hf : Continuous fun q : Λ × ℝ => f q.1 q.2)
    (l : Λ) {T₀ T₁ K B h : ℝ} (hK : ∀ t ∈ Icc T₀ T₁, ‖M l t‖ ≤ K)
    (hB : ∀ t ∈ Icc T₀ T₁, ‖f l t‖ ≤ B) (hh : 0 < h) (hKh : K * h ≤ 1 / 2) (z : W) {τ : ℝ}
    (hτ : Icc (τ - h) (τ + h) ⊆ Icc T₀ T₁) (r : ℝ) (hr : r ∈ Icc (-h) h) :
    (r, (z, τ, l)) ∈ dom (linField M f) univ ∧
      (flow (linField M f) univ (r, (z, τ, l))).2 = (τ + r, l) := by
  have hτ' : τ ∈ Icc T₀ T₁ := hτ ⟨by linarith, by linarith⟩
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK τ hτ')
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB τ hτ')
  set a : ℝ := 2 * (K * ‖z‖ + B) * h
  have ha : 0 ≤ a := by positivity
  set L : ℝ := K * (‖z‖ + a) + B
  have hL : 0 ≤ L := by positivity
  have hpl : IsPicardLindelof (fun t x => M l t x + f l t)
      (⟨τ, by constructor <;> linarith⟩ : Icc (τ - h) (τ + h)) z ⟨a, ha⟩ 0 ⟨L, hL⟩
      ⟨K, hK0⟩ := by
    refine ⟨fun t ht => LipschitzOnWith.of_dist_le_mul fun x _ y _ => ?_, fun x _ => ?_,
      fun t ht x hx => ?_, ?_⟩
    · rw [dist_eq_norm, dist_eq_norm, add_sub_add_right_eq_sub, ← map_sub]
      exact ((M l t).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hK t (hτ ht))
        (norm_nonneg _))
    · exact ((hM.comp (continuous_const.prodMk continuous_id)).clm_apply continuous_const
        |>.add (hf.comp (continuous_const.prodMk continuous_id))).continuousOn
    · have hx' : ‖x‖ ≤ ‖z‖ + a := by
        have := norm_le_norm_add_norm_sub' x z
        rw [mem_closedBall, dist_eq_norm] at hx
        change ‖x - z‖ ≤ a at hx
        linarith
      calc ‖M l t x + f l t‖ ≤ ‖M l t‖ * ‖x‖ + ‖f l t‖ :=
            (norm_add_le _ _).trans (by gcongr; exact (M l t).le_opNorm x)
        _ ≤ K * (‖z‖ + a) + B := add_le_add (mul_le_mul (hK t (hτ ht)) hx' (norm_nonneg _) hK0)
            (hB t (hτ ht))
    · change L * max (τ + h - τ) (τ - (τ - h)) ≤ a - 0
      rw [add_sub_cancel_left, sub_sub_cancel, max_self, sub_zero]
      simp only [L, a]
      nlinarith
  obtain ⟨α, hα0, hα⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  simp only at hα0
  set c : ℝ → W × ℝ × Λ := fun s => (α (τ + s), τ + s, l)
  have hc : IsSol (linField M f) univ c (Icc (-h) h) := by
    refine ⟨ordConnected_Icc, fun _ _ => mem_univ _, fun s hs => ?_⟩
    have hmaps : MapsTo (fun s => τ + s) (Icc (-h) h) (Icc (τ - h) (τ + h)) :=
      fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hs' := hmaps hs
    have h1 := (hα _ hs').scomp s ((hasDerivAt_id s).const_add τ).hasDerivWithinAt hmaps
    rw [one_smul] at h1
    exact h1.prodMk ((((hasDerivAt_id s).const_add τ).hasDerivWithinAt).prodMk
      (hasDerivWithinAt_const _ _ _))
  have h0 : (0 : ℝ) ∈ Icc (-h) h := ⟨by linarith, hh.le⟩
  have hc0 : c 0 = (z, τ, l) := by simp [c, hα0]
  rw [← hc0]
  exact ⟨mem_dom_of_isSol hc h0 hr, by rw [flow_eq hG hc h0 hr]⟩

/-- The flow of `linField` is defined for all times, and moves the time component at unit
speed. -/
theorem mem_dom_linField [FiniteDimensional ℝ W] (hM : ContDiff ℝ ∞ fun q : Λ × ℝ => M q.1 q.2)
    (hf : ContDiff ℝ ∞ fun q : Λ × ℝ => f q.1 q.2) (s : ℝ) (w : W × ℝ × Λ) :
    (s, w) ∈ dom (linField M f) univ ∧
      (flow (linField M f) univ (s, w)).2 = (w.2.1 + s, w.2.2) := by
  have hG : LocallyLipschitzOn univ (linField M f) :=
    locallyLipschitzOn_of_contDiffOn isOpen_univ
      ((contDiff_linField hM hf).of_le (by simp)).contDiffOn
  obtain ⟨z, τ, l⟩ := w
  simp only
  set T := |s|
  have hcM : Continuous fun t => M l t := hM.continuous.comp (continuous_const.prodMk
    continuous_id)
  have hcf : Continuous fun t => f l t := hf.continuous.comp (continuous_const.prodMk
    continuous_id)
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := τ - T - 1) (b := τ + T + 1)).exists_bound_of_continuousOn
    hcM.continuousOn
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := τ - T - 1) (b := τ + T + 1)).exists_bound_of_continuousOn
    hcf.continuousOn
  set h : ℝ := 1 / (2 * (|K| + 1))
  have hh : 0 < h := by positivity
  have hh1 : h ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [abs_nonneg K]
  have hKh : K * h ≤ 1 / 2 := by
    have : K * h = K / (2 * (|K| + 1)) := by simp only [h]; ring
    rw [this, div_le_iff₀ (by positivity)]
    linarith [le_abs_self K]
  have hstep : ∀ k : ℕ, ∀ r, |r| ≤ k * h → |r| ≤ T →
      (r, (z, τ, l)) ∈ dom (linField M f) univ ∧
        (flow (linField M f) univ (r, (z, τ, l))).2 = (τ + r, l) := by
    intro k
    induction k with
    | zero =>
      intro r hr _
      have hr0 : r = 0 := abs_nonpos_iff.1 (by simpa using hr)
      subst hr0
      exact ⟨mem_dom_zero (mem_univ _), by rw [flow_zero hG (mem_univ _)]; simp⟩
    | succ k ih =>
      intro r hr hrT
      push_cast at hr
      obtain ⟨r₀, r₁, rfl, hr₁, hr₀, hr₀'⟩ : ∃ r₀ r₁, r = r₀ + r₁ ∧ r₁ ∈ Icc (-h) h ∧
          |r₀| ≤ k * h ∧ |r₀| ≤ |r| := by
        rcases abs_le.1 hr with ⟨hr1, hr2⟩
        by_cases h1 : h ≤ r
        · refine ⟨r - h, h, by ring, ⟨by linarith, le_rfl⟩, ?_, ?_⟩ <;>
            rw [abs_of_nonneg (by linarith : 0 ≤ r - h)]
          · linarith
          · rw [abs_of_nonneg (by linarith : 0 ≤ r)]; linarith
        by_cases h2 : r ≤ -h
        · refine ⟨r + h, -h, by ring, ⟨le_rfl, by linarith⟩, ?_, ?_⟩ <;>
            rw [abs_of_nonpos (by linarith : r + h ≤ 0)]
          · linarith
          · rw [abs_of_nonpos (by linarith : r ≤ 0)]; linarith
        · exact ⟨0, r, by ring, ⟨by linarith, by linarith⟩, by simp; positivity,
            by simp⟩
      obtain ⟨hd₀, hf₀⟩ := ih r₀ hr₀ (hr₀'.trans hrT)
      have hw : flow (linField M f) univ (r₀, (z, τ, l)) =
          ((flow (linField M f) univ (r₀, (z, τ, l))).1, τ + r₀, l) := Prod.ext rfl hf₀
      have hT₀ := (abs_le.1 (hr₀'.trans hrT))
      obtain ⟨hd₁, hf₁⟩ := linField_local hG hM.continuous hf.continuous l (T₀ := τ - T - 1) (T₁ := τ + T + 1)
        (fun t ht => hK t ht) (fun t ht => hB t ht) hh hKh
        (flow (linField M f) univ (r₀, (z, τ, l))).1 (τ := τ + r₀)
        (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩) r₁ hr₁
      rw [← hw] at hd₁ hf₁
      obtain ⟨hd, hfl⟩ := flow_add hG hd₀ hd₁
      exact ⟨hd, by rw [hfl, hf₁, add_assoc]⟩
  obtain ⟨k, hk⟩ := exists_nat_ge (T / h)
  exact hstep k s (by rwa [div_le_iff₀ hh] at hk) le_rfl

/-- **Global existence and smooth dependence for linear equations with parameters**: the
equation `ż = M(l, t) z + f(l, t)`, with `M`, `f` smooth in `(l, t)` and `f = 0` for `t ≤ t₀`, has
a solution `z(l, t)` defined for all `(l, t)`, smooth jointly, and zero for `t ≤ t₀`. -/
theorem exists_linear_ode [FiniteDimensional ℝ W] [FiniteDimensional ℝ Λ]
    (hM : ContDiff ℝ ∞ fun q : Λ × ℝ => M q.1 q.2)
    (hf : ContDiff ℝ ∞ fun q : Λ × ℝ => f q.1 q.2) (t₀ : ℝ)
    (hf0 : ∀ l t, t ≤ t₀ → f l t = 0) :
    ∃ z : Λ → ℝ → W, ContDiff ℝ ∞ (fun q : Λ × ℝ => z q.1 q.2) ∧
      (∀ l t, t ≤ t₀ → z l t = 0) ∧ ∀ l t, HasDerivAt (z l) (M l t (z l t) + f l t) t := by
  set G := linField M f
  have hGs := contDiff_linField hM hf
  have hG : LocallyLipschitzOn univ G :=
    locallyLipschitzOn_of_contDiffOn isOpen_univ (hGs.of_le (by simp)).contDiffOn
  have hdom : ∀ p, p ∈ dom G univ := fun p => (mem_dom_linField hM hf p.1 p.2).1
  have hfl : ContDiff ℝ ∞ (flow G univ) := by
    rw [← contDiffOn_univ, show (univ : Set (ℝ × W × ℝ × Λ)) = dom G univ from
      (eq_univ_of_forall hdom).symm]
    exact (contDiffOn_flow isOpen_univ hGs.contDiffOn).2
  refine ⟨fun l t => (flow G univ (t - t₀, (0, t₀, l))).1, ?_, ?_, ?_⟩
  · exact contDiff_fst.comp (hfl.comp (by fun_prop))
  · intro l t ht
    set c : ℝ → W × ℝ × Λ := fun s => (0, t₀ + s, l)
    have hc : IsSol G univ c (Iic 0) := by
      refine ⟨ordConnected_Iic, fun _ _ => mem_univ _, fun s hs => ?_⟩
      have hval : G (c s) = (0, 1, 0) := by
        simp [G, c, linField, hf0 l (t₀ + s) (by linarith [mem_Iic.1 hs])]
      rw [hval]
      exact ((hasDerivWithinAt_const _ _ _).prodMk
        ((((hasDerivAt_id s).const_add t₀).hasDerivWithinAt).prodMk
          (hasDerivWithinAt_const _ _ _)))
    have := flow_eq hG hc (mem_Iic.2 le_rfl) (t := t - t₀) (by simpa using ht)
    simp only [c, add_zero] at this
    simp [this]
  · intro l t
    have hd := hasDerivAt_flow_of_lipschitz hG hdom (t - t₀) (0, t₀, l)
    have h2 := (mem_dom_linField hM hf (t - t₀) (0, t₀, l)).2
    simp only [add_sub_cancel] at h2
    have hw : flow G univ (t - t₀, (0, t₀, l)) =
        ((flow G univ (t - t₀, (0, t₀, l))).1, t, l) := Prod.ext rfl h2
    have h3 := (hasFDerivAt_fst.comp_hasDerivAt _ (hd.comp_sub_const t t₀))
    rw [hw] at h3
    exact h3

end

end LorentzianCalderon.ODEFlow
