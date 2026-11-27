module

public import LorentzianCalderon.ODE.Basic

public section

/-!
# Smooth dependence of flows on the initial point

The flow of a smooth field `F` on an open set `U` of a finite-dimensional space is smooth on its
open domain. The spatial derivative `D_z Fl(t, z)` solves the variational equation
`Ȧ = DF(Fl) A`, `A(0) = 1`, hence is the second component of the flow of the augmented field
`(z, A) ↦ (F z, DF(z) A)`; a Grönwall estimate shows this, and induction on the order of
differentiability, applied to the augmented field, gives smoothness (Hartman, Ordinary
differential equations, Chapter V, Theorems 3.1 and 4.1).
-/

namespace LorentzianCalderon.ODEFlow

noncomputable section
open Set Filter Metric Function Asymptotics
open scoped Topology NNReal ContDiff

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {F : V → V} {U : Set V}

/-- The field of the variational equation: `(z, A) ↦ (F z, DF(z) ∘ A)`. -/
def augField (F : V → V) (q : V × (V →L[ℝ] V)) : V × (V →L[ℝ] V) :=
  (F q.1, (fderiv ℝ F q.1).comp q.2)

/-- The augmented field of a smooth field is smooth. -/
theorem contDiffOn_augField (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) :
    ContDiffOn ℝ ∞ (augField F) (U ×ˢ univ) := by
  have hm : MapsTo (fun q : V × (V →L[ℝ] V) => q.1) (U ×ˢ univ) U := fun q hq => hq.1
  exact (hF.comp contDiffOn_fst hm).prodMk
    (((hF.fderiv_of_isOpen hU (m := ∞) (by simp)).comp contDiffOn_fst hm).clm_comp
      contDiffOn_snd)

/-- The augmented field of `-F` is minus that of `F`. -/
theorem augField_neg : augField (-F) = -augField F := by
  ext1 q
  simp only [augField, Pi.neg_apply, fderiv_neg, ContinuousLinearMap.neg_comp, Prod.neg_mk]

omit [NormedSpace ℝ V] in
/-- `-F` has the Lipschitz constants of `F`. -/
theorem lipschitzOnWith_neg {s : Set V} {K : ℝ≥0} (h : LipschitzOnWith K F s) :
    LipschitzOnWith K (-F) s := fun x hx y hy => by
  simpa [edist_neg_neg] using h hx hy

/-- The first component of the augmented flow is the flow. -/
theorem flow_augField_fst (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) {t : ℝ}
    {q : V × (V →L[ℝ] V)} (h : (t, q) ∈ dom (augField F) (U ×ˢ univ)) :
    (t, q.1) ∈ dom F U ∧ (flow (augField F) (U ×ˢ univ) (t, q)).1 = flow F U (t, q.1) := by
  have hFL := locallyLipschitzOn_of_contDiffOn hU (hF.of_le (by simp))
  have hGL := locallyLipschitzOn_of_contDiffOn (hU.prod isOpen_univ)
    ((contDiffOn_augField hU hF).of_le (by simp))
  have hc := isSol_flow hGL h
  have hq : q ∈ U ×ˢ (univ : Set (V →L[ℝ] V)) := (mem_of_mem_dom hGL h).1
  have hc1 : IsSol F U (fun s => (flow (augField F) (U ×ˢ univ) (s, q)).1) (uIcc 0 t) :=
    ⟨ordConnected_uIcc, fun s hs => (hc.mem s hs).1, fun s hs => by
      have := hasFDerivAt_fst.comp_hasDerivWithinAt (𝕜 := ℝ) s (hc.deriv s hs)
      exact this⟩
  have h0 := flow_eq hFL hc1 left_mem_uIcc right_mem_uIcc
  have hm := mem_dom_of_isSol hc1 left_mem_uIcc (right_mem_uIcc (a := (0 : ℝ)) (b := t))
  simp only [flow_zero hGL hq] at h0 hm
  exact ⟨hm, h0.symm⟩

/-- With zero initial deviation, the Grönwall bound is linear in the error rate. -/
lemma gronwallBound_zero_eq (K ε x : ℝ) : gronwallBound 0 K ε x = ε * gronwallBound 0 K 1 x := by
  unfold gronwallBound
  split_ifs <;> ring

variable [FiniteDimensional ℝ V]

/-- A uniform first-order Taylor estimate for a `C¹` field on a closed ball. -/
theorem exists_taylor (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) {w : V} {a : ℝ}
    (ha : closedBall w a ⊆ U) {η : ℝ} (hη : 0 < η) :
    ∃ β > 0, ∀ p ∈ closedBall w a, ∀ q ∈ closedBall w a, ‖q - p‖ < β →
      ‖F q - F p - fderiv ℝ F p (q - p)‖ ≤ η * ‖q - p‖ := by
  have hc : ContinuousOn (fderiv ℝ F) (closedBall w a) :=
    (hF.continuousOn_fderiv_of_isOpen hU (by simp)).mono ha
  obtain ⟨β, hβ, h⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_closedBall w a).uniformContinuousOn_of_continuous hc) η hη
  refine ⟨β, hβ, fun p hp q hq hpq => ?_⟩
  have hd : ∀ x ∈ U, HasFDerivAt F (fderiv ℝ F x) x := fun x hx =>
    ((hF.differentiableOn (by simp) x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  have hconv := (convex_closedBall w a).inter (convex_ball p β)
  refine hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le' (f' := fderiv ℝ F)
    (fun x hx => (hd x (ha hx.1)).hasFDerivWithinAt) (fun x hx => ?_)
    ⟨hp, mem_ball_self hβ⟩ ⟨hq, by rwa [mem_ball, dist_eq_norm]⟩
  rw [← dist_eq_norm]
  exact (h x hx.1 p hp (by simpa [dist_comm] using hx.2)).le

/-- The spatial derivative of the flow, for nonnegative times, is the second component of the
augmented flow. -/
theorem hasFDerivAt_flow_of_nonneg (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) {w : V}
    {a ε r : ℝ} {K : ℝ≥0} (ha : closedBall w a ⊆ U) (hK : LipschitzOnWith K F (closedBall w a))
    (hbox : ∀ z ∈ closedBall w r, ∀ t ∈ Icc (-ε) ε,
      (t, z) ∈ dom F U ∧ flow F U (t, z) ∈ closedBall w a)
    {z : V} (hz : z ∈ ball w r) {t : ℝ} (ht : t ∈ Icc 0 ε)
    (htG : (t, (z, (1 : V →L[ℝ] V))) ∈ dom (augField F) (U ×ˢ univ)) :
    HasFDerivAt (fun z' => flow F U (t, z')) (flow (augField F) (U ×ˢ univ) (t, (z, 1))).2 z := by
  set G := augField F
  set U' := U ×ˢ (univ : Set (V →L[ℝ] V))
  have hFL := locallyLipschitzOn_of_contDiffOn hU (hF.of_le (by simp))
  have hGL := locallyLipschitzOn_of_contDiffOn (hU.prod isOpen_univ)
    ((contDiffOn_augField hU hF).of_le (by simp))
  have hIcc : uIcc 0 t = Icc 0 t := uIcc_of_le ht.1
  have htε : ∀ s ∈ Icc 0 t, s ∈ Icc (-ε) ε := fun s hs =>
    ⟨by linarith [hs.1, ht.1, ht.2], hs.2.trans ht.2⟩
  have h0 : (0 : ℝ) ∈ Icc 0 t := ⟨le_rfl, ht.1⟩
  have hzU : ∀ z' ∈ closedBall w r, z' ∈ U := fun z' hz' =>
    (mem_of_mem_dom hFL (hbox z' hz' 0 (htε 0 h0)).1).1
  have hsol : ∀ z' ∈ closedBall w r, IsSol F U (fun s => flow F U (s, z')) (Icc 0 t) :=
    fun z' hz' => hIcc ▸ isSol_flow hFL (hbox z' hz' t (htε t ⟨ht.1, le_rfl⟩)).1
  have hxa : ∀ z' ∈ closedBall w r, ∀ s ∈ Icc 0 t, flow F U (s, z') ∈ closedBall w a :=
    fun z' hz' s hs => (hbox z' hz' s (htε s hs)).2
  set x : ℝ → V := fun s => flow F U (s, z)
  set Ψ : ℝ → V →L[ℝ] V := fun s => (flow G U' (s, (z, 1))).2
  have hzr : z ∈ closedBall w r := ball_subset_closedBall hz
  have hcG := isSol_flow hGL htG
  rw [hIcc] at hcG
  have hfst : ∀ s ∈ Icc 0 t, (flow G U' (s, (z, 1))).1 = x s := fun s hs =>
    (flow_augField_fst hU hF (mem_dom_of_mem_uIcc htG (hIcc ▸ hs))).2
  have hΨd : ∀ s ∈ Icc 0 t,
      HasDerivWithinAt Ψ ((fderiv ℝ F (x s)).comp (Ψ s)) (Icc 0 t) s := fun s hs => by
    have := hasFDerivAt_snd.comp_hasDerivWithinAt s (hcG.deriv s hs)
    rw [← hfst s hs]
    exact this
  have hΨ0 : Ψ 0 = 1 := by
    simp only [Ψ]
    rw [flow_zero hGL (show (z, (1 : V →L[ℝ] V)) ∈ U' from ⟨hzU z hzr, trivial⟩)]
  obtain ⟨K', hK'⟩ := (isCompact_closedBall w a).exists_bound_of_continuousOn
    ((hF.continuousOn_fderiv_of_isOpen hU (by simp)).mono ha)
  have hlip : ∀ z' ∈ closedBall w r, ∀ s ∈ Icc 0 t,
      ‖flow F U (s, z') - x s‖ ≤ ‖z' - z‖ * Real.exp (K * ε) := fun z' hz' s hs => by
    have := dist_le_of_trajectories_ODE_of_mem (v := fun _ => F) (s := fun _ => closedBall w a)
      (K := K) (fun _ _ => hK) (hsol z' hz').continuousOn
      (fun s hs => (hsol z' hz').hasDerivWithinAt_Ici subset_rfl hs)
      (fun s hs => hxa z' hz' s (Ico_subset_Icc_self hs)) (hsol z hzr).continuousOn
      (fun s hs => (hsol z hzr).hasDerivWithinAt_Ici subset_rfl hs)
      (fun s hs => hxa z hzr s (Ico_subset_Icc_self hs))
      (le_of_eq (by rw [flow_zero hFL (hzU z' hz'), flow_zero hFL (hzU z hzr), dist_eq_norm]))
      s hs
    rw [dist_eq_norm, sub_zero] at this
    exact this.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
      (mul_le_mul_of_nonneg_left (hs.2.trans ht.2) K.2)) (norm_nonneg _))
  rw [hasFDerivAt_iff_isLittleO, isLittleO_iff]
  intro c hc
  set E := Real.exp (K * ε)
  set G1 := gronwallBound 0 K' 1 t
  set η := c / (E * (|G1| + 1))
  have hE : 0 < E := Real.exp_pos _
  have hη : 0 < η := by positivity
  obtain ⟨β, hβ, hT⟩ := exists_taylor hU hF ha hη
  have hρ : 0 < min (r - dist z w) (β / E) := lt_min (sub_pos.2 hz) (by positivity)
  filter_upwards [ball_mem_nhds z hρ] with z' hz'
  rw [mem_ball] at hz'
  have hz'r : z' ∈ closedBall w r := by
    rw [mem_closedBall]
    linarith [dist_triangle z' z w, min_le_left (r - dist z w) (β / E)]
  have hsmall : ‖z' - z‖ * E < β := by
    rw [← dist_eq_norm, ← lt_div_iff₀ hE]
    exact hz'.trans_le (min_le_right _ _)
  set y : ℝ → V := fun s => flow F U (s, z')
  set e : ℝ → V := fun s => y s - x s - Ψ s (z' - z)
  have he0 : e 0 = 0 := by
    simp only [e, y, x, flow_zero hFL (hzU z' hz'r), flow_zero hFL (hzU z hzr), hΨ0]
    exact sub_eq_zero.2 rfl
  have hed : ∀ s ∈ Icc 0 t, HasDerivWithinAt e
      (F (y s) - F (x s) - ((fderiv ℝ F (x s)).comp (Ψ s)) (z' - z)) (Icc 0 t) s :=
    fun s hs => by
      have := (((hsol z' hz'r).deriv s hs).sub ((hsol z hzr).deriv s hs)).sub
        ((hΨd s hs).clm_apply (hasDerivWithinAt_const s _ (z' - z)))
      rw [map_zero, add_zero] at this
      exact this
  have hbound : ∀ s ∈ Ico 0 t,
      ‖F (y s) - F (x s) - ((fderiv ℝ F (x s)).comp (Ψ s)) (z' - z)‖ ≤
        K' * ‖e s‖ + η * E * ‖z' - z‖ := fun s hs => by
    have hs' := Ico_subset_Icc_self hs
    have hyx : ‖y s - x s‖ ≤ ‖z' - z‖ * E := hlip z' hz'r s hs'
    have h1 := hT (x s) (hxa z hzr s hs') (y s) (hxa z' hz'r s hs') (hyx.trans_lt hsmall)
    have h2 : ‖fderiv ℝ F (x s) (e s)‖ ≤ K' * ‖e s‖ := ((fderiv ℝ F (x s)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hK' _ (hxa z hzr s hs')) (norm_nonneg _))
    have heq : F (y s) - F (x s) - ((fderiv ℝ F (x s)).comp (Ψ s)) (z' - z) =
        fderiv ℝ F (x s) (e s) + (F (y s) - F (x s) - fderiv ℝ F (x s) (y s - x s)) := by
      simp only [e, map_sub, ContinuousLinearMap.comp_apply]
      abel
    rw [heq]
    calc _ ≤ ‖fderiv ℝ F (x s) (e s)‖ + ‖F (y s) - F (x s) - fderiv ℝ F (x s) (y s - x s)‖ :=
          norm_add_le _ _
      _ ≤ K' * ‖e s‖ + η * (‖z' - z‖ * E) :=
          add_le_add h2 (h1.trans (mul_le_mul_of_nonneg_left hyx hη.le))
      _ = _ := by ring
  have hgr := norm_le_gronwallBound_of_norm_deriv_right_le (f := e)
    (fun s hs => (hed s hs).continuousWithinAt)
    (fun s hs => (hed s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
      (mem_of_superset (Icc_mem_nhdsGE hs.2) (Icc_subset_Icc_left hs.1)))
    (by rw [he0, norm_zero]) hbound t ⟨ht.1, le_rfl⟩
  rw [sub_zero, gronwallBound_zero_eq] at hgr
  have hG1 : G1 ≤ |G1| + 1 := by linarith [le_abs_self G1]
  calc _ = ‖e t‖ := rfl
    _ ≤ η * E * ‖z' - z‖ * G1 := hgr
    _ ≤ η * E * ‖z' - z‖ * (|G1| + 1) := by gcongr
    _ = c * ‖z' - z‖ := by
      simp only [η]
      field_simp

/-- One more order of differentiability of the flow, from the flows of `F` and of the augmented
field. -/
theorem contDiffOn_flow_succ (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) {n : ℕ}
    (hFn : ContDiffOn ℝ n (flow F U) (dom F U))
    (hGn : ContDiffOn ℝ n (flow (augField F) (U ×ˢ univ)) (dom (augField F) (U ×ˢ univ))) :
    ContDiffOn ℝ (n + 1) (flow F U) (dom F U) := by
  have hF1 : ContDiffOn ℝ 1 F U := hF.of_le (by simp)
  have hFL := locallyLipschitzOn_of_contDiffOn hU hF1
  have hGs := contDiffOn_augField hU hF
  have hGL := locallyLipschitzOn_of_contDiffOn (hU.prod isOpen_univ) (hGs.of_le (by simp))
  have hGo := (isOpen_dom (hU.prod isOpen_univ) (hGs.of_le (by simp))).1
  refine (contDiffOn_of_local hFL fun w hw => ?_).2
  obtain ⟨a, ha, ε, hε, r, hr, K, haU, hK, hbox, hsolb, -⟩ := exists_box hU hF1 hw
  obtain ⟨δ₁, hδ₁, hball⟩ := Metric.isOpen_iff.1 hGo _
    (mem_dom_zero (F := augField F) (show (w, (1 : V →L[ℝ] V)) ∈ U ×ˢ univ from ⟨hw, trivial⟩))
  set δ := min ε δ₁
  set ρ := min r δ₁
  set O := Ioo (-δ) δ ×ˢ ball w ρ
  have hO : IsOpen O := isOpen_Ioo.prod isOpen_ball
  have hδε : δ ≤ ε := min_le_left _ _
  have hδδ : δ ≤ δ₁ := min_le_right _ _
  have hOr : ∀ p ∈ O, p.2 ∈ ball w r := fun p hp => ball_subset_ball (min_le_left _ _) hp.2
  have hOε : ∀ p ∈ O, p.1 ∈ Ioo (-ε) ε := fun p hp =>
    ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩
  have hOD : O ⊆ dom F U := fun p hp =>
    (hbox p.2 (ball_subset_closedBall (hOr p hp)) p.1 (Ioo_subset_Icc_self (hOε p hp))).1
  have hOG : ∀ p ∈ O, (p.1, (p.2, (1 : V →L[ℝ] V))) ∈ dom (augField F) (U ×ˢ univ) :=
    fun p hp => hball (by
      have h1 : |p.1| < δ₁ := abs_lt.2 ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩
      have h2 : dist p.2 w < δ₁ := lt_of_lt_of_le hp.2 (min_le_right _ _)
      simp only [mem_ball, Prod.dist_eq, dist_self, Real.dist_eq, sub_zero, max_lt_iff]
      exact ⟨h1, h2, hδ₁⟩)
  set Ψ : ℝ × V → V →L[ℝ] V := fun p => (flow (augField F) (U ×ˢ univ) (p.1, (p.2, 1))).2
  have hdz : ∀ p ∈ O, HasFDerivAt (fun z' => flow F U (p.1, z')) (Ψ p) p.2 := fun p hp => by
    rcases le_total 0 p.1 with h | h
    · exact hasFDerivAt_flow_of_nonneg hU hF haU hK hbox (hOr p hp)
        ⟨h, (hOε p hp).2.le⟩ (hOG p hp)
    · have hbox' : ∀ z ∈ closedBall w r, ∀ t ∈ Icc (-ε) ε,
          (t, z) ∈ dom (-F) U ∧ flow (-F) U (t, z) ∈ closedBall w a := fun z hz t ht => by
        have h1 := hbox z hz (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
        refine ⟨mem_dom_neg_iff.2 h1.1, ?_⟩
        have := flow_neg hFL h1.1
        simp only [neg_neg] at this
        rw [this]
        exact h1.2
      have hG' : (-p.1, (p.2, (1 : V →L[ℝ] V))) ∈ dom (augField (-F)) (U ×ˢ univ) := by
        rw [augField_neg, mem_dom_neg_iff]
        simpa using hOG p hp
      have hd := hasFDerivAt_flow_of_nonneg (F := -F) hU hF.neg haU (lipschitzOnWith_neg hK) hbox'
        (hOr p hp) ⟨by linarith, by linarith [(hOε p hp).1]⟩ hG'
      have heq1 : flow (augField (-F)) (U ×ˢ univ) (-p.1, (p.2, 1)) =
          flow (augField F) (U ×ˢ univ) (p.1, (p.2, 1)) := by
        rw [augField_neg]
        exact flow_neg hGL (hOG p hp)
      rw [heq1] at hd
      refine hd.congr_of_eventuallyEq ?_
      filter_upwards [isOpen_ball.mem_nhds (hOr p hp)] with z' hz'
      exact (flow_neg hFL (hbox z' (ball_subset_closedBall hz') p.1
        (Ioo_subset_Icc_self (hOε p hp))).1).symm
  have hdt : ∀ p ∈ O, HasDerivAt (fun s => flow F U (s, p.2)) (F (flow F U p)) p.1 :=
    fun p hp => ((hsolb p.2 (ball_subset_closedBall (hOr p hp))).deriv p.1
      (Ioo_subset_Icc_self (hOε p hp))).hasDerivAt (Icc_mem_nhds (hOε p hp).1 (hOε p hp).2)
  have hFfl : ContDiffOn ℝ n (fun p => F (flow F U p)) O :=
    (hF.of_le (by exact_mod_cast le_top)).comp (hFn.mono hOD)
      fun p hp => (mem_of_mem_dom hFL (hOD hp)).2
  have hΨs : ContDiffOn ℝ n Ψ O :=
    contDiff_snd.comp_contDiffOn (hGn.comp
      (by fun_prop : ContDiff ℝ n fun p : ℝ × V => (p.1, (p.2, (1 : V →L[ℝ] V)))).contDiffOn
      fun p hp => hOG p hp)
  have hA : ContDiffOn ℝ n
      (fun p => ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (F (flow F U p))) O :=
    contDiffOn_const.smulRight hFfl
  set D : ℝ × V → ℝ × V →L[ℝ] V := fun p =>
    (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (F (flow F U p))).coprod (Ψ p)
  have hDs : ContDiffOn ℝ n D O := by
    have : D = fun p =>
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (F (flow F U p))).comp
          (ContinuousLinearMap.fst ℝ ℝ V) + (Ψ p).comp (ContinuousLinearMap.snd ℝ ℝ V) := by
      ext1 p
      ext q <;> simp [D]
    rw [this]
    exact (hA.clm_comp contDiffOn_const).add (hΨs.clm_comp contDiffOn_const)
  have hderiv : ∀ p ∈ O, HasFDerivAt (flow F U) (D p) p := fun p hp => by
    have := hasStrictFDerivAt_uncurry_coprod (f := fun t z => flow F U (t, z))
      (f₁ := fun t z => ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (F (flow F U (t, z))))
      (f₂ := fun t z => Ψ (t, z)) (u := p)
      (by filter_upwards [hO.mem_nhds hp] with v hv; exact (hdt v hv).hasFDerivAt)
      (by filter_upwards [hO.mem_nhds hp] with v hv; exact hdz v hv)
      (hA.continuousOn.continuousAt (hO.mem_nhds hp))
      (hΨs.continuousOn.continuousAt (hO.mem_nhds hp))
    exact this.hasFDerivAt
  refine ⟨δ, lt_min hε hδ₁, ρ, lt_min hr hδ₁, hOD, ?_⟩
  refine (contDiffOn_succ_iff_fderiv_of_isOpen hO).2
    ⟨fun p hp => (hderiv p hp).differentiableAt.differentiableWithinAt,
      fun h => by simp at h, hDs.congr fun p hp => (hderiv p hp).fderiv⟩

universe u

/-- The flow of a smooth field is `Cⁿ` on its domain, for every `n`. -/
theorem contDiffOn_flow_nat : ∀ (n : ℕ) {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] {G : W → W} {S : Set W}, IsOpen S → ContDiffOn ℝ ∞ G S →
    ContDiffOn ℝ n (flow G S) (dom G S)
  | 0, _, _, _, _, _, _, hS, hG => by
    rw [Nat.cast_zero, contDiffOn_zero]
    exact (isOpen_dom hS (hG.of_le (by simp))).2
  | n + 1, _, _, _, _, _, _, hS, hG => by
    have := contDiffOn_flow_succ hS hG (contDiffOn_flow_nat n hS hG)
      (contDiffOn_flow_nat n (hS.prod isOpen_univ) (contDiffOn_augField hS hG))
    exact_mod_cast this

/-- **Smooth dependence on the initial point**: the flow of a smooth field is smooth on its
domain, which is open. Hartman, Ordinary differential equations, Chapter V, Theorems 3.1 and
4.1. -/
theorem contDiffOn_flow (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) :
    IsOpen (dom F U) ∧ ContDiffOn ℝ ∞ (flow F U) (dom F U) :=
  ⟨(isOpen_dom hU (hF.of_le (by simp))).1,
    contDiffOn_infty.2 fun n => contDiffOn_flow_nat n hU hF⟩

end

end LorentzianCalderon.ODEFlow
