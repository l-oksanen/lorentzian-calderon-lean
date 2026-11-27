module

public import Mathlib

public section

/-!
# Flows of autonomous ordinary differential equations

For a vector field `F : V → V`, locally Lipschitz on an open set `U`, the maximal flow
`flow F U : ℝ × V → V` on its domain `dom F U`: the points `(t, z)` such that some solution of
`ẋ = F(x)` in `U` with `x(0) = z` reaches the time `t`. Uniqueness, the group property, time
reversal, local existence (Picard–Lindelöf), and a continuation principle: a regularity of the
flow near the time `0` propagates to its whole domain.
-/

namespace LorentzianCalderon.ODEFlow

noncomputable section
open Set Filter Metric Function
open scoped Topology NNReal ContDiff

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {F : V → V} {U : Set V} {c d : ℝ → V} {I J : Set ℝ}

/-- `c` solves `ċ = F(c)` on the interval `I`, staying in `U`. -/
structure IsSol (F : V → V) (U : Set V) (c : ℝ → V) (I : Set ℝ) : Prop where
  interval : I.OrdConnected
  mem : ∀ t ∈ I, c t ∈ U
  deriv : ∀ t ∈ I, HasDerivWithinAt c (F (c t)) I t

/-- The domain of the flow: `(t, z)` such that a solution starting at `z` reaches the time `t`. -/
def dom (F : V → V) (U : Set V) : Set (ℝ × V) :=
  { p | ∃ (c : ℝ → V) (I : Set ℝ), IsSol F U c I ∧ (0 : ℝ) ∈ I ∧ p.1 ∈ I ∧ c 0 = p.2 }

theorem mem_dom {p : ℝ × V} :
    p ∈ dom F U ↔ ∃ (c : ℝ → V) (I : Set ℝ), IsSol F U c I ∧ (0 : ℝ) ∈ I ∧ p.1 ∈ I ∧ c 0 = p.2 :=
  Iff.rfl

/-- The flow: `flow F U (t, z)` is the value at the time `t` of the solution starting at `z`. -/
def flow (F : V → V) (U : Set V) (p : ℝ × V) : V := by
  classical
  exact if h : p ∈ dom F U then h.choose p.1 else p.2

namespace IsSol

/-- A solution is continuous on its interval. -/
theorem continuousOn (hc : IsSol F U c I) : ContinuousOn c I :=
  fun t ht => (hc.deriv t ht).continuousWithinAt

/-- A solution restricts to a subinterval. -/
theorem mono (hc : IsSol F U c I) (hJ : J ⊆ I) (hJc : J.OrdConnected) : IsSol F U c J where
  interval := hJc
  mem t ht := hc.mem t (hJ ht)
  deriv t ht := (hc.deriv t (hJ ht)).mono hJ

/-- A function equal to a solution on its interval is a solution. -/
theorem congr (hc : IsSol F U c I) (h : EqOn d c I) : IsSol F U d I where
  interval := hc.interval
  mem t ht := h ht ▸ hc.mem t ht
  deriv t ht := by
    rw [h ht]
    exact (hc.deriv t ht).congr_of_mem h ht

/-- The solution translated in time. -/
theorem comp_add (hc : IsSol F U c I) (a : ℝ) :
    IsSol F U (fun s => c (s + a)) ((· + a) ⁻¹' I) where
  interval := ⟨fun x hx y hy z hz => hc.interval.out hx hy
    ⟨by simpa using hz.1, by simpa using hz.2⟩⟩
  mem t ht := hc.mem _ ht
  deriv t ht := by
    have := (hc.deriv (t + a) ht).scomp t ((hasDerivAt_id t).add_const a).hasDerivWithinAt
      (fun _ hs => hs)
    rw [one_smul] at this
    exact this

/-- The solution reversed in time solves the equation of `-F`. -/
theorem comp_neg (hc : IsSol F U c I) :
    IsSol (-F) U (fun s => c (-s)) (Neg.neg ⁻¹' I) where
  interval := ⟨fun x hx y hy z hz => hc.interval.out hy hx
    ⟨by simpa using hz.2, by simpa using hz.1⟩⟩
  mem t ht := hc.mem _ ht
  deriv t ht := by
    have := (hc.deriv (-t) ht).scomp t (hasDerivAt_neg t).hasDerivWithinAt (fun _ hs => hs)
    rw [neg_one_smul] at this
    exact this

/-- Derivatives within `I` are one-sided derivatives at the points of an interval in `I`. -/
theorem hasDerivWithinAt_Ici (hc : IsSol F U c I) {a b : ℝ} (hab : Icc a b ⊆ I) {t : ℝ}
    (ht : t ∈ Ico a b) : HasDerivWithinAt c (F (c t)) (Ici t) t :=
  (hc.deriv t (hab (Ico_subset_Icc_self ht))).mono_of_mem_nhdsWithin
    (mem_of_superset (Icc_mem_nhdsGE ht.2) fun _ hs => hab ⟨ht.1.trans hs.1, hs.2⟩)

/-- Derivatives within `I` are left derivatives at the points of an interval in `I`. -/
theorem hasDerivWithinAt_Iic (hc : IsSol F U c I) {a b : ℝ} (hab : Icc a b ⊆ I) {t : ℝ}
    (ht : t ∈ Ioc a b) : HasDerivWithinAt c (F (c t)) (Iic t) t :=
  (hc.deriv t (hab (Ioc_subset_Icc_self ht))).mono_of_mem_nhdsWithin
    (mem_of_superset (Icc_mem_nhdsLE ht.1) fun _ hs => hab ⟨hs.1, hs.2.trans ht.2⟩)

/-- Uniqueness of solutions. -/
theorem eqOn (hF : LocallyLipschitzOn U F) (hc : IsSol F U c I) (hd : IsSol F U d J) {t₀ : ℝ}
    (h₀I : t₀ ∈ I) (h₀J : t₀ ∈ J) (h : c t₀ = d t₀) : EqOn c d (I ∩ J) := by
  rintro t ⟨htI, htJ⟩
  have hSI : uIcc t₀ t ⊆ I := hc.interval.uIcc_subset h₀I htI
  have hSJ : uIcc t₀ t ⊆ J := hd.interval.uIcc_subset h₀J htJ
  set K := c '' uIcc t₀ t ∪ d '' uIcc t₀ t
  have hKc : IsCompact K := (isCompact_uIcc.image_of_continuousOn (hc.continuousOn.mono hSI)).union
    (isCompact_uIcc.image_of_continuousOn (hd.continuousOn.mono hSJ))
  have hKU : K ⊆ U := union_subset (image_subset_iff.2 fun s hs => hc.mem s (hSI hs))
    (image_subset_iff.2 fun s hs => hd.mem s (hSJ hs))
  obtain ⟨L, hL⟩ := (hF.mono hKU).exists_lipschitzOnWith_of_compact hKc
  have hcK : ∀ s ∈ uIcc t₀ t, c s ∈ K := fun s hs => Or.inl ⟨s, hs, rfl⟩
  have hdK : ∀ s ∈ uIcc t₀ t, d s ∈ K := fun s hs => Or.inr ⟨s, hs, rfl⟩
  rcases le_total t₀ t with h' | h'
  · have hS : Icc t₀ t = uIcc t₀ t := (uIcc_of_le h').symm
    exact ODE_solution_unique_of_mem_Icc_right (v := fun _ => F) (s := fun _ => K)
      (fun _ _ => hL) (hc.continuousOn.mono (hS ▸ hSI))
      (fun s hs => hc.hasDerivWithinAt_Ici (hS ▸ hSI) hs)
      (fun s hs => hcK s (hS ▸ Ico_subset_Icc_self hs)) (hd.continuousOn.mono (hS ▸ hSJ))
      (fun s hs => hd.hasDerivWithinAt_Ici (hS ▸ hSJ) hs)
      (fun s hs => hdK s (hS ▸ Ico_subset_Icc_self hs)) h ⟨h', le_rfl⟩
  · have hS : Icc t t₀ = uIcc t₀ t := (uIcc_of_ge h').symm
    exact ODE_solution_unique_of_mem_Icc_left (v := fun _ => F) (s := fun _ => K)
      (fun _ _ => hL) (hc.continuousOn.mono (hS ▸ hSI))
      (fun s hs => hc.hasDerivWithinAt_Iic (hS ▸ hSI) hs)
      (fun s hs => hcK s (hS ▸ Ioc_subset_Icc_self hs)) (hd.continuousOn.mono (hS ▸ hSJ))
      (fun s hs => hd.hasDerivWithinAt_Iic (hS ▸ hSJ) hs)
      (fun s hs => hdK s (hS ▸ Ioc_subset_Icc_self hs)) h ⟨le_rfl, h'⟩

omit [NormedSpace ℝ V] in
/-- Near a point of `I` outside `J`, the union `I ∪ J` of intervals meeting at `s` is `I`. -/
private lemma mem_nhdsWithin_union {s τ : ℝ} (hI : I.OrdConnected) (hJ : J.OrdConnected)
    (hsI : s ∈ I) (hsJ : s ∈ J) (hτI : τ ∈ I) (hτJ : τ ∉ J) : I ∈ 𝓝[I ∪ J] τ := by
  have hsτ : 0 < |s - τ| := abs_pos.2 (sub_ne_zero.2 fun h => hτJ (h ▸ hsJ))
  refine mem_nhdsWithin_iff_exists_mem_nhds_inter.2 ⟨ball τ |s - τ|, ball_mem_nhds _ hsτ, ?_⟩
  rintro y ⟨hy, hy' | hy'⟩
  · exact hy'
  · by_contra hyI
    have h1 : y ∉ uIcc s τ := fun h => hyI (hI.uIcc_subset hsI hτI h)
    have h2 : τ ∉ uIcc s y := fun h => hτJ (hJ.uIcc_subset hsJ hy' h)
    rw [mem_ball, Real.dist_eq] at hy
    simp only [mem_uIcc, not_or, not_and_or, not_le] at h1 h2
    rcases abs_cases (y - τ) with ⟨h3, h3'⟩ | ⟨h3, h3'⟩ <;>
      rcases abs_cases (s - τ) with ⟨h4, h4'⟩ | ⟨h4, h4'⟩ <;> rw [h3, h4] at hy <;>
      rcases h1 with ⟨h5 | h5, h6 | h6⟩ <;> rcases h2 with ⟨h7 | h7, h8 | h8⟩ <;> linarith

/-- Two solutions that agree at a common time glue to a solution on the union. -/
theorem union (hF : LocallyLipschitzOn U F) (hc : IsSol F U c I) (hd : IsSol F U d J) {s : ℝ}
    (hsI : s ∈ I) (hsJ : s ∈ J) (h : c s = d s) :
    ∃ e, IsSol F U e (I ∪ J) ∧ EqOn e c I ∧ EqOn e d J := by
  classical
  have hcd := hc.eqOn hF hd hsI hsJ h
  set e := fun τ => if τ ∈ I then c τ else d τ
  have heI : EqOn e c I := fun τ hτ => by simp [e, hτ]
  have heJ : EqOn e d J := fun τ hτ => by
    by_cases h' : τ ∈ I
    · simp only [e, h', ite_true]
      exact hcd ⟨h', hτ⟩
    · simp [e, h']
  have hsub : ∀ x ∈ I ∪ J, uIcc x s ⊆ I ∪ J := fun x hx => by
    rcases hx with hx | hx
    · exact (hc.interval.uIcc_subset hx hsI).trans subset_union_left
    · exact (hd.interval.uIcc_subset hx hsJ).trans subset_union_right
  have hint : (I ∪ J).OrdConnected := ⟨fun x hx y hy => Icc_subset_uIcc.trans
    ((uIcc_subset_uIcc_union_uIcc (b := s)).trans
      (union_subset (hsub x hx) (uIcc_comm s y ▸ hsub y hy)))⟩
  refine ⟨e, ⟨hint, fun τ hτ => ?_, fun τ hτ => ?_⟩, heI, heJ⟩
  · rcases hτ with hτ | hτ
    · rw [heI hτ]; exact hc.mem τ hτ
    · rw [heJ hτ]; exact hd.mem τ hτ
  · have hdI : ∀ τ ∈ I, HasDerivWithinAt e (F (e τ)) I τ := fun τ hτ => by
      rw [heI hτ]; exact (hc.deriv τ hτ).congr_of_mem heI hτ
    have hdJ : ∀ τ ∈ J, HasDerivWithinAt e (F (e τ)) J τ := fun τ hτ => by
      rw [heJ hτ]; exact (hd.deriv τ hτ).congr_of_mem heJ hτ
    by_cases hτI : τ ∈ I <;> by_cases hτJ : τ ∈ J
    · exact (hdI τ hτI).union (hdJ τ hτJ)
    · exact (hdI τ hτI).mono_of_mem_nhdsWithin
        (mem_nhdsWithin_union hc.interval hd.interval hsI hsJ hτI hτJ)
    · rw [union_comm]
      exact (hdJ τ hτJ).mono_of_mem_nhdsWithin
        (mem_nhdsWithin_union hd.interval hc.interval hsJ hsI hτJ hτI)
    · exact absurd hτ (by simp [hτI, hτJ])

end IsSol

/-- A solution starting at `c 0` puts its times in the domain of the flow. -/
theorem mem_dom_of_isSol (hc : IsSol F U c I) (h0 : (0 : ℝ) ∈ I) {t : ℝ} (ht : t ∈ I) :
    (t, c 0) ∈ dom F U :=
  ⟨c, I, hc, h0, ht, rfl⟩

/-- The flow along a solution is that solution. -/
theorem flow_eq (hF : LocallyLipschitzOn U F) (hc : IsSol F U c I) (h0 : (0 : ℝ) ∈ I) {t : ℝ}
    (ht : t ∈ I) : flow F U (t, c 0) = c t := by
  have hm := mem_dom_of_isSol hc h0 ht
  rw [flow, dite_eq_left hm]
  obtain ⟨J, hd, h0J, htJ, hd0⟩ := hm.choose_spec
  exact hd.eqOn hF hc h0J h0 hd0 ⟨htJ, ht⟩

/-- Any vector is a derivative within a singleton. -/
private lemma hasDerivWithinAt_singleton' (f : ℝ → V) (f' : V) (t : ℝ) :
    HasDerivWithinAt f f' {t} t :=
  HasFDerivWithinAt.of_not_accPt (by rw [accPt_iff_clusterPt, inf_principal]; simp [ClusterPt])

/-- Every point of `U` is in the domain at the time `0`. -/
theorem mem_dom_zero {z : V} (hz : z ∈ U) : ((0 : ℝ), z) ∈ dom F U :=
  mem_dom_of_isSol (c := fun _ => z) (I := {0})
    ⟨ordConnected_singleton, fun _ _ => hz, fun t ht => by
      rw [mem_singleton_iff.1 ht]; exact hasDerivWithinAt_singleton' _ _ _⟩ rfl rfl

/-- The flow at the time `0` is the identity. -/
theorem flow_zero (hF : LocallyLipschitzOn U F) {z : V} (hz : z ∈ U) : flow F U (0, z) = z :=
  flow_eq (c := fun _ => z) (I := {0}) hF
    ⟨ordConnected_singleton, fun _ _ => hz, fun t ht => by
      rw [mem_singleton_iff.1 ht]; exact hasDerivWithinAt_singleton' _ _ _⟩ rfl rfl

/-- The trajectory through a point of the domain is a solution up to that point. -/
theorem isSol_flow (hF : LocallyLipschitzOn U F) {t : ℝ} {z : V} (h : (t, z) ∈ dom F U) :
    IsSol F U (fun s => flow F U (s, z)) (uIcc 0 t) := by
  obtain ⟨c, I, hc, h0, ht, rfl⟩ := h
  exact (hc.mono (hc.interval.uIcc_subset h0 ht) ordConnected_uIcc).congr fun s hs =>
    flow_eq hF hc h0 (hc.interval.uIcc_subset h0 ht hs)

/-- The time slices of the domain are intervals containing `0`. -/
theorem mem_dom_of_mem_uIcc {t s : ℝ} {z : V} (h : (t, z) ∈ dom F U) (hs : s ∈ uIcc 0 t) :
    (s, z) ∈ dom F U := by
  obtain ⟨c, I, hc, h0, ht, rfl⟩ := h
  exact ⟨c, I, hc, h0, hc.interval.uIcc_subset h0 ht hs, rfl⟩

/-- The domain lies over `U`, and the flow maps it into `U`. -/
theorem mem_of_mem_dom (hF : LocallyLipschitzOn U F) {p : ℝ × V} (h : p ∈ dom F U) :
    p.2 ∈ U ∧ flow F U p ∈ U := by
  obtain ⟨c, I, hc, h0, ht, hc0⟩ := h
  refine ⟨hc0 ▸ hc.mem 0 h0, ?_⟩
  rw [show p = (p.1, c 0) by rw [hc0]]
  rw [flow_eq hF hc h0 ht]
  exact hc.mem _ ht

/-- The group property of the flow. -/
theorem flow_add (hF : LocallyLipschitzOn U F) {s t : ℝ} {z : V} (h₁ : (s, z) ∈ dom F U)
    (h₂ : (t, flow F U (s, z)) ∈ dom F U) :
    (s + t, z) ∈ dom F U ∧ flow F U (s + t, z) = flow F U (t, flow F U (s, z)) := by
  obtain ⟨c, I, hc, h0, hs, rfl⟩ := h₁
  rw [flow_eq hF hc h0 hs] at h₂ ⊢
  obtain ⟨d, J, hd, h0J, htJ, hd0⟩ := h₂
  simp only at htJ hd0
  have hd' := hd.comp_add (-s)
  have hsJ : s ∈ (· + -s) ⁻¹' J := by simpa using h0J
  have hstJ : s + t ∈ (· + -s) ⁻¹' J := by simpa using htJ
  obtain ⟨e, he, heI, heJ⟩ := hc.union hF hd' hs hsJ (by simp [hd0])
  have he0 : e 0 = c 0 := heI h0
  refine ⟨he0 ▸ mem_dom_of_isSol he (Or.inl h0) (Or.inr hstJ), ?_⟩
  rw [← he0, flow_eq hF he (Or.inl h0) (Or.inr hstJ), heJ hstJ, ← hd0,
    flow_eq hF hd h0J htJ]
  simp

/-- Reversing the time maps the domain of `F` to that of `-F`. -/
theorem dom_neg {p : ℝ × V} (h : p ∈ dom F U) : (-p.1, p.2) ∈ dom (-F) U := by
  obtain ⟨c, I, hc, h0, ht, hc0⟩ := h
  exact ⟨_, _, hc.comp_neg, by simpa using h0, by simpa using ht, by simpa using hc0⟩

/-- The domain of `-F` is the domain of `F` reversed in time. -/
theorem mem_dom_neg_iff {p : ℝ × V} : p ∈ dom (-F) U ↔ (-p.1, p.2) ∈ dom F U :=
  ⟨fun h => by simpa using dom_neg (F := -F) h, fun h => by simpa using dom_neg h⟩

/-- The flow of `-F` is the flow of `F` reversed in time. -/
theorem flow_neg (hF : LocallyLipschitzOn U F) {p : ℝ × V} (h : p ∈ dom F U) :
    flow (-F) U (-p.1, p.2) = flow F U p := by
  obtain ⟨c, I, hc, h0, ht, hc0⟩ := h
  have hF' : LocallyLipschitzOn U (-F) := by simpa using hF.neg
  have := flow_eq hF' hc.comp_neg (by simpa using h0) (t := -p.1) (by simpa using ht)
  simp only [neg_zero, neg_neg] at this
  rw [← hc0, this, show p = (p.1, c 0) by rw [hc0], flow_eq hF hc h0 ht]

/-- A `C¹` field on an open set is locally Lipschitz there. -/
theorem locallyLipschitzOn_of_contDiffOn (hU : IsOpen U) (hF : ContDiffOn ℝ 1 F U) :
    LocallyLipschitzOn U F := fun x hx => by
  obtain ⟨K, t, ht, hL⟩ := (hF.contDiffAt (hU.mem_nhds hx)).exists_lipschitzOnWith
  exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hL⟩

/-- Local existence (Picard–Lindelöf): near a point `w` of `U`, the flow exists for a uniform
time, stays in a closed ball in `U` on which `F` is Lipschitz, and is continuous. -/
theorem exists_box [FiniteDimensional ℝ V] (hU : IsOpen U) (hF : ContDiffOn ℝ 1 F U) {w : V}
    (hw : w ∈ U) :
    ∃ a > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ r > (0 : ℝ), ∃ K : ℝ≥0, closedBall w a ⊆ U ∧
      LipschitzOnWith K F (closedBall w a) ∧
      (∀ z ∈ closedBall w r, ∀ t ∈ Icc (-ε) ε,
        (t, z) ∈ dom F U ∧ flow F U (t, z) ∈ closedBall w a) ∧
      (∀ z ∈ closedBall w r, IsSol F U (fun s => flow F U (s, z)) (Icc (-ε) ε)) ∧
      ContinuousOn (flow F U) (Icc (-ε) ε ×ˢ closedBall w r) := by
  classical
  have hFL := locallyLipschitzOn_of_contDiffOn hU hF
  obtain ⟨a, ha, haU⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hw)
  obtain ⟨K, hK⟩ := (hF.mono haU).exists_lipschitzOnWith one_ne_zero (convex_closedBall w a)
    (isCompact_closedBall w a)
  obtain ⟨C, hC⟩ := (isCompact_closedBall w a).exists_bound_of_continuousOn
    (hF.mono haU).continuousOn
  set L : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  set ε : ℝ := a / (2 * (L + 1))
  have hε : 0 < ε := by positivity
  set a' : ℝ≥0 := ⟨a, ha.le⟩
  set r' : ℝ≥0 := ⟨a / 2, by positivity⟩
  have hLε : (L : ℝ) * ε ≤ a / 2 := by
    rw [show (L : ℝ) * ε = a / 2 * (L / (L + 1)) by simp only [ε]; field_simp]
    exact mul_le_of_le_one_right (by positivity) ((div_le_one (by positivity)).2 (by linarith))
  have hpl : IsPicardLindelof (fun _ => F) (tmin := -ε) (tmax := ε) ⟨0, by simp [hε.le]⟩
      w a' r' L K :=
    IsPicardLindelof.of_time_independent (fun x hx => (hC x hx).trans (le_max_left _ _)) hK
      (by simp only [sub_zero, zero_sub, neg_neg, max_self]
          change (L : ℝ) * ε ≤ a - a / 2
          linarith)
  have (x) (hx : x ∈ closedBall w r') := ODE.FunSpace.exists_isFixedPt_next hpl hx
  choose α hα using this
  set β := fun (x : V) => if hx : x ∈ closedBall w r' then (α x hx).compProj else fun _ => x
    with hβ
  have hβ0 : ∀ x ∈ closedBall w r', β x 0 = x := fun x hx => by
    rw [hβ]
    beta_reduce
    rw [dite_eq_left hx]
    change (α x hx).compProj ((⟨0, by simp [hε.le]⟩ : Icc (-ε) ε) : ℝ) = x
    rw [ODE.FunSpace.compProj_val, ← hα x hx, ODE.FunSpace.next_apply₀]
  have hβd : ∀ x ∈ closedBall w r', ∀ t ∈ Icc (-ε) ε,
      HasDerivWithinAt (β x) (F (β x t)) (Icc (-ε) ε) t := fun x hx t ht => by
    rw [hβ]
    beta_reduce
    rw [dite_eq_left hx]
    apply ODE.hasDerivWithinAt_picard_Icc (t₀ := 0) (by simp [hε.le]) hpl.continuousOn_uncurry
      (α x hx |>.continuous_compProj.continuousOn)
      (fun _ _ ↦ α x hx |>.compProj_mem_closedBall hpl.mul_max_le)
      x ht |>.congr_of_mem _ ht
    intro t' ht'
    nth_rw 1 [← hα x hx]
    rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]
  have hβm : ∀ x ∈ closedBall w r', ∀ t, β x t ∈ closedBall w a := fun x hx t => by
    simp only [hβ, dite_eq_left hx]
    exact (α x hx).compProj_mem_closedBall hpl.mul_max_le
  obtain ⟨L', hL'⟩ := ODE.FunSpace.exists_forall_closedBall_funSpace_dist_le_mul hpl
  have hβL : ∀ t ∈ Icc (-ε) ε, LipschitzOnWith L' (β · t) (closedBall w r') := fun t ht =>
    LipschitzOnWith.of_dist_le_mul fun x hx y hy => by
      simp only [hβ, dite_eq_left hx, dite_eq_left hy, ODE.FunSpace.compProj_apply]
      rw [← ODE.FunSpace.toContinuousMap_apply_eq_apply,
        ← ODE.FunSpace.toContinuousMap_apply_eq_apply]
      have : Nonempty (Icc (-ε) ε) := ⟨⟨0, by simp [hε.le]⟩⟩
      apply ContinuousMap.dist_le_iff_of_nonempty.mp
      exact hL' x y hx hy (α x hx) (α y hy) (hα x hx) (hα y hy)
  have hsol : ∀ x ∈ closedBall w r', IsSol F U (β x) (Icc (-ε) ε) := fun x hx =>
    ⟨ordConnected_Icc, fun t _ => haU (hβm x hx t), hβd x hx⟩
  have h0 : (0 : ℝ) ∈ Icc (-ε) ε := by simp [hε.le]
  have hfl : ∀ x ∈ closedBall w r', ∀ t ∈ Icc (-ε) ε, flow F U (t, x) = β x t :=
    fun x hx t ht => by
      have := flow_eq hFL (hsol x hx) h0 ht
      rwa [hβ0 x hx] at this
  refine ⟨a, ha, ε, hε, a / 2, by positivity, K, haU, hK, fun z hz t ht => ?_,
    fun z hz => (hsol z hz).congr fun t ht => hfl z hz t ht, ?_⟩
  · have := mem_dom_of_isSol (hsol z hz) h0 ht
    rw [hβ0 z hz] at this
    exact ⟨this, hfl z hz t ht ▸ hβm z hz t⟩
  · refine ContinuousOn.congr (f := fun p : ℝ × V => β p.2 p.1) ?_ fun p hp => hfl _ hp.2 _ hp.1
    exact continuousOn_prod_of_continuousOn_lipschitzOnWith' _ L' hβL fun x hx =>
      HasDerivWithinAt.continuousOn (hβd x hx)

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
/-- A relatively clopen part of a preconnected set is all of it. -/
private lemma subset_of_closure_inter_subset' {X : Type*} [TopologicalSpace X] {S u : Set X}
    (hS : IsPreconnected S) (hu : IsOpen u) (hne : (S ∩ u).Nonempty)
    (h : ∀ x ∈ S, x ∈ closure (S ∩ u) → x ∈ u) : S ⊆ u := by
  by_contra hsub
  obtain ⟨x, hxS, hxu⟩ := not_subset.1 hsub
  obtain ⟨y, hyS, hyu, hyc⟩ := hS u (closure (S ∩ u))ᶜ hu isClosed_closure.isOpen_compl
    (fun y hy => by
      by_cases hy' : y ∈ closure (S ∩ u)
      · exact Or.inl (h y hy hy')
      · exact Or.inr hy') hne ⟨x, hxS, fun hx => hxu (h x hxS hx)⟩
  exact hyc (subset_closure ⟨hyS, hyu⟩)

/-- Continuation: a regularity of the flow near the time `0` holds on the whole domain of the
flow, which is open. -/
theorem contDiffOn_of_local (hF : LocallyLipschitzOn U F) {k : WithTop ℕ∞}
    (hloc : ∀ w ∈ U, ∃ δ > (0 : ℝ), ∃ ρ > (0 : ℝ), Ioo (-δ) δ ×ˢ ball w ρ ⊆ dom F U ∧
      ContDiffOn ℝ k (flow F U) (Ioo (-δ) δ ×ˢ ball w ρ)) :
    IsOpen (dom F U) ∧ ContDiffOn ℝ k (flow F U) (dom F U) := by
  set good := { p : ℝ × V | ∃ N, IsOpen N ∧ p ∈ N ∧ N ⊆ dom F U ∧
    ContDiffOn ℝ k (flow F U) N }
  have hgood : IsOpen good := isOpen_iff_forall_mem_open.2 fun p ⟨N, hN, hpN, hND, hNs⟩ =>
    ⟨N, fun q hq => ⟨N, hN, hq, hND, hNs⟩, hN, hpN⟩
  suffices h : dom F U ⊆ good by
    refine ⟨isOpen_iff_forall_mem_open.2 fun p hp => ?_, contDiffOn_of_locally_contDiffOn
      fun p hp => ?_⟩
    · obtain ⟨N, hN, hpN, hND, _⟩ := h hp
      exact ⟨N, hND, hN, hpN⟩
    · obtain ⟨N, hN, hpN, _, hNs⟩ := h hp
      exact ⟨N, hN, hpN, hNs.mono inter_subset_right⟩
  rintro ⟨T, z₀⟩ hT
  have hz₀ : z₀ ∈ U := (mem_of_mem_dom hF hT).1
  have hγ := isSol_flow hF hT
  set u := { s : ℝ | (s, z₀) ∈ good }
  have hu : IsOpen u := hgood.preimage (continuous_id.prodMk continuous_const)
  have h0u : (0 : ℝ) ∈ u := by
    obtain ⟨δ, hδ, ρ, hρ, hsub, hs⟩ := hloc z₀ hz₀
    exact ⟨_, isOpen_Ioo.prod isOpen_ball, ⟨⟨by linarith, hδ⟩, mem_ball_self hρ⟩, hsub, hs⟩
  suffices uIcc 0 T ⊆ u from this right_mem_uIcc
  refine subset_of_closure_inter_subset' isPreconnected_uIcc hu ⟨0, left_mem_uIcc, h0u⟩
    fun s hs hcl => ?_
  set w := flow F U (s, z₀)
  obtain ⟨δ, hδ, ρ, hρ, hsub, hsm⟩ := hloc w (hγ.mem s hs)
  obtain ⟨N₁, hN₁, hN₁'⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1
    (hγ.continuousOn s hs (ball_mem_nhds _ hρ))
  obtain ⟨s', ⟨hs'1, hs'2⟩, hs'S, hs'u⟩ := mem_closure_iff_nhds.1 hcl _
    (inter_mem hN₁ (ball_mem_nhds s (half_pos hδ)))
  have hs'w : flow F U (s', z₀) ∈ ball w ρ := hN₁' ⟨hs'1, hs'S⟩
  obtain ⟨N', hN', hs'N', hN'D, hN's⟩ := hs'u
  set M := (fun z : V => (s', z)) ⁻¹' (N' ∩ flow F U ⁻¹' ball w ρ)
  have hM : IsOpen M := (hN's.continuousOn.isOpen_inter_preimage hN' isOpen_ball).preimage
    (continuous_const.prodMk continuous_id)
  set N := Ioo (s' - δ) (s' + δ) ×ˢ M
  have hkey : ∀ p ∈ N, p ∈ dom F U ∧ flow F U p = flow F U (p.1 - s', flow F U (s', p.2)) :=
    fun p hp => by
      have h1 : (p.1 - s', flow F U (s', p.2)) ∈ dom F U := hsub
        ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩, hp.2.2⟩
      have := flow_add hF (hN'D hp.2.1) h1
      rwa [add_sub_cancel] at this
  have hs's : |s' - s| < δ / 2 := by
    rw [← Real.dist_eq]
    exact hs'2
  refine ⟨N, isOpen_Ioo.prod hM, ⟨⟨by linarith [abs_lt.1 hs's], by linarith [abs_lt.1 hs's]⟩,
    hs'N', hs'w⟩, fun p hp => (hkey p hp).1, ?_⟩
  refine ContDiffOn.congr ?_ fun p hp => (hkey p hp).2
  refine hsm.comp ((contDiffOn_fst.sub contDiffOn_const).prodMk
    (hN's.comp (contDiffOn_const.prodMk contDiffOn_snd) fun p hp => hp.2.1)) fun p hp =>
      ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩, hp.2.2⟩

/-- The domain of the flow is open and the flow is continuous on it. -/
theorem isOpen_dom [FiniteDimensional ℝ V] (hU : IsOpen U) (hF : ContDiffOn ℝ 1 F U) :
    IsOpen (dom F U) ∧ ContinuousOn (flow F U) (dom F U) := by
  have := contDiffOn_of_local (k := 0) (locallyLipschitzOn_of_contDiffOn hU hF) fun w hw => by
    obtain ⟨a, ha, ε, hε, r, hr, K, -, -, hbox, -, hcont⟩ := exists_box hU hF hw
    refine ⟨ε, hε, r, hr, fun p hp => (hbox p.2 (ball_subset_closedBall hp.2) p.1
      (Ioo_subset_Icc_self hp.1)).1, ?_⟩
    exact contDiffOn_zero.2 (hcont.mono (prod_mono Ioo_subset_Icc_self ball_subset_closedBall))
  exact ⟨this.1, contDiffOn_zero.1 this.2⟩

end

end LorentzianCalderon.ODEFlow
