module

public import LorentzianCalderon.Waves.Calculus
public import LorentzianCalderon.Waves.Flow
public import LorentzianCalderon.Induction.Setup
public import LorentzianCalderon.Causal.TimeFlow
public import LorentzianCalderon.Green.Basic

public section

/-!
# Flow box and transport equations

The first two steps of blueprint `lem_onesided`. For a vector field `Ẑ` on an open set `T` with
`Ẑϱ = 1` for a smooth function `ϱ`, the flow box `boxSet` is the set of points whose flow line
reaches the level `ϱ = τ₀`, and `flowProj x` is the point where it does. Linear transport equations
`Ẑb + a b = f` are solved along the flow lines with `b = 0` on the level `ϱ = τ₀`
(`FlowBoxData.exists_transport`).
-/

namespace LorentzianCalderon

noncomputable section
open MeasureTheory Set Filter Function
open scoped ContDiff Topology Matrix

variable {n : ℕ}

/-! ### Calculus on the line -/

/-- A solution of `β' = A β + F` with `β(lo) = 0` and a source `F ≥ 0` that is positive at
`c ∈ [lo, hi)` is positive at `hi`. -/
theorem pos_of_hasDerivAt_linear {O : Set ℝ} (hO : IsOpen O) {lo c hi : ℝ} (hlc : lo ≤ c)
    (hch : c < hi) (hsub : Icc lo hi ⊆ O) {A F β : ℝ → ℝ} (hA : ContinuousOn A O)
    (hF : ContinuousOn F O) (hβ : ∀ s ∈ Icc lo hi, HasDerivAt β (A s * β s + F s) s)
    (h0 : β lo = 0) (hF0 : ∀ s ∈ Icc lo hi, 0 ≤ F s) (hFc : 0 < F c) : 0 < β hi := by
  have hlo : lo ∈ Icc lo hi := left_mem_Icc.2 (hlc.trans hch.le)
  set G : ℝ → ℝ := fun s => ∫ r in lo..s, A r
  have hG : ∀ s ∈ Icc lo hi, HasDerivAt G (A s) s := fun s hs =>
    intervalIntegral.integral_hasDerivAt_right
      ((hA.mono ((uIcc_subset_Icc hlo hs).trans hsub)).intervalIntegrable)
      (hA.stronglyMeasurableAtFilter hO s (hsub hs)) (hA.continuousAt (hO.mem_nhds (hsub hs)))
  set w : ℝ → ℝ := fun s => β s * Real.exp (-G s)
  have hw : ∀ s ∈ Icc lo hi, HasDerivAt w (F s * Real.exp (-G s)) s := fun s hs => by
    exact ((hβ s hs).mul ((hG s hs).neg.exp)).congr_deriv (by simp only [Pi.neg_apply]; ring)
  have hwc : ContinuousOn w (Icc lo hi) := fun s hs => (hw s hs).continuousAt.continuousWithinAt
  have hmono : MonotoneOn w (Icc lo hi) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc lo hi) hwc (fun s hs => ?_) fun s hs => ?_
    · exact (hw s (interior_subset hs)).differentiableAt.differentiableWithinAt
    · rw [(hw s (interior_subset hs)).deriv]
      exact mul_nonneg (hF0 s (interior_subset hs)) (Real.exp_pos _).le
  have hcO : c ∈ O := hsub ⟨hlc, hch.le⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1
    ((hF.continuousAt (hO.mem_nhds hcO)).eventually (lt_mem_nhds hFc))
  set δ := min (ε / 2) (hi - c)
  have hδ : 0 < δ := lt_min (by positivity) (by linarith)
  have hδh : c + δ ≤ hi := by linarith [min_le_right (ε / 2) (hi - c)]
  have hsub' : Icc c (c + δ) ⊆ Icc lo hi := Icc_subset_Icc hlc hδh
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope w (fun s => F s * Real.exp (-G s))
    (by linarith : c < c + δ) (hwc.mono hsub')
    (fun s hs => hw s (hsub' (Ioo_subset_Icc_self hs)))
  have hFξ : 0 < F ξ := hball (by
    rw [Real.dist_eq, abs_of_pos (by linarith [hξ.1])]
    linarith [hξ.2, min_le_left (ε / 2) (hi - c)])
  have hstep : w c < w (c + δ) := by
    have h1 : 0 < (w (c + δ) - w c) / (c + δ - c) := hξeq ▸ mul_pos hFξ (Real.exp_pos _)
    rw [show c + δ - c = δ by ring] at h1
    have := (div_pos_iff_of_pos_right hδ).1 h1
    linarith
  have h1 := hmono hlo ⟨hlc, hch.le⟩ hlc
  have h2 := hmono (hsub' (right_mem_Icc.2 (by linarith))) (right_mem_Icc.2 (hlc.trans hch.le))
    hδh
  have hwlo : w lo = 0 := by simp [w, h0]
  have : 0 < w hi := by linarith
  exact (mul_pos_iff_of_pos_right (Real.exp_pos _)).1 this

/-! ### The flow box -/

/-- The autonomous equation `ẋ = Ẑ(x)`, with a dummy parameter. -/
def zField (Zh : E n → E n) : ℝ → E n → ℝ → E n := fun _ x _ => Zh x

theorem zField_def (Zh : E n → E n) :
    zField Zh =
      fun _ x _ => Zh x := by rfl

/-- `Ẑ` is smooth on the open set `T`, `Ẑϱ = 1` there, and `X` is its flow. -/
structure FlowBoxData (T : Set (E n)) (ϱ : E n → ℝ) (Zh : E n → E n)
    (X : ℝ × ℝ × E n × ℝ → E n) : Prop where
  isOpen : IsOpen T
  ϱ_smooth : ContDiff ℝ ∞ ϱ
  Zh_smooth : ContDiffOn ℝ ∞ Zh T
  time : ∀ x ∈ T, fderiv ℝ ϱ x (Zh x) = 1
  flow : IsFlow (zField Zh) T univ X

/-- The points of `T` whose flow line reaches the level `ϱ = τ₀`. -/
def boxSet (T : Set (E n)) (ϱ : E n → ℝ) (Zh : E n → E n) (τ₀ : ℝ) : Set (E n) :=
  { x | x ∈ T ∧ (τ₀, ϱ x, x, (0 : ℝ)) ∈ flowDom (zField Zh) T univ }

theorem mem_boxSet {T : Set (E n)} {ϱ : E n → ℝ} {Zh : E n → E n} {τ₀ : ℝ} {x} :
    x ∈ boxSet T ϱ Zh τ₀ ↔ x ∈ T ∧ (τ₀, ϱ x, x, (0 : ℝ)) ∈ flowDom (zField Zh) T univ := Iff.rfl

/-- The point where the flow line of `x` meets the level `ϱ = τ₀`. -/
def flowProj (ϱ : E n → ℝ) (X : ℝ × ℝ × E n × ℝ → E n) (τ₀ : ℝ) (x : E n) : E n :=
  X (τ₀, ϱ x, x, 0)

theorem flowProj_def (ϱ : E n → ℝ) (X : ℝ × ℝ × E n × ℝ → E n) (τ₀ : ℝ) (x : E n) :
    flowProj ϱ X τ₀ x =
      X (τ₀, ϱ x, x, 0) := by rfl

namespace FlowBoxData

variable {T : Set (E n)} {ϱ : E n → ℝ} {Zh : E n → E n} {X : ℝ × ℝ × E n × ℝ → E n}
  (hD : FlowBoxData T ϱ Zh X) (τ₀ : ℝ)
include hD

theorem time_eq {t t₀ : ℝ} {x₀ : E n} (h : (t, t₀, x₀, (0 : ℝ)) ∈ flowDom (zField Zh) T univ) :
    ϱ (X (t, t₀, x₀, 0)) = ϱ x₀ + (t - t₀) :=
  hD.flow.time_eq (fun y hy _ => ⟨(hD.ϱ_smooth.differentiable (by simp) y).hasFDerivAt,
    hD.time y hy⟩) h

theorem isOpen_boxSet : IsOpen (boxSet T ϱ Zh τ₀) :=
  hD.isOpen.inter (hD.flow.isOpen.preimage
    (continuous_const.prodMk (hD.ϱ_smooth.continuous.prodMk
      (continuous_id.prodMk continuous_const))))

omit hD in
theorem boxSet_subset : boxSet T ϱ Zh τ₀ ⊆ T := fun _ hx => hx.1

theorem contDiffOn_flowProj : ContDiffOn ℝ ∞ (flowProj ϱ X τ₀) (boxSet T ϱ Zh τ₀) :=
  hD.flow.smooth.comp (contDiff_const.prodMk (hD.ϱ_smooth.prodMk
    (contDiff_id.prodMk contDiff_const))).contDiffOn fun _ hx => hx.2

/-- Moving along the flow line of a point of the flow box. -/
theorem flowLine {x : E n} (hx : x ∈ boxSet T ϱ Zh τ₀) {s : ℝ}
    (hs : (s, ϱ x, x, (0 : ℝ)) ∈ flowDom (zField Zh) T univ) :
    X (s, ϱ x, x, 0) ∈ boxSet T ϱ Zh τ₀ ∧ ϱ (X (s, ϱ x, x, 0)) = s ∧
      flowProj ϱ X τ₀ (X (s, ϱ x, x, 0)) = flowProj ϱ X τ₀ x ∧
      (s, τ₀, flowProj ϱ X τ₀ x, (0 : ℝ)) ∈ flowDom (zField Zh) T univ ∧
      X (s, τ₀, flowProj ϱ X τ₀ x, 0) = X (s, ϱ x, x, 0) := by
  have hϱ : ϱ (X (s, ϱ x, x, 0)) = s := by rw [hD.time_eq hs]; ring
  obtain ⟨h1, h2⟩ := hD.flow.flow hx.2 hs
  obtain ⟨h3, h4⟩ := hD.flow.flow hs hx.2
  refine ⟨⟨hD.flow.mem_U hs, ?_⟩, hϱ, ?_, h3, h4⟩
  · rw [hϱ]; exact h1
  · simp only [flowProj, hϱ]; exact h2

theorem mem_of_uIcc {x : E n} (hx : x ∈ boxSet T ϱ Zh τ₀) {s : ℝ} (hs : s ∈ uIcc τ₀ (ϱ x)) :
    (s, ϱ x, x, (0 : ℝ)) ∈ flowDom (zField Zh) T univ :=
  IsFlow.mem_of_uIcc hx.2 (hD.flow.self hx.2).1 hs

theorem self {x : E n} (hx : x ∈ boxSet T ϱ Zh τ₀) :
    (ϱ x, ϱ x, x, (0 : ℝ)) ∈ flowDom (zField Zh) T univ ∧ X (ϱ x, ϱ x, x, 0) = x :=
  hD.flow.self hx.2

theorem time_flowProj {x : E n} (hx : x ∈ boxSet T ϱ Zh τ₀) : ϱ (flowProj ϱ X τ₀ x) = τ₀ := by
  rw [flowProj, hD.time_eq hx.2]; ring

theorem eq_flow_flowProj {x : E n} (hx : x ∈ boxSet T ϱ Zh τ₀) :
    (ϱ x, τ₀, flowProj ϱ X τ₀ x, (0 : ℝ)) ∈ flowDom (zField Zh) T univ ∧
      X (ϱ x, τ₀, flowProj ϱ X τ₀ x, 0) = x := by
  obtain ⟨-, -, -, h1, h2⟩ := hD.flowLine τ₀ hx (hD.self τ₀ hx).1
  exact ⟨h1, h2.trans (hD.self τ₀ hx).2⟩

/-- **Transport along the flow lines.** The linear equation `Ẑb + a b = f` has a smooth solution
on the flow box with `b = 0` on the level `ϱ = τ₀`. It vanishes at `x` if `f` vanishes on the
flow line of `x` between the levels `τ₀` and `ϱ(x)`, and is positive at `x` if `f ≥ 0` and `f` is
positive at a point of that flow line below `x`. -/
theorem exists_transport {a f : E n → ℝ} (ha : ContDiffOn ℝ ∞ a (boxSet T ϱ Zh τ₀))
    (hf : ContDiffOn ℝ ∞ f (boxSet T ϱ Zh τ₀)) :
    ∃ b : E n → ℝ, ContDiffOn ℝ ∞ b (boxSet T ϱ Zh τ₀) ∧
      (∀ x ∈ boxSet T ϱ Zh τ₀, fderiv ℝ b x (Zh x) + a x * b x = f x) ∧
      (∀ x ∈ boxSet T ϱ Zh τ₀, (∀ y ∈ boxSet T ϱ Zh τ₀, flowProj ϱ X τ₀ y = flowProj ϱ X τ₀ x →
        ϱ y ∈ uIcc τ₀ (ϱ x) → f y = 0) → b x = 0) ∧
      ((∀ y ∈ boxSet T ϱ Zh τ₀, 0 ≤ f y) → ∀ x ∈ boxSet T ϱ Zh τ₀, ∀ y ∈ boxSet T ϱ Zh τ₀,
        flowProj ϱ X τ₀ y = flowProj ϱ X τ₀ x → τ₀ ≤ ϱ y → ϱ y < ϱ x → 0 < f y → 0 < b x) := by
  set B := boxSet T ϱ Zh τ₀ with hB_def
  set π := flowProj ϱ X τ₀
  have hB : IsOpen B := hD.isOpen_boxSet τ₀
  have hBT : B ⊆ T := boxSet_subset τ₀
  set Fa : ℝ → E n × ℝ → ℝ → E n × ℝ := fun _ z _ => (Zh z.1, -a z.1 * z.2 + f z.1)
  have hFa : ContDiffOn ℝ ∞ (fun z : E n × ℝ => (Zh z.1, -a z.1 * z.2 + f z.1)) (B ×ˢ univ) := by
    have hm : MapsTo (fun z : E n × ℝ => z.1) (B ×ˢ univ) B := fun z hz => hz.1
    exact ((hD.Zh_smooth.mono hBT).comp contDiff_fst.contDiffOn hm).prodMk
      (((ha.comp contDiff_fst.contDiffOn hm).neg.mul contDiff_snd.contDiffOn).add
        (hf.comp contDiff_fst.contDiffOn hm))
  obtain ⟨Xa, hXa⟩ := exists_isFlow (P := ℝ) (hB.prod isOpen_univ) hFa
  -- the flow line `γ` of `x`, which stays in the flow box
  have hγB : ∀ x ∈ B, ∀ s ∈ uIcc τ₀ (ϱ x), X (s, ϱ x, x, 0) ∈ B ∧
      ϱ (X (s, ϱ x, x, 0)) = s ∧ π (X (s, ϱ x, x, 0)) = π x := fun x hx s hs => by
    obtain ⟨h1, h2, h3, -⟩ := hD.flowLine τ₀ hx (hD.mem_of_uIcc τ₀ hx hs)
    exact ⟨h1, h2, h3⟩
  have hγc : ∀ x ∈ B, ContinuousOn (fun s => X (s, ϱ x, x, 0)) (uIcc τ₀ (ϱ x)) :=
    fun x hx s hs => (hD.flow.hasDerivAt (hD.mem_of_uIcc τ₀ hx hs)).continuousAt.continuousWithinAt
  -- a solution of the augmented system along the flow line of `x`
  have hsol : ∀ x ∈ B, ∀ β : ℝ → ℝ, β τ₀ = 0 →
      (∀ s ∈ uIcc τ₀ (ϱ x), HasDerivWithinAt β
        (-a (X (s, ϱ x, x, 0)) * β s + f (X (s, ϱ x, x, 0))) (uIcc τ₀ (ϱ x)) s) →
      (ϱ x, τ₀, (π x, (0 : ℝ)), (0 : ℝ)) ∈ flowDom Fa (B ×ˢ univ) univ ∧
        Xa (ϱ x, τ₀, (π x, 0), 0) = (x, β (ϱ x)) := fun x hx β hβ0 hβ => by
    have hs : Facts.IsODESolution Fa (B ×ˢ univ) 0 (fun s => (X (s, ϱ x, x, 0), β s))
        (uIcc τ₀ (ϱ x)) := {
      interval := ordConnected_uIcc
      mem := fun s hs => ⟨(hγB x hx s hs).1, mem_univ _⟩
      deriv := fun s hs =>
        ((hD.flow.hasDerivAt (hD.mem_of_uIcc τ₀ hx hs)).hasDerivWithinAt.prodMk (hβ s hs)) }
    have := hXa.mem_of_sol (mem_univ _) hs right_mem_uIcc left_mem_uIcc
    simp only [hβ0, (hD.self τ₀ hx).2] at this
    exact this
  have hex : ∀ x ∈ B, ∃ β : ℝ → ℝ, β τ₀ = 0 ∧ ∀ s ∈ uIcc τ₀ (ϱ x), HasDerivWithinAt β
      (-a (X (s, ϱ x, x, 0)) * β s + f (X (s, ϱ x, x, 0))) (uIcc τ₀ (ϱ x)) s := fun x hx => by
    have hm : MapsTo (fun s => X (s, ϱ x, x, 0)) (uIcc τ₀ (ϱ x)) B := fun s hs =>
      (hγB x hx s hs).1
    obtain ⟨β, hβ0, hβ⟩ := exists_linear_scalar_ode
      (ha.continuousOn.comp (hγc x hx) hm) (hf.continuousOn.comp (hγc x hx) hm)
    exact ⟨β, hβ0, fun s hs => (hβ s hs).hasDerivWithinAt⟩
  set b : E n → ℝ := fun x => (Xa (ϱ x, τ₀, (π x, 0), 0)).2
  have hkey : ∀ x ∈ B, (ϱ x, τ₀, (π x, (0 : ℝ)), (0 : ℝ)) ∈ flowDom Fa (B ×ˢ univ) univ ∧
      Xa (ϱ x, τ₀, (π x, 0), 0) = (x, b x) := fun x hx => by
    obtain ⟨β, hβ0, hβ⟩ := hex x hx
    obtain ⟨h1, h2⟩ := hsol x hx β hβ0 hβ
    refine ⟨h1, ?_⟩
    simp only [b, h2]
  have hψ : ContDiffOn ℝ ∞ (fun x => (ϱ x, τ₀, (π x, (0 : ℝ)), (0 : ℝ))) B :=
    hD.ϱ_smooth.contDiffOn.prodMk (contDiffOn_const.prodMk
      (((hD.contDiffOn_flowProj τ₀).prodMk contDiffOn_const).prodMk contDiffOn_const))
  have hb : ContDiffOn ℝ ∞ b B :=
    contDiff_snd.comp_contDiffOn (hXa.smooth.comp hψ fun x hx => (hkey x hx).1)
  refine ⟨b, hb, fun x hx => ?_, fun x hx hvan => ?_, fun hf0 x hx y hy hyx hy0 hyx' hfy => ?_⟩
  · -- the transport equation
    have hself := hD.self τ₀ hx
    have hev : (fun s => b (X (s, ϱ x, x, 0))) =ᶠ[𝓝 (ϱ x)]
        fun s => (Xa (s, τ₀, (π x, 0), 0)).2 := by
      filter_upwards [hD.flow.eventually_mem hself.1] with s hs
      obtain ⟨h1, h2, h3, -, -⟩ := hD.flowLine τ₀ hx hs
      simp only [b, h2]
      rw [show π (X (s, ϱ x, x, 0)) = π x from h3]
    have hR : HasDerivAt (fun s => (Xa (s, τ₀, (π x, 0), 0)).2) (-a x * b x + f x) (ϱ x) := by
      have := hasFDerivAt_snd.comp_hasDerivAt _ (hXa.hasDerivAt (hkey x hx).1)
      rw [(hkey x hx).2] at this
      exact this
    have hc := hD.flow.hasDerivAt hself.1
    rw [hself.2] at hc
    have hbd : HasFDerivAt b (fderiv ℝ b x) x :=
      ((hb.contDiffAt (hB.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
    rw [← hself.2] at hbd
    have hL := hbd.comp_hasDerivAt (ϱ x) hc
    rw [hself.2] at hL
    have := hL.unique (hR.congr_of_eventuallyEq hev)
    simp only [zField] at this
    linarith
  · -- vanishing
    have hs : Facts.IsODESolution Fa (B ×ˢ univ) 0 (fun s => (X (s, ϱ x, x, 0), (0 : ℝ)))
        (uIcc τ₀ (ϱ x)) := {
      interval := ordConnected_uIcc
      mem := fun s hs => ⟨(hγB x hx s hs).1, mem_univ _⟩
      deriv := fun s hs => by
        obtain ⟨h1, h2, h3⟩ := hγB x hx s hs
        refine ((hD.flow.hasDerivAt (hD.mem_of_uIcc τ₀ hx hs)).hasDerivWithinAt.prodMk
          (hasDerivWithinAt_const _ _ (0 : ℝ))).congr_deriv ?_
        simp only [Fa, zField, mul_zero, zero_add, hvan _ h1 h3 (by rw [h2]; exact hs)] }
    have := hXa.mem_of_sol (mem_univ _) hs right_mem_uIcc left_mem_uIcc
    simp only [(hD.self τ₀ hx).2] at this
    exact congrArg Prod.snd this.2
  · -- positivity
    set O := {s : ℝ | (s, τ₀, (π x, (0 : ℝ)), (0 : ℝ)) ∈ flowDom Fa (B ×ˢ univ) univ}
    have hO : IsOpen O := hXa.isOpen.preimage (IsFlow.continuous_slice _ _ _)
    have hOB : ∀ s ∈ O, (Xa (s, τ₀, (π x, 0), 0)).1 ∈ B := fun s hs => (hXa.mem_U hs).1
    have hXc : ContinuousOn (fun s => (Xa (s, τ₀, (π x, 0), 0)).1) O := fun s hs =>
      (continuous_fst.continuousAt.comp
        (hXa.hasDerivAt hs).continuousAt).continuousWithinAt
    have hsub : Icc τ₀ (ϱ x) ⊆ O := fun s hs =>
      hXa.mem_of_uIcc_self (hkey x hx).1 (Icc_subset_uIcc hs)
    have hlt : τ₀ < ϱ x := hy0.trans_lt hyx'
    have hy' := hkey y hy
    rw [hyx] at hy'
    refine pos_of_hasDerivAt_linear hO hy0 hyx' hsub (A := fun s => -a (Xa (s, τ₀, (π x, 0), 0)).1)
      (F := fun s => f (Xa (s, τ₀, (π x, 0), 0)).1)
      (β := fun s => (Xa (s, τ₀, (π x, 0), 0)).2)
      (ha.continuousOn.comp hXc hOB).neg (hf.continuousOn.comp hXc hOB) (fun s hs => ?_) ?_
      (fun s hs => hf0 _ (hOB s (hsub hs))) ?_
    · exact hasFDerivAt_snd.comp_hasDerivAt _ (hXa.hasDerivAt (hsub hs))
    · rw [(hXa.self (hkey x hx).1).2]
    · rw [hy'.2]
      exact hfy

end FlowBoxData

/-- A curve in `T` whose velocity is a positive multiple of `Ẑ` is, reparametrized by `ϱ`, a flow
line of `Ẑ`. -/
theorem FlowBoxData.flowLine_of_tangent {T : Set (E n)} {ϱ : E n → ℝ} {Zh : E n → E n}
    {X : ℝ × ℝ × E n × ℝ → E n} (hD : FlowBoxData T ϱ Zh X) {σ : ℝ → E n} {I : Set ℝ}
    (hI : IsOpen I) (hσ : ContDiffOn ℝ ∞ σ I) {t₁ t₂ : ℝ} (hsub : Icc t₁ t₂ ⊆ I)
    (himage : σ '' Icc t₁ t₂ ⊆ T) (hpos : ∀ s ∈ Icc t₁ t₂, 0 < fderiv ℝ ϱ (σ s) (deriv σ s))
    (hZh : ∀ s ∈ Icc t₁ t₂, Zh (σ s) = (fderiv ℝ ϱ (σ s) (deriv σ s))⁻¹ • deriv σ s)
    {a e : ℝ} (ha : t₁ < a) (hae : a ≤ e) (he : e < t₂) :
    StrictMonoOn (fun s => ϱ (σ s)) (Icc t₁ t₂) ∧ ∀ s ∈ Icc a e,
      (ϱ (σ s), ϱ (σ a), σ a, (0 : ℝ)) ∈ flowDom (zField Zh) T univ ∧
        X (ϱ (σ s), ϱ (σ a), σ a, 0) = σ s := by
  set τ : ℝ → ℝ := fun s => ϱ (σ s)
  have hσd : ∀ s ∈ I, HasDerivAt σ (deriv σ s) s := fun s hs =>
    ((hσ.contDiffAt (hI.mem_nhds hs)).differentiableAt (by simp)).hasDerivAt
  have hτd : ∀ s ∈ I, HasDerivAt τ (fderiv ℝ ϱ (σ s) (deriv σ s)) s := fun s hs =>
    (hD.ϱ_smooth.differentiable (by simp) (σ s)).hasFDerivAt.comp_hasDerivAt s (hσd s hs)
  have hτc : ContinuousOn τ (Icc t₁ t₂) := fun s hs =>
    (hτd s (hsub hs)).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn τ (Icc t₁ t₂) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc t₁ t₂) hτc fun s hs => ?_
    rw [interior_Icc] at hs
    rw [(hτd s (hsub (Ioo_subset_Icc_self hs))).deriv]
    exact hpos s (Ioo_subset_Icc_self hs)
  refine ⟨hmono, ?_⟩
  set J := Ioo t₁ t₂
  have hinj : InjOn τ J := hmono.injOn.mono Ioo_subset_Icc_self
  set ginv := invFunOn τ J
  have hleft : ∀ s ∈ J, ginv (τ s) = s := fun s hs => hinj.leftInvOn_invFunOn hs
  have ht₁₂ : t₁ < t₂ := ha.trans_le hae |>.trans he
  have hIoo : Ioo (τ t₁) (τ t₂) ⊆ τ '' J := intermediate_value_Ioo ht₁₂.le hτc
  have hτJ : ∀ s ∈ J, τ s ∈ Ioo (τ t₁) (τ t₂) := fun s hs =>
    ⟨hmono (left_mem_Icc.2 ht₁₂.le) (Ioo_subset_Icc_self hs) hs.1,
      hmono (Ioo_subset_Icc_self hs) (right_mem_Icc.2 ht₁₂.le) hs.2⟩
  have hgmono : StrictMonoOn ginv (τ '' J) := by
    rintro _ ⟨s₁, hs₁, rfl⟩ _ ⟨s₂, hs₂, rfl⟩ h
    rw [hleft s₁ hs₁, hleft s₂ hs₂]
    by_contra h'
    exact absurd h (not_lt.2 (hmono.monotoneOn (Ioo_subset_Icc_self hs₂)
      (Ioo_subset_Icc_self hs₁) (not_lt.1 h')))
  have hgd : ∀ s ∈ J, HasDerivAt ginv (fderiv ℝ ϱ (σ s) (deriv σ s))⁻¹ (τ s) := fun s hs => by
    have hnhds : τ '' J ∈ 𝓝 (τ s) := mem_of_superset (Ioo_mem_nhds (hτJ s hs).1 (hτJ s hs).2)
      hIoo
    have hcont : ContinuousAt ginv (τ s) := by
      refine hgmono.continuousAt_of_image_mem_nhds hnhds ?_
      rw [hinj.leftInvOn_invFunOn.image_image, hleft s hs]
      exact isOpen_Ioo.mem_nhds hs
    refine HasDerivAt.of_local_left_inverse (f := τ) hcont ?_
      (hpos s (Ioo_subset_Icc_self hs)).ne' ?_
    · rw [hleft s hs]
      exact hτd s (hsub (Ioo_subset_Icc_self hs))
    · filter_upwards [hnhds] with y hy
      exact invFunOn_eq hy
  have hIcc : Icc (τ a) (τ e) ⊆ τ '' J := fun y hy => hIoo
    ⟨(hmono (left_mem_Icc.2 ht₁₂.le) ⟨ha.le, hae.trans he.le⟩ ha).trans_le hy.1,
      hy.2.trans_lt (hmono ⟨ha.le.trans hae, he.le⟩ (right_mem_Icc.2 ht₁₂.le) he)⟩
  have hsol : Facts.IsODESolution (zField Zh) T 0 (fun y => σ (ginv y)) (Icc (τ a) (τ e)) := {
    interval := ordConnected_Icc
    mem := fun y hy => by
      obtain ⟨s, hs, rfl⟩ := hIcc hy
      rw [hleft s hs]
      exact himage (mem_image_of_mem σ (Ioo_subset_Icc_self hs))
    deriv := fun y hy => by
      obtain ⟨s, hs, rfl⟩ := hIcc hy
      have h1 : HasDerivAt σ (deriv σ s) (ginv (τ s)) := by
        rw [hleft s hs]; exact hσd s (hsub (Ioo_subset_Icc_self hs))
      refine (h1.scomp (τ s) (hgd s hs)).hasDerivWithinAt.congr_deriv ?_
      simp only [zField, hleft s hs, hZh s (Ioo_subset_Icc_self hs)] }
  intro s hs
  have haJ : a ∈ J := ⟨ha, hae.trans_lt he⟩
  have hsJ : s ∈ J := ⟨ha.trans_le hs.1, hs.2.trans_lt he⟩
  have hτs : τ s ∈ Icc (τ a) (τ e) :=
    ⟨hmono.monotoneOn (Ioo_subset_Icc_self haJ) (Ioo_subset_Icc_self hsJ) hs.1,
      hmono.monotoneOn (Ioo_subset_Icc_self hsJ) ⟨ha.le.trans hae, he.le⟩ hs.2⟩
  have := hD.flow.mem_of_sol (mem_univ _) hsol hτs (left_mem_Icc.2 (hτs.1.trans hτs.2))
  simp only [hleft s hsJ, hleft a haJ] at this
  exact this

/-- `-g(dφ, du) = du(Z)` for `Z = -grad φ`. -/
theorem neg_coform_eq_fderiv {g : MatrixField n} {x : E n} (hsymm : (g x)ᵀ = g x)
    (φ u : E n → ℝ) : -coform g x (d φ x) (d u x) = fderiv ℝ u x (-grad g φ x) := by
  have hinv : ∀ j k, (g x)⁻¹ j k = (g x)⁻¹ k j := fun j k => by
    have := congrFun (congrFun (Matrix.transpose_nonsing_inv (g x)) k) j
    rw [hsymm] at this
    simpa [Matrix.transpose_apply] using this
  have hG : ∀ k, grad g φ x k = ∑ j, (g x)⁻¹ k j * d φ x j := fun k => by simp [grad_def]
  rw [map_neg, fderiv_apply_eq_sum_d, neg_inj]
  simp only [coform_def, hG]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hinv]

/-- **Flow box and transport equations** (`lem_onesided`, first two steps), from the hypotheses of
`IsEmission` that they use: the cut-off `θ` near `σ(t)`, the solutions `bk` of the transport
hierarchy on the flow box `Bx`, the cut-off `χ`, and the neighbourhood `V` of `σ(1)`. -/
theorem exists_transport_of_emission {g : MatrixField n} {Y : E n → E n} (hg : IsSpacetime g Y)
    {σ : ℝ → E n} {b t₁ t₂ : ℝ} {T : Set (E n)} {φ : E n → ℝ}
    (hσ : ∃ I, IsGeodesic g σ I ∧ Icc 0 b ⊆ I)
    (hσf : ∀ t ∈ Icc 0 b, IsFutureCausal g Y (σ t) (deriv σ t))
    (ht₁ : 0 < t₁) (ht₂ : t₂ < b) (h1t₂ : 1 < t₂) (hT : IsOpen T) (hφ : ContDiffOn ℝ ∞ φ T)
    (hZ : ∀ x ∈ T, IsFutureCausal g Y x (-grad g φ x)) (himage : σ '' Icc t₁ t₂ ⊆ T)
    (htangent : ∀ t ∈ Icc t₁ t₂, ∃ c : ℝ, 0 < c ∧ -grad g φ (σ t) = c • deriv σ t)
    {t : ℝ} (ht : t ∈ Ioo t₁ 1) {N : Set (E n)} (hN : IsOpen N) (htN : σ t ∈ N) :
    ∃ (θ : E n → ℝ) (Bx : Set (E n)) (bk : ℕ → E n → ℝ) (χ ϱ : E n → ℝ) (ϱout : ℝ)
      (V : Set (E n)), ContDiff ℝ ∞ θ ∧ HasCompactSupport θ ∧ tsupport θ ⊆ N ∩ T ∧
      (∀ x, 0 ≤ θ x) ∧ 0 < θ (σ t) ∧ σ 1 ∈ V ∧
      IsOpen Bx ∧ Bx ⊆ T ∧ (∀ k, ContDiffOn ℝ ∞ (bk k) Bx) ∧
      (∀ x ∈ Bx, 2 * -coform g x (d φ x) (d (bk 0) x) + bk 0 x * box g φ x = θ x) ∧
      (∀ k, ∀ x ∈ Bx, 2 * -coform g x (d φ x) (d (bk (k + 1)) x) +
        bk (k + 1) x * box g φ x = -box g (bk k) x) ∧
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ Bx ∧ IsCauchyTemporal g Y ϱ ∧
      (∀ x ∈ Bx, ϱ x < ϱout → (∃ k, bk k x ≠ 0) → ∀ᶠ y in 𝓝 x, χ y = 1) ∧
      IsOpen V ∧ (∀ x ∈ V, χ x = 1) ∧ (∀ x ∈ V, ϱ x < ϱout) ∧ Disjoint V (tsupport θ) ∧
      ∀ x ∈ V, 0 < bk 0 x := by
  /- The vector field `Ẑ = Z / Zϱ` and its flow. -/
  obtain ⟨ϱ, -, hϱ, -⟩ := Facts.exists_cauchyTemporal hg
  obtain ⟨q, hq_def⟩ : ∃ q : E n → ℝ, ∀ x, q x = fderiv ℝ ϱ x (-grad g φ x) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Zh, hZh_def⟩ : ∃ Zh : E n → E n, ∀ x, Zh x = (q x)⁻¹ • -grad g φ x :=
    ⟨_, fun _ => rfl⟩
  have hq : ∀ x ∈ T, 0 < q x := fun x hx => by rw [hq_def]; exact hϱ.fderiv_pos hg (hZ x hx)
  have hZs : ContDiffOn ℝ ∞ (fun x => -grad g φ x) T :=
    (contDiffOn_grad hg.smooth hg.det_ne_zero hT hφ).neg
  have hqs : ContDiffOn ℝ ∞ q T :=
    ((hϱ.smooth.fderiv_right (m := ∞) (by simp)).contDiffOn.clm_apply hZs).congr
      fun x _ => hq_def x
  have hZhs : ContDiffOn ℝ ∞ Zh T :=
    ((hqs.inv fun x hx => (hq x hx).ne').smul hZs).congr fun x _ => hZh_def x
  have htime : ∀ x ∈ T, fderiv ℝ ϱ x (Zh x) = 1 := fun x hx => by
    rw [hZh_def, map_smul, smul_eq_mul, ← hq_def]
    exact inv_mul_cancel₀ (hq x hx).ne'
  obtain ⟨X, hX⟩ := exists_isFlow (P := ℝ) hT hZhs
  have hD : FlowBoxData T ϱ Zh X := ⟨hT, hϱ.smooth, hZhs, htime, hX⟩
  /- `σ` is a flow line. -/
  obtain ⟨I, hIg, hbI⟩ := hσ
  have hsub0 : Icc t₁ t₂ ⊆ Icc 0 b := fun s hs => ⟨ht₁.le.trans hs.1, hs.2.trans ht₂.le⟩
  have hpos : ∀ s ∈ Icc t₁ t₂, 0 < fderiv ℝ ϱ (σ s) (deriv σ s) := fun s hs =>
    hϱ.fderiv_pos hg (hσf s (hsub0 hs))
  have hZhσ : ∀ s ∈ Icc t₁ t₂, Zh (σ s) = (fderiv ℝ ϱ (σ s) (deriv σ s))⁻¹ • deriv σ s := by
    intro s hs
    obtain ⟨c, hc, hcs⟩ := htangent s hs
    have hc' : (0 : ℝ) < c := hc
    rw [hZh_def, hq_def, hcs, map_smul, smul_eq_mul, smul_smul]
    congr 1
    field_simp [hc'.ne', (hpos s hs).ne']
  set ti := (t₁ + t) / 2
  set tout := (1 + t₂) / 2
  have hti : t₁ < ti := by simp only [ti]; linarith [ht.1]
  have htit : ti < t := by simp only [ti]; linarith [ht.1]
  have htout : 1 < tout := by simp only [tout]; linarith
  have htout₂ : tout < t₂ := by simp only [tout]; linarith
  have ht1 : t < 1 := ht.2
  obtain ⟨hmono, hline⟩ := hD.flowLine_of_tangent hIg.isOpen hIg.smooth (hsub0.trans hbI)
    himage hpos hZhσ (a := ti) (e := tout) hti (by linarith) htout₂
  have hmemI : ∀ s, ti ≤ s → s ≤ tout → s ∈ Icc t₁ t₂ := fun s h1 h2 =>
    ⟨hti.le.trans h1, h2.trans htout₂.le⟩
  have hϱ1 : ϱ (σ ti) < ϱ (σ t) := hmono (hmemI _ le_rfl (by linarith)) (hmemI _ htit.le
    (by linarith)) htit
  have hϱ2 : ϱ (σ t) < ϱ (σ 1) := hmono (hmemI _ htit.le (by linarith)) (hmemI _ (by linarith)
    htout.le) ht1
  have hϱ3 : ϱ (σ 1) < ϱ (σ tout) := hmono (hmemI _ (by linarith) htout.le)
    (hmemI _ (by linarith) le_rfl) htout
  set τin := ϱ (σ ti)
  set ϱout := ϱ (σ tout)
  set c₁ := (τin + ϱ (σ t)) / 2
  have hc₁ : τin < c₁ := by simp only [c₁]; linarith
  have hc₁' : c₁ < ϱ (σ t) := by simp only [c₁]; linarith
  set B := boxSet T ϱ Zh τin
  have hB : IsOpen B := hD.isOpen_boxSet τin
  set π := flowProj ϱ X τin
  have hσB : ∀ s ∈ Icc ti tout, σ s ∈ B ∧ π (σ s) = σ ti := fun s hs => by
    obtain ⟨h1, h2⟩ := hline s hs
    obtain ⟨h3, h4⟩ := hX.flow (hX.self h1).1 h1
    rw [h2] at h3 h4
    rw [(hX.self h1).2] at h4
    exact ⟨⟨himage (mem_image_of_mem σ (hmemI s hs.1 hs.2)), h3⟩, h4⟩
  have hσtB := hσB t ⟨htit.le, by linarith⟩
  have hσ1B := hσB 1 ⟨by linarith, htout.le⟩
  /- The flow lines near `σ(ti)` reach the level `ϱout`. -/
  have htube : ∀ᶠ y in 𝓝 (σ ti), ∀ s ∈ Icc τin ϱout,
      (s, τin, y, (0 : ℝ)) ∈ flowDom (zField Zh) T univ := by
    refine isCompact_Icc.eventually_forall_of_forall_eventually fun s hs => ?_
    have htout' := (hline tout ⟨by linarith, le_rfl⟩).1
    have hm : (s, τin, σ ti, (0 : ℝ)) ∈ flowDom (zField Zh) T univ :=
      IsFlow.mem_of_uIcc (hX.self htout').1 htout' (Icc_subset_uIcc hs)
    exact (continuous_snd.prodMk (continuous_const.prodMk
      (continuous_fst.prodMk continuous_const))).continuousAt.preimage_mem_nhds
      (hX.isOpen.mem_nhds hm)
  /- The source `θ`. -/
  have hπc : ContinuousAt π (σ t) :=
    ((hD.contDiffOn_flowProj τin).contDiffAt (hB.mem_nhds hσtB.1)).continuousAt
  rw [← hσtB.2] at htube
  have hϱc : ContinuousAt ϱ (σ t) := hϱ.smooth.continuous.continuousAt
  have hev : ∀ᶠ x in 𝓝 (σ t), x ∈ N ∧ x ∈ B ∧
      (∀ s ∈ Icc τin ϱout, (s, τin, π x, (0 : ℝ)) ∈ flowDom (zField Zh) T univ) ∧
      c₁ < ϱ x ∧ ϱ x < ϱ (σ 1) := by
    filter_upwards [hN.mem_nhds htN, hB.mem_nhds hσtB.1, hπc.eventually htube,
      hϱc.eventually (lt_mem_nhds hc₁'), hϱc.eventually (gt_mem_nhds hϱ2)] with x h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  let θb : ContDiffBump (σ t) := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  set θ : E n → ℝ := ⇑θb
  have hθW : ∀ x ∈ tsupport θ, x ∈ N ∧ x ∈ B ∧
      (∀ s ∈ Icc τin ϱout, (s, τin, π x, (0 : ℝ)) ∈ flowDom (zField Zh) T univ) ∧
      c₁ < ϱ x ∧ ϱ x < ϱ (σ 1) := fun x hx => by
    rw [θb.tsupport_eq] at hx
    exact hball ((Metric.mem_closedBall.1 hx).trans_lt (by simp only [θb]; linarith))
  have hθt : θ (σ t) = 1 := θb.one_of_mem_closedBall (Metric.mem_closedBall_self θb.rIn_pos.le)
  have hθσt : σ t ∈ tsupport θ := subset_tsupport _ (by simp [hθt])
  /- The compact set `C` swept out by the flow lines through `supp θ`. -/
  set K := π '' tsupport θ
  have hK : IsCompact K := θb.hasCompactSupport.isCompact.image_of_continuousOn
    ((hD.contDiffOn_flowProj τin).continuousOn.mono fun x hx => (hθW x hx).2.1)
  have hKtube : ∀ y ∈ K, ∀ s ∈ Icc τin ϱout,
      (s, τin, y, (0 : ℝ)) ∈ flowDom (zField Zh) T univ := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hθW x hx).2.2.1
  have hKϱ : ∀ y ∈ K, ϱ y = τin := by
    rintro _ ⟨x, hx, rfl⟩
    exact hD.time_flowProj τin (hθW x hx).2.1
  set C := (fun z : E n × ℝ => X (z.2, τin, z.1, 0)) '' (K ×ˢ Icc c₁ ϱout)
  have hzmem : ∀ z ∈ K ×ˢ Icc c₁ ϱout, (z.2, τin, z.1, (0 : ℝ)) ∈ flowDom (zField Zh) T univ :=
    fun z hz => hKtube z.1 hz.1 z.2 ⟨hc₁.le.trans hz.2.1, hz.2.2⟩
  have hC : IsCompact C := (hK.prod isCompact_Icc).image_of_continuousOn fun z hz =>
    ((hX.contDiffAt (hzmem z hz)).continuousAt.comp (f := fun z : E n × ℝ => (z.2, τin, z.1,
      (0 : ℝ))) (continuous_snd.prodMk (continuous_const.prodMk
        (continuous_fst.prodMk continuous_const))).continuousAt).continuousWithinAt
  have hCB : C ⊆ B := by
    rintro _ ⟨z, hz, rfl⟩
    have hm := hzmem z hz
    have hϱz : ϱ (X (z.2, τin, z.1, 0)) = z.2 := by
      rw [hD.time_eq hm, hKϱ z.1 hz.1]; ring
    refine ⟨hX.mem_U hm, ?_⟩
    have := (hX.flow (hX.self hm).1 hm).1
    rw [hϱz]
    exact this
  obtain ⟨χ, hχ, -, hχc, hχB, hχC⟩ := exists_cutoff hC hB hCB
  set O := {x | χ =ᶠ[𝓝 x] 1}
  have hO : IsOpen O := isOpen_setOf_eventually_nhds
  have hCO : C ⊆ O := hχC
  have hχ1 : ∀ x ∈ O, χ x = 1 := fun x hx => hx.eq_of_nhds
  /- The transport hierarchy. -/
  have hBT : B ⊆ T := FlowBoxData.boxSet_subset τin
  have hqB : ∀ x ∈ B, 0 < q x := fun x hx => hq x hx.1
  have h2q : ∀ x ∈ B, 2 * q x ≠ 0 := fun x hx => (mul_pos two_pos (hqB x hx)).ne'
  set a : E n → ℝ := fun x => box g φ x / (2 * q x)
  have ha : ContDiffOn ℝ ∞ a B :=
    ((contDiffOn_box hg.smooth hg.det_ne_zero hT hφ).mono hBT).div
      (contDiffOn_const.mul (hqs.mono hBT)) h2q
  set f₀ : E n → ℝ := fun x => θ x / (2 * q x)
  have hf₀ : ContDiffOn ℝ ∞ f₀ B :=
    θb.contDiff.contDiffOn.div (contDiffOn_const.mul (hqs.mono hBT)) h2q
  set src : (E n → ℝ) → E n → ℝ := fun bp x => -box g bp x / (2 * q x)
  have hsrc : ∀ bp, ContDiffOn ℝ ∞ bp B → ContDiffOn ℝ ∞ (src bp) B := fun bp hbp =>
    (contDiffOn_box hg.smooth hg.det_ne_zero hB hbp).neg.div
      (contDiffOn_const.mul (hqs.mono hBT)) h2q
  classical
  let solve : (E n → ℝ) → E n → ℝ := fun f =>
    if h : ContDiffOn ℝ ∞ f B then (hD.exists_transport τin ha h).choose else 0
  have hsolve : ∀ f (hf : ContDiffOn ℝ ∞ f B),
      solve f = (hD.exists_transport τin ha hf).choose := fun f hf => by simp [solve, hf]
  let bk : ℕ → E n → ℝ := fun k => Nat.rec (solve f₀) (fun _ bp => solve (src bp)) k
  have hbks : ∀ k, bk (k + 1) = solve (src (bk k)) := fun k => rfl
  have hbk_smooth : ∀ k, ContDiffOn ℝ ∞ (bk k) B := by
    intro k
    induction k with
    | zero =>
      have := (hD.exists_transport τin ha hf₀).choose_spec.1
      rwa [← hsolve f₀ hf₀] at this
    | succ k ih =>
      have := (hD.exists_transport τin ha (hsrc _ ih)).choose_spec.1
      rwa [← hsolve _ (hsrc _ ih), ← hbks] at this
  have hspec0 := (hD.exists_transport τin ha hf₀).choose_spec
  rw [← hsolve f₀ hf₀] at hspec0
  obtain ⟨-, htr0, hvan0, hpos0⟩ := hspec0
  have hspecs : ∀ k, (∀ x ∈ B, fderiv ℝ (bk (k + 1)) x (Zh x) + a x * bk (k + 1) x =
      src (bk k) x) ∧ (∀ x ∈ B, (∀ y ∈ B, π y = π x → ϱ y ∈ uIcc τin (ϱ x) →
        src (bk k) y = 0) → bk (k + 1) x = 0) := fun k => by
    have := (hD.exists_transport τin ha (hsrc _ (hbk_smooth k))).choose_spec
    rw [← hsolve _ (hsrc _ (hbk_smooth k)), ← hbks] at this
    exact ⟨this.2.1, this.2.2.1⟩
  have htr : ∀ bb f : E n → ℝ, (∀ x ∈ B, fderiv ℝ bb x (Zh x) + a x * bb x = f x) →
      ∀ x ∈ B, 2 * -coform g x (d φ x) (d bb x) + bb x * box g φ x = 2 * q x * f x := by
    intro bb f h x hx
    have hZq : -grad g φ x = q x • Zh x := by
      rw [hZh_def, smul_smul, mul_inv_cancel₀ (hqB x hx).ne', one_smul]
    rw [neg_coform_eq_fderiv (hg.symm x), ← h x hx, hZq, map_smul, smul_eq_mul]
    simp only [a]
    field_simp [(hqB x hx).ne']
  /- The flow lines missing `supp θ`, and the points below the level `c₁`. -/
  set Ov := (B ∩ π ⁻¹' Kᶜ) ∪ (B ∩ ϱ ⁻¹' Iio c₁)
  have hOv : IsOpen Ov :=
    ((hD.contDiffOn_flowProj τin).continuousOn.isOpen_inter_preimage hB
      hK.isClosed.isOpen_compl).union (hB.inter (isOpen_Iio.preimage hϱ.smooth.continuous))
  have hOvB : Ov ⊆ B := fun x hx => hx.elim (·.1) (·.1)
  have hseg : ∀ x ∈ Ov, ∀ y ∈ B, π y = π x → ϱ y ∈ uIcc τin (ϱ x) → y ∈ Ov := by
    rintro x (⟨-, hxK⟩ | ⟨-, hxc⟩) y hy hπ hϱy
    · exact Or.inl ⟨hy, by simp only [mem_preimage, hπ]; exact hxK⟩
    · refine Or.inr ⟨hy, ?_⟩
      simp only [mem_preimage, mem_Iio] at hxc ⊢
      rcases mem_uIcc.1 hϱy with h | h <;> linarith [h.1, h.2]
  have hθOv : ∀ y ∈ Ov, θ y = 0 := by
    rintro y (⟨-, hyK⟩ | ⟨-, hyc⟩)
    · exact image_eq_zero_of_notMem_tsupport fun h => hyK (mem_image_of_mem π h)
    · exact image_eq_zero_of_notMem_tsupport fun h => lt_asymm (hθW y h).2.2.2.1 hyc
  have hvan : ∀ k, ∀ x ∈ Ov, bk k x = 0 := by
    intro k
    induction k with
    | zero =>
      intro x hx
      exact hvan0 x (hOvB hx) fun y hy hπ hϱy => by
        simp [f₀, hθOv y (hseg x hx y hy hπ hϱy)]
    | succ k ih =>
      intro x hx
      refine (hspecs k).2 x (hOvB hx) fun y hy hπ hϱy => ?_
      have : box g (bk k) y = 0 := box_eq_zero_of_eventuallyEq (by
        filter_upwards [hOv.mem_nhds (hseg x hx y hy hπ hϱy)] with z hz
        exact ih z hz)
      simp [src, this]
  /- The neighbourhood `V` of `σ(1)`. -/
  set V := O ∩ ϱ ⁻¹' Iio ϱout ∩ (tsupport θ)ᶜ ∩ (B ∩ bk 0 ⁻¹' Ioi 0)
  have hV : IsOpen V :=
    ((hO.inter (isOpen_Iio.preimage hϱ.smooth.continuous)).inter
      (isClosed_tsupport _).isOpen_compl).inter
      ((hbk_smooth 0).continuousOn.isOpen_inter_preimage hB isOpen_Ioi)
  have hσ1C : σ 1 ∈ C :=
    ⟨(σ ti, ϱ (σ 1)), ⟨⟨σ t, hθσt, hσtB.2⟩, ⟨by linarith, hϱ3.le⟩⟩,
      (hline 1 ⟨by linarith, htout.le⟩).2⟩
  have hf₀0 : ∀ y ∈ B, 0 ≤ f₀ y := fun y hy =>
    div_nonneg (θb.nonneg) (mul_pos two_pos (hqB y hy)).le
  have hσ1V : σ 1 ∈ V := by
    refine ⟨⟨⟨hCO hσ1C, hϱ3⟩, fun h => lt_irrefl _ (hθW _ h).2.2.2.2⟩, hσ1B.1, ?_⟩
    refine hpos0 hf₀0 (σ 1) hσ1B.1 (σ t) hσtB.1 (hσtB.2.trans hσ1B.2.symm) hϱ1.le hϱ2 ?_
    simp only [f₀, hθt]
    exact div_pos one_pos (mul_pos two_pos (hqB _ hσtB.1))
  refine ⟨θ, B, bk, χ, ϱ, ϱout, V, θb.contDiff, θb.hasCompactSupport,
    fun x hx => ⟨(hθW x hx).1, hBT (hθW x hx).2.1⟩, fun x => θb.nonneg, by rw [hθt]; exact one_pos,
    hσ1V, hB, hBT, hbk_smooth, fun x hx => ?_, fun k x hx => ?_, hχ, hχc, hχB, hϱ,
    fun x hx hϱx => ?_, hV, fun x hx => hχ1 x hx.1.1.1, fun x hx => hx.1.1.2,
    Set.disjoint_left.2 fun x hx hxθ => hx.1.2 hxθ, fun x hx => hx.2.2⟩
  · refine (htr (bk 0) _ htr0 x hx).trans ?_
    simp only [f₀]
    field_simp [(hqB x hx).ne']
  · refine (htr (bk (k + 1)) _ (hspecs k).1 x hx).trans ?_
    simp only [src]
    field_simp [(hqB x hx).ne']
  · rintro ⟨k, hk⟩
    have hxK : π x ∈ K := by
      by_contra h
      exact hk (hvan k x (Or.inl ⟨hx, h⟩))
    have hxc : c₁ ≤ ϱ x := by
      by_contra h
      exact hk (hvan k x (Or.inr ⟨hx, not_le.1 h⟩))
    have hxC : x ∈ C := ⟨(π x, ϱ x), ⟨hxK, hxc, hϱx.le⟩, (hD.eq_flow_flowProj τin hx).2⟩
    exact eventually_of_mem (hO.mem_nhds (hCO hxC)) hχ1

end

end LorentzianCalderon
