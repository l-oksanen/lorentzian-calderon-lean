module

public import LorentzianCalderon.Waves.Jump
public import LorentzianCalderon.Local.Energy.Calculus

public section

/-!
# Calculus lemmas for progressing waves

Smoothness of functions defined on open sets and of families depending on a parameter `s`,
Hadamard's lemma for functions vanishing on the graph `{s = φ(x)}`, and points of a level set
of a function with nonvanishing differential as limits from below.
-/

namespace LorentzianCalderon

noncomputable section
open MeasureTheory Set Filter Function
open scoped ContDiff Topology

variable {n : ℕ}

/-! ### Localization -/

/-- A function smooth on an open set agrees near each of its points with a smooth function. -/
theorem exists_contDiff_eventuallyEq {V : Set (E n)} (hV : IsOpen V) {u : E n → ℝ}
    (hu : ContDiffOn ℝ ∞ u V) {x : E n} (hx : x ∈ V) :
    ∃ v : E n → ℝ, ContDiff ℝ ∞ v ∧ v =ᶠ[𝓝 x] u := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV x hx
  let β : ContDiffBump x := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  have hβV : tsupport β ⊆ V := by
    rw [β.tsupport_eq]
    exact (Metric.closedBall_subset_ball (show ε / 2 < ε by linarith)).trans hball
  refine ⟨fun y => β y * u y, contDiff_mul_of_tsupport_subset hV β.contDiff hβV hu, ?_⟩
  filter_upwards [Metric.ball_mem_nhds x (by positivity : 0 < ε / 4)] with y hy
  rw [β.one_of_mem_closedBall (Metric.ball_subset_closedBall hy), one_mul]

/-- A function is smooth on an open set if near each point it agrees with a smooth function. -/
theorem contDiffOn_of_locally {V : Set (E n)} {f : E n → ℝ}
    (h : ∀ x ∈ V, ∃ v : E n → ℝ, ContDiff ℝ ∞ v ∧ v =ᶠ[𝓝 x] f) : ContDiffOn ℝ ∞ f V :=
  fun x hx => by
    obtain ⟨v, hv, hvf⟩ := h x hx
    exact (hv.contDiffAt.congr_of_eventuallyEq hvf.symm).contDiffWithinAt

variable {g : MatrixField n}

theorem contDiffOn_box (hg : ∀ i j, ContDiff ℝ ∞ fun x => g x i j)
    (hdet : ∀ x, (g x).det ≠ 0) {V : Set (E n)} (hV : IsOpen V) {u : E n → ℝ}
    (hu : ContDiffOn ℝ ∞ u V) : ContDiffOn ℝ ∞ (box g u) V :=
  contDiffOn_of_locally fun x hx => by
    obtain ⟨v, hv, hvu⟩ := exists_contDiff_eventuallyEq hV hu hx
    exact ⟨box g v, contDiff_box hg hdet hv, by
      filter_upwards [hvu.eventuallyEq_nhds] with y hy
      exact box_congr hy⟩

/-! ### Families depending on a parameter -/

/-- The partial differential of a smooth family is smooth in both variables. -/
theorem contDiff_d_param {u : ℝ → E n → ℝ} (hu : ContDiff ℝ ∞ fun p : ℝ × E n => u p.1 p.2)
    (j : Fin (n + 1)) : ContDiff ℝ ∞ fun p : ℝ × E n => d (u p.1) p.2 j := by
  have h : ContDiff ℝ ∞ (Function.uncurry fun (p : ℝ × E n) (y : E n) => u p.1 y) :=
    hu.comp (contDiff_fst.fst.prodMk contDiff_snd)
  simp only [d_def]
  exact (h.fderiv (g := fun p : ℝ × E n => p.2) contDiff_snd (by simp)).clm_apply contDiff_const

/-- Cut-off of a family smooth on `ℝ × V` by a function supported in `V`. -/
theorem contDiff_mul_param {V : Set (E n)} (hV : IsOpen V) {χ : E n → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχV : tsupport χ ⊆ V) {f : ℝ → E n → ℝ}
    (hf : ContDiffOn ℝ ∞ (fun p : ℝ × E n => f p.1 p.2) (univ ×ˢ V)) :
    ContDiff ℝ ∞ fun p : ℝ × E n => χ p.2 * f p.1 p.2 := by
  refine contDiff_iff_contDiffAt.2 fun p => ?_
  by_cases hp : p.2 ∈ V
  · exact (hχ.comp contDiff_snd).contDiffAt.mul
      (hf.contDiffAt ((isOpen_univ.prod hV).mem_nhds ⟨mem_univ _, hp⟩))
  · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    have h0 := notMem_tsupport_iff_eventuallyEq.1 fun h => hp (hχV h)
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds h0] with q hq
    simp [show χ q.2 = 0 from hq]

/-- The family `B(x, φ(x) - s)`. -/
theorem contDiffOn_comp_sub {V : Set (E n)} {φ : E n → ℝ} (hφ : ContDiffOn ℝ ∞ φ V)
    {B : E n → ℝ → ℝ} (hB : ContDiffOn ℝ ∞ (fun q : E n × ℝ => B q.1 q.2) (V ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E n => B p.2 (φ p.2 - p.1)) (univ ×ˢ V) := by
  have h1 : ContDiffOn ℝ ∞ (fun p : ℝ × E n => φ p.2) (univ ×ˢ V) :=
    hφ.comp contDiff_snd.contDiffOn fun p hp => hp.2
  exact hB.comp (contDiff_snd.contDiffOn.prodMk (h1.sub contDiff_fst.contDiffOn))
    fun p hp => ⟨hp.2, mem_univ _⟩

/-! ### Hadamard's lemma -/

section Parametric

variable {P G : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup G]
  [NormedSpace ℝ G] [CompleteSpace G]

omit [FiniteDimensional ℝ P] [CompleteSpace G] in
/-- The partial derivative in the parameter of a function `k(p, t)` that is `C¹` jointly. -/
theorem hasFDerivAt_param {W : Set P} (hW : IsOpen W) {k : P → ℝ → G}
    (hk : ContDiffOn ℝ 1 (fun q : P × ℝ => k q.1 q.2) (W ×ˢ univ)) {p : P} (hp : p ∈ W) (t : ℝ) :
    HasFDerivAt (fun x => k x t)
      ((fderiv ℝ (fun q : P × ℝ => k q.1 q.2) (p, t)).comp (ContinuousLinearMap.inl ℝ P ℝ)) p := by
  have hd : DifferentiableAt ℝ (fun q : P × ℝ => k q.1 q.2) (p, t) :=
    (hk.contDiffAt ((hW.prod isOpen_univ).mem_nhds ⟨hp, mem_univ _⟩)).differentiableAt one_ne_zero
  have hi : HasFDerivAt (fun x : P => (x, t)) (ContinuousLinearMap.inl ℝ P ℝ) p :=
    (hasFDerivAt_id p).prodMk (hasFDerivAt_const t p)
  exact hd.hasFDerivAt.comp p hi
omit [CompleteSpace G] in

/-- Differentiation under the integral sign over `[0, 1]`. -/
theorem hasFDerivAt_integral_param {W : Set P} (hW : IsOpen W) {k : P → ℝ → G}
    (hk : ContDiffOn ℝ 1 (fun q : P × ℝ => k q.1 q.2) (W ×ˢ univ)) {p : P} (hp : p ∈ W) :
    HasFDerivAt (fun x => ∫ t in (0 : ℝ)..1, k x t)
      (∫ t in (0 : ℝ)..1,
        (fderiv ℝ (fun q : P × ℝ => k q.1 q.2) (p, t)).comp (ContinuousLinearMap.inl ℝ P ℝ)) p := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hW p hp
  have hcb : Metric.closedBall p (ε / 2) ⊆ W :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hWU : IsOpen (W ×ˢ (univ : Set ℝ)) := hW.prod isOpen_univ
  have hcont : ContinuousOn (fun q : P × ℝ => k q.1 q.2) (W ×ˢ univ) := hk.continuousOn
  have hcont' : ContinuousOn (fun q : P × ℝ =>
      (fderiv ℝ (fun q : P × ℝ => k q.1 q.2) q).comp (ContinuousLinearMap.inl ℝ P ℝ))
      (W ×ˢ univ) :=
    ((ContinuousLinearMap.compL ℝ P (P × ℝ) G).flip
      (ContinuousLinearMap.inl ℝ P ℝ)).continuous.comp_continuousOn
      (hk.continuousOn_fderiv_of_isOpen hWU le_rfl)
  have hKc : IsCompact (Metric.closedBall p (ε / 2) ×ˢ Icc (0 : ℝ) 1) :=
    (isCompact_closedBall _ _).prod isCompact_Icc
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn
    (hcont'.mono (prod_mono hcb (subset_univ _)))
  have hslice : ∀ x ∈ W, Continuous fun t => k x t := fun x hx =>
    continuous_iff_continuousAt.2 fun t =>
      (hcont.continuousAt (hWU.mem_nhds ⟨hx, mem_univ _⟩)).comp
        (continuous_const.prodMk continuous_id).continuousAt
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume)
    (F := fun x t => k x t) (a := 0) (b := 1)
    (F' := fun x t => (fderiv ℝ (fun q : P × ℝ => k q.1 q.2) (x, t)).comp
      (ContinuousLinearMap.inl ℝ P ℝ))
    (s := Metric.ball p (ε / 2)) (bound := fun _ => C) (Metric.ball_mem_nhds p (by linarith))
    ?_ ?_ ?_ ?_ intervalIntegrable_const ?_
  · filter_upwards [hW.mem_nhds hp] with x hx
    exact (hslice x hx).aestronglyMeasurable
  · exact (hslice p hp).intervalIntegrable _ _
  · exact (ContinuousOn.aestronglyMeasurable (hcont'.comp
      (continuous_const.prodMk continuous_id).continuousOn fun t _ => ⟨hp, mem_univ t⟩)
      measurableSet_uIoc)
  · refine Eventually.of_forall fun t ht x hx => ?_
    rw [uIoc_of_le zero_le_one] at ht
    exact hC (x, t) ⟨Metric.ball_subset_closedBall hx, Ioc_subset_Icc_self ht⟩
  · exact Eventually.of_forall fun t _ x hx =>
      hasFDerivAt_param hW hk (hcb (Metric.ball_subset_closedBall hx)) t

/-- Smooth dependence of `∫₀¹ k(p, t) dt` on the parameter `p`. -/
theorem contDiffOn_integral_param {W : Set P} (hW : IsOpen W) :
    ∀ (m : ℕ) {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
      {k : P → ℝ → G}, ContDiffOn ℝ ∞ (fun q : P × ℝ => k q.1 q.2) (W ×ˢ univ) →
      ContDiffOn ℝ m (fun x => ∫ t in (0 : ℝ)..1, k x t) W := by
  intro m
  induction m with
  | zero =>
    intro G _ _ _ k hk
    exact contDiffOn_zero.2 fun x hx =>
      (hasFDerivAt_integral_param hW (hk.of_le (by simp)) hx).continuousAt.continuousWithinAt
  | succ m ih =>
    intro G _ _ _ k hk
    have hWU : IsOpen (W ×ˢ (univ : Set ℝ)) := hW.prod isOpen_univ
    have hk1 := hk.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
    rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 by push_cast; rfl,
      contDiffOn_succ_iff_fderiv_of_isOpen hW]
    refine ⟨fun x hx =>
      (hasFDerivAt_integral_param hW hk1 hx).differentiableAt.differentiableWithinAt,
      fun h => absurd h (by simp), ?_⟩
    have hk' : ContDiffOn ℝ ∞ (fun q : P × ℝ =>
        (fderiv ℝ (fun q : P × ℝ => k q.1 q.2) q).comp (ContinuousLinearMap.inl ℝ P ℝ))
        (W ×ˢ univ) :=
      ((ContinuousLinearMap.compL ℝ P (P × ℝ) G).flip
        (ContinuousLinearMap.inl ℝ P ℝ)).contDiff.comp_contDiffOn
        (hk.fderiv_of_isOpen hWU (by simp))
    refine (ih (k := fun x t =>
      (fderiv ℝ (fun q : P × ℝ => k q.1 q.2) (x, t)).comp (ContinuousLinearMap.inl ℝ P ℝ))
      hk').congr fun x hx => ?_
    exact (hasFDerivAt_integral_param hW hk1 hx).fderiv

theorem contDiffOn_integral_param_infty {W : Set P} (hW : IsOpen W) {k : P → ℝ → G}
    (hk : ContDiffOn ℝ ∞ (fun q : P × ℝ => k q.1 q.2) (W ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun x => ∫ t in (0 : ℝ)..1, k x t) W :=
  contDiffOn_infty.2 fun m => contDiffOn_integral_param hW m hk

end Parametric

/-- **Hadamard's lemma** with parameters: a smooth function of `(s, x)` vanishing on the graph
`s = φ(x)` is `(φ(x) - s)` times a smooth function. -/
theorem exists_eq_sub_mul_of_eq_zero {V : Set (E n)} (hV : IsOpen V) {φ : E n → ℝ}
    (hφ : ContDiffOn ℝ ∞ φ V) {f : ℝ → E n → ℝ}
    (hf : ContDiffOn ℝ ∞ (fun p : ℝ × E n => f p.1 p.2) (univ ×ˢ V))
    (h0 : ∀ x ∈ V, f (φ x) x = 0) :
    ∃ c : ℝ → E n → ℝ, ContDiffOn ℝ ∞ (fun p : ℝ × E n => c p.1 p.2) (univ ×ˢ V) ∧
      ∀ s, ∀ x ∈ V, f s x = (φ x - s) * c s x := by
  set W : Set (ℝ × E n) := univ ×ˢ V
  have hW : IsOpen W := isOpen_univ.prod hV
  set F : ℝ × E n → ℝ := fun p => f p.1 p.2
  set D : ℝ × E n → ℝ := fun q => fderiv ℝ F q (1, 0)
  have hD : ContDiffOn ℝ ∞ D W :=
    (hf.fderiv_of_isOpen hW (by simp)).clm_apply contDiffOn_const
  set γ : ℝ × E n → ℝ → ℝ × E n := fun p t => (φ p.2 + t * (p.1 - φ p.2), p.2)
  have hγ : ContDiffOn ℝ ∞ (fun q : (ℝ × E n) × ℝ => γ q.1 q.2) (W ×ˢ univ) := by
    have hφ2 : ContDiffOn ℝ ∞ (fun q : (ℝ × E n) × ℝ => φ q.1.2) (W ×ˢ univ) :=
      hφ.comp (contDiff_snd.comp contDiff_fst).contDiffOn fun q hq => hq.1.2
    exact (hφ2.add (contDiff_snd.contDiffOn.mul
      ((contDiff_fst.comp contDiff_fst).contDiffOn.sub hφ2))).prodMk
      (contDiff_snd.comp contDiff_fst).contDiffOn
  have hγW : ∀ p ∈ W, ∀ t, γ p t ∈ W := fun p hp t => ⟨mem_univ _, hp.2⟩
  refine ⟨fun s x => -∫ t in (0 : ℝ)..1, D (γ (s, x) t), ?_, fun s x hx => ?_⟩
  · have := contDiffOn_integral_param_infty hW (k := fun p t => D (γ p t))
      (hD.comp hγ fun q hq => hγW q.1 hq.1 q.2)
    exact this.neg
  · have hp : (s, x) ∈ W := ⟨mem_univ _, hx⟩
    have hderiv : ∀ t, HasDerivAt (fun t => F (γ (s, x) t)) ((s - φ x) * D (γ (s, x) t)) t := by
      intro t
      have h1 : HasDerivAt (γ (s, x)) ((s - φ x, 0) : ℝ × E n) t := by
        have := ((hasDerivAt_id t).mul_const (s - φ x)).const_add (φ x)
        simpa [γ] using this.prodMk (hasDerivAt_const t x)
      have h2 : HasFDerivAt F (fderiv ℝ F (γ (s, x) t)) (γ (s, x) t) :=
        ((hf.contDiffAt (hW.mem_nhds (hγW _ hp t))).differentiableAt (by simp)).hasFDerivAt
      have := h2.comp_hasDerivAt t h1
      rw [show ((s - φ x, 0) : ℝ × E n) = (s - φ x) • ((1, 0) : ℝ × E n) by simp, map_smul,
        smul_eq_mul] at this
      exact this
    have hcontD : Continuous fun t => D (γ (s, x) t) :=
      continuous_iff_continuousAt.2 fun t =>
        (hD.continuousOn.continuousAt (hW.mem_nhds (hγW _ hp t))).comp
          (by fun_prop : Continuous (γ (s, x))).continuousAt
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
      ((continuous_const.mul hcontD).intervalIntegrable 0 1)
    simp only [γ, one_mul, zero_mul, add_zero, add_sub_cancel, F] at hftc
    rw [h0 x hx, sub_zero, intervalIntegral.integral_const_mul] at hftc
    rw [← hftc]
    ring

/-! ### Level sets -/

/-- A point where `dφ ≠ 0` is a limit of points of a neighbourhood with smaller values of `φ`. -/
theorem mem_closure_lt_of_fderiv_ne_zero {V : Set (E n)} {φ : E n → ℝ} {x : E n}
    (hV : V ∈ 𝓝 x) (hφ : DifferentiableAt ℝ φ x) (hdφ : fderiv ℝ φ x ≠ 0) :
    x ∈ closure (V ∩ {y | φ y < φ x}) := by
  obtain ⟨w, hw⟩ : ∃ w, fderiv ℝ φ x w ≠ 0 := by
    by_contra! h
    exact hdφ (ContinuousLinearMap.ext h)
  set v : E n := -(fderiv ℝ φ x w)⁻¹ • w
  have hv : fderiv ℝ φ x v = -1 := by simp [v, hw]
  have hline : HasDerivAt (fun t : ℝ => φ (x + t • v)) (-1) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
    have hφ' : HasFDerivAt φ (fderiv ℝ φ x) (x + (0 : ℝ) • v) := by
      simpa using hφ.hasFDerivAt
    have := hφ'.comp_hasDerivAt (0 : ℝ) h1
    rw [hv] at this
    exact this
  have hslope := hline.tendsto_slope_zero_right
  have hpath : Tendsto (fun t : ℝ => x + t • v) (𝓝[>] 0) (𝓝 x) := by
    have : Continuous fun t : ℝ => x + t • v := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto hpath ?_
  filter_upwards [hpath hV, hslope (Iio_mem_nhds (show (-1 : ℝ) < 0 by norm_num)),
    self_mem_nhdsWithin] with t htV hts (ht : 0 < t)
  refine ⟨htV, ?_⟩
  simp only [mem_preimage, mem_Iio, zero_add, zero_smul, add_zero, smul_eq_mul] at hts
  have h2 : φ (x + t • v) - φ x < 0 := by
    by_contra! h
    exact (not_lt.2 (mul_nonneg (inv_nonneg.2 ht.le) h)) hts
  show φ (x + t • v) < φ x
  linarith

end

end LorentzianCalderon
