module

public import LorentzianCalderon.Local.Step.Basic

public section

/-!
# The local continuation step: the lens

Step 0 of `prop_local_step`. With `ψ̃ = ψ - |x - q₀|²` (Euclidean norm), on a small ball
`B(q₀, R)` the map `Ψ` has invertible differential, `κ > 1/2`, and `ψ̃` is temporal. For
`0 ≤ ρ < R` the lens `L_ρ = {x ∈ B(q₀, R) | ψ x ≤ τ, τ - ρ² ≤ ψ̃ x}` lies in the closed ball of
radius `ρ` and is compact. With `r = R / 2`, the open set
`V° = {x ∈ B(q₀, r) | τ - r² < ψ̃ x}` contains `q₀`, and `V° ∩ {ψ < τ}` is contained in `L_r` and
has full measure in it.
-/

namespace LorentzianCalderon

noncomputable section
open Set Matrix Filter Metric MeasureTheory
open scoped ContDiff Topology

variable {n : ℕ} {ι : Type*}

section Lorentz

variable {g : MatrixField n} {Y : E n → E n} {x : E n}

/-- An eikonal covector of future type and a temporal covector have negative inner product. -/
theorem coform_neg_of_future {ψ φ : E n → ℝ} (hL : IsLorentzian (g x))
    (hY : form (g x) (Y x) (Y x) < 0) (hψ : IsFutureTimelike g Y x (-grad g ψ x))
    (hφ : IsFutureCausal g Y x (-grad g φ x)) : coform g x (d φ x) (d ψ x) < 0 := by
  have hB := hL.isLorentzForm_inv
  have hT : bil (g x)⁻¹ (timeCovector g Y x) (timeCovector g Y x) < 0 := by
    rw [← coform_eq_bil, coform_timeCovector hL]; exact hY
  have h1 : bil (g x)⁻¹ (d ψ x) (d ψ x) < 0 := by
    rw [← coform_eq_bil]; exact coform_self_neg_of_future hL hψ
  have h2 : bil (g x)⁻¹ (d ψ x) (timeCovector g Y x) < 0 := by
    have := hψ.future; rwa [form_neg_grad_time hL, coform_eq_bil] at this
  have h3 : bil (g x)⁻¹ (d φ x) (d φ x) ≤ 0 := by
    have := hφ.causal; rwa [form_neg_grad hL, coform_eq_bil] at this
  have h4 : bil (g x)⁻¹ (d φ x) (timeCovector g Y x) < 0 := by
    have := hφ.future; rwa [form_neg_grad_time hL, coform_eq_bil] at this
  rw [coform_eq_bil]
  exact hB.neg_of_sameCone hT h3 h4 h1 h2

theorem fderiv_neg_grad (f ψ : E n → ℝ) :
    fderiv ℝ f x (-grad g ψ x) = -coform g x (d f x) (d ψ x) := by
  rw [fderiv_apply_eq_sum_d, coform_def]
  have : ∀ i, (-grad g ψ x) i = -∑ k, (g x)⁻¹ i k * d ψ x k := fun i => by
    rw [grad_def]; rfl
  simp only [this, neg_mul, Finset.sum_neg_distrib, neg_inj, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end Lorentz

section Closure

/-- A point where two functions increase in a common direction is a limit of points where both
are larger. -/
theorem mem_closure_of_fderiv_pos {f₁ f₂ : E n → ℝ} {x v : E n}
    (h₁ : DifferentiableAt ℝ f₁ x) (h₂ : DifferentiableAt ℝ f₂ x)
    (hv₁ : 0 < fderiv ℝ f₁ x v) (hv₂ : 0 < fderiv ℝ f₂ x v) {O : Set (E n)} (hO : O ∈ 𝓝 x) :
    x ∈ closure {y | y ∈ O ∧ f₁ x < f₁ y ∧ f₂ x < f₂ y} := by
  have hℓ : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have ht : Tendsto (fun t : ℝ => x + t • v) (𝓝[>] 0) (𝓝 x) := by
    have := hℓ.continuousAt.tendsto
    simp only [zero_smul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hpos : ∀ {f : E n → ℝ}, DifferentiableAt ℝ f x → 0 < fderiv ℝ f x v →
      ∀ᶠ t in 𝓝[>] (0 : ℝ), f x < f (x + t • v) := by
    intro f hf hv
    have hd : HasDerivAt (fun t : ℝ => f (x + t • v)) (fderiv ℝ f x v) 0 := by
      exact hf.hasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) hℓ (by simp)
    have := hd.tendsto_slope_zero_right
    filter_upwards [this.eventually (lt_mem_nhds hv), self_mem_nhdsWithin] with t h1 h2
    simp only [zero_add, zero_smul, add_zero, smul_eq_mul] at h1
    have h2' : (0 : ℝ) < t := h2
    have h3 := mul_pos h2' h1
    rw [← mul_assoc, mul_inv_cancel₀ h2'.ne', one_mul] at h3
    linarith
  refine mem_closure_of_tendsto ht ?_
  filter_upwards [ht.eventually hO, hpos h₁ hv₁, hpos h₂ hv₂] with t h1 h2 h3
  exact ⟨h1, h2, h3⟩

/-- A function continuous at `x` that vanishes on a set accumulating at `x` vanishes at `x`. -/
theorem eq_zero_of_mem_closure {X : Type*} [TopologicalSpace X] {f : X → ℝ} {x : X}
    {O : Set X} (hf : ContinuousAt f x) (h0 : ∀ y ∈ O, f y = 0) (hx : x ∈ closure O) :
    f x = 0 := by
  have := mem_closure_image hf hx
  have hs : f '' O ⊆ {0} := by
    rintro _ ⟨y, hy, rfl⟩; exact h0 y hy
  have := closure_mono hs this
  simpa using this

/-- A `C¹` function vanishing on an open set has vanishing value and differential at the points
of its closure. -/
theorem eq_zero_and_fderiv_of_mem_closure {f : E n → ℝ} {U O : Set (E n)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) (hO : IsOpen O) (h0 : ∀ y ∈ O, f y = 0) {x : E n} (hx : x ∈ U)
    (hxc : x ∈ closure O) : f x = 0 ∧ fderiv ℝ f x = 0 := by
  refine ⟨eq_zero_of_mem_closure (hf.continuousOn.continuousAt (hU.mem_nhds hx)) h0 hxc, ?_⟩
  have hc : ContinuousAt (fderiv ℝ f) x :=
    (hf.continuousOn_fderiv_of_isOpen hU le_rfl).continuousAt (hU.mem_nhds hx)
  have := mem_closure_image hc hxc
  have hs : fderiv ℝ f '' O ⊆ {0} := by
    rintro _ ⟨y, hy, rfl⟩
    have : f =ᶠ[𝓝 y] fun _ => 0 := Filter.eventually_of_mem (hO.mem_nhds hy) h0
    simp [this.fderiv_eq]
  simpa using closure_mono hs this

end Closure

namespace StepData

/-- `ψ̃ = ψ - |x - q₀|²`. -/
def ψt (S : StepData n ι) (x : E n) : ℝ := S.ψ x - ‖x - S.q₀‖ ^ 2

theorem ψt_def (S : StepData n ι) (x : E n) :
    ψt S x =
      S.ψ x - ‖x - S.q₀‖ ^ 2 := by rfl

/-- The ball `B(q₀, R)` on which `Ψ` has invertible differential, `κ > 1/2` and `ψ̃` is
temporal. -/
structure Ball (S : StepData n ι) (R : ℝ) : Prop where
  pos : 0 < R
  subset : ball S.q₀ R ⊆ S.V
  det : ∀ x ∈ ball S.q₀ R, (D S.Ψ x).det ≠ 0
  κ_pos : ∀ x ∈ ball S.q₀ R, 1 / 2 < S.κ x
  temporal : ∀ x ∈ ball S.q₀ R, IsFutureTimelike S.g S.Y x (-grad S.g S.ψt x)

/-- The lens `L_ρ = {x ∈ B(q₀, R) | ψ x ≤ τ, τ - ρ² ≤ ψ̃ x}`. -/
def L (S : StepData n ι) (R ρ : ℝ) : Set (E n) :=
  {x | x ∈ ball S.q₀ R ∧ S.ψ x ≤ S.τ ∧ S.τ - ρ ^ 2 ≤ S.ψt x}

theorem L_def (S : StepData n ι) (R ρ : ℝ) :
    L S R ρ =
      {x | x ∈ ball S.q₀ R ∧ S.ψ x ≤ S.τ ∧ S.τ - ρ ^ 2 ≤ S.ψt x} := by rfl

theorem mem_L {S : StepData n ι} {R ρ : ℝ} {x} :
    x ∈ L S R ρ ↔ x ∈ ball S.q₀ R ∧ S.ψ x ≤ S.τ ∧ S.τ - ρ ^ 2 ≤ S.ψt x := Iff.rfl

/-- `V° = {x ∈ B(q₀, R/2) | τ - (R/2)² < ψ̃ x}`. -/
def Vo (S : StepData n ι) (R : ℝ) : Set (E n) :=
  {x | x ∈ ball S.q₀ (R / 2) ∧ S.τ - (R / 2) ^ 2 < S.ψt x}

theorem mem_Vo_iff {S : StepData n ι} {R : ℝ} {x} :
    x ∈ Vo S R ↔ x ∈ ball S.q₀ (R / 2) ∧ S.τ - (R / 2) ^ 2 < S.ψt x := Iff.rfl

/-- The part `V° ∩ {ψ < τ}` of the lens `L_{R/2}` below the top. -/
def Vlow (S : StepData n ι) (R : ℝ) : Set (E n) := {x | x ∈ S.Vo R ∧ S.ψ x < S.τ}

theorem mem_Vlow {S : StepData n ι} {R : ℝ} {x} :
    x ∈ Vlow S R ↔ x ∈ S.Vo R ∧ S.ψ x < S.τ := Iff.rfl

variable {S : StepData n ι} (hS : S.Hyp)
include hS

theorem Hyp.differentiableAt_of_contDiffOn {f : E n → ℝ} (hf : ContDiffOn ℝ ∞ f S.V) {x : E n}
    (hx : x ∈ S.V) : DifferentiableAt ℝ f x :=
  (hf.contDiffAt (hS.isOpen_V.mem_nhds hx)).differentiableAt (by simp)

theorem Hyp.differentiableAt_Ψ {x : E n} (hx : x ∈ S.V) : DifferentiableAt ℝ S.Ψ x :=
  (hS.smooth_Ψ.contDiffAt (hS.isOpen_V.mem_nhds hx)).differentiableAt (by simp)

theorem Hyp.contDiffOn_ψt : ContDiffOn ℝ ∞ S.ψt S.V :=
  hS.smooth_ψ.sub ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).contDiffOn

theorem Hyp.coform_ψ_neg {x : E n} (hx : x ∈ S.V) :
    coform S.g x (d S.ψ x) (d S.ψ x) < 0 :=
  coform_self_neg_of_future (hS.lorentzian_g x) (hS.temporal x hx)

theorem Hyp.coform_φ_ψ_neg (a : ι) {x : E n} (hx : x ∈ S.V) :
    coform S.g x (d (S.φ a) x) (d S.ψ x) < 0 :=
  coform_neg_of_future (hS.lorentzian_g x) (hS.time_g.timelike x) (hS.temporal x hx)
    ((hS.eikonal a).future x hx)

/-- A point of `V` is a limit of points above it where `f` is larger, if `g(df, dψ) < 0`. -/
theorem Hyp.mem_closure_top {x : E n} (hx : x ∈ S.V) {f : E n → ℝ}
    (hf : DifferentiableAt ℝ f x) (hfψ : coform S.g x (d f x) (d S.ψ x) < 0) {O : Set (E n)}
    (hO : O ∈ 𝓝 x) : x ∈ closure {y | y ∈ O ∧ S.ψ x < S.ψ y ∧ f x < f y} :=
  mem_closure_of_fderiv_pos (v := -grad S.g S.ψ x)
    (hS.differentiableAt_of_contDiffOn hS.smooth_ψ hx) hf
    (by rw [fderiv_neg_grad]; linarith [hS.coform_ψ_neg hx]) (by rw [fderiv_neg_grad]; linarith)
    hO

theorem Hyp.continuousOn_D (i j : Fin (n + 1)) : ContinuousOn (fun x => D S.Ψ x i j) S.V :=
  (hS.contDiffOn_dΨ i j).continuousOn.congr fun _ hx => (d_coord_comp (hS.differentiableAt_Ψ hx) i j).symm

theorem Hyp.continuousOn_pullback (i j : Fin (n + 1)) :
    ContinuousOn (fun x => ((D S.Ψ x)ᵀ * S.g' (S.Ψ x) * D S.Ψ x) i j) S.V := by
  simp only [mul_apply, transpose_apply]
  exact continuousOn_finsetSum _ fun l _ => (continuousOn_finsetSum _ fun k _ =>
    ((hS.continuousOn_D k i).mul (hS.contDiffOn_g'Ψ k l).continuousOn)).mul
    (hS.continuousOn_D l j)

/-- By continuity, `Ψ^* g' = g` on the top `{ψ = τ}`. -/
theorem Hyp.pullback_of_closure {x : E n} (hx : x ∈ S.V)
    (hxc : x ∈ closure {y | y ∈ S.V ∧ S.τ < S.ψ y}) :
    S.g x = (D S.Ψ x)ᵀ * S.g' (S.Ψ x) * D S.Ψ x := by
  ext i j
  have hc : ContinuousAt (fun y => S.g y i j - ((D S.Ψ y)ᵀ * S.g' (S.Ψ y) * D S.Ψ y) i j) x :=
    ((hS.smooth_g i j).continuous.continuousOn.sub (hS.continuousOn_pullback i j)).continuousAt
      (hS.isOpen_V.mem_nhds hx)
  have := eq_zero_of_mem_closure hc (fun y hy => by
    simp [hS.pullback_top y hy.1 hy.2]) hxc
  linarith

theorem Hyp.q₀_mem_closure : S.q₀ ∈ closure {y | y ∈ S.V ∧ S.τ < S.ψ y} := by
  have hq := hS.mem_V
  refine closure_mono (fun y (hy : y ∈ {y | y ∈ S.V ∧ S.ψ S.q₀ < S.ψ y ∧ S.ψ S.q₀ < S.ψ y}) =>
    (⟨hy.1, by rw [τ_def]; exact hy.2.1⟩ : y ∈ {y | y ∈ S.V ∧ S.τ < S.ψ y})) (hS.mem_closure_top hq
    (hS.differentiableAt_of_contDiffOn hS.smooth_ψ hq) (hS.coform_ψ_neg hq)
    (hS.isOpen_V.mem_nhds hq))

theorem Hyp.d_ψt (x : E n) (hx : x ∈ S.V) (k : Fin (n + 1)) :
    d S.ψt x k = d S.ψ x k - 2 * (x - S.q₀) k := by
  have h1 := (hasStrictFDerivAt_norm_sq (x - S.q₀)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).sub_const S.q₀)
  have h2 := (hS.differentiableAt_of_contDiffOn hS.smooth_ψ hx).hasFDerivAt.sub h1
  have e : S.ψt = S.ψ - ((fun x : E n => ‖x‖ ^ 2) ∘ fun y => id y - S.q₀) := by
    funext y; simp [ψt]
  simp only [d_def]
  rw [e, h2.fderiv]
  simp [EuclideanSpace.inner_single_right]

theorem Hyp.exists_ball : ∃ R, S.Ball R := by
  have hq := hS.mem_V
  have hpull := hS.pullback_of_closure hq hS.q₀_mem_closure
  have hdet : (D S.Ψ S.q₀).det ≠ 0 := det_ne_zero_of_pullback hpull (hS.det_ne_zero _)
  have hκ : S.κ S.q₀ = 1 := κ_eq_one hS hq hpull
  have hVn := hS.isOpen_V.mem_nhds hq
  have hDc : ContinuousAt (fun x => (D S.Ψ x).det) S.q₀ :=
    ((continuous_id.matrix_det).comp_continuousOn (continuousOn_pi.2 fun i =>
      continuousOn_pi.2 fun j => hS.continuousOn_D i j)).continuousAt hVn
  have hκc : ContinuousAt S.κ S.q₀ := hS.contDiffOn_κ.continuousOn.continuousAt hVn
  have hdt : ∀ k, ContinuousOn (fun x => d S.ψt x k) S.V := fun k =>
    (contDiffOn_d hS.isOpen_V hS.contDiffOn_ψt k).continuousOn
  have hginv : ∀ j k, ContinuousOn (fun x => (S.g x)⁻¹ j k) S.V := fun j k =>
    (hS.contDiffOn_g_inv j k).continuousOn
  have hT : ∀ k, ContinuousOn (fun x => timeCovector S.g S.Y x k) S.V := fun k => by
    simp only [timeCovector_def, Pi.neg_apply, mulVec, dotProduct]
    exact (continuousOn_finsetSum _ fun j _ => ((hS.smooth_g k j).continuous.continuousOn).mul
      ((EuclideanSpace.proj j : E n →L[ℝ] ℝ).continuous.comp
        hS.time_g.continuous).continuousOn).neg
  have hF₁ : ContinuousAt (fun x => coform S.g x (d S.ψt x) (d S.ψt x)) S.q₀ := by
    simp only [coform_def]
    exact (continuousOn_finsetSum _ fun j _ => continuousOn_finsetSum _ fun k _ =>
      ((hginv j k).mul (hdt j)).mul (hdt k)).continuousAt hVn
  have hF₂ : ContinuousAt (fun x => coform S.g x (d S.ψt x) (timeCovector S.g S.Y x)) S.q₀ := by
    simp only [coform_def]
    exact (continuousOn_finsetSum _ fun j _ => continuousOn_finsetSum _ fun k _ =>
      ((hginv j k).mul (hdt j)).mul (hT k)).continuousAt hVn
  have hdq : d S.ψt S.q₀ = d S.ψ S.q₀ := by
    ext k; rw [hS.d_ψt _ hq]; simp
  have hF₁q : coform S.g S.q₀ (d S.ψt S.q₀) (d S.ψt S.q₀) < 0 := by
    rw [hdq]; exact hS.coform_ψ_neg hq
  have hF₂q : coform S.g S.q₀ (d S.ψt S.q₀) (timeCovector S.g S.Y S.q₀) < 0 := by
    rw [hdq, ← form_neg_grad_time (hS.lorentzian_g _)]; exact (hS.temporal _ hq).future
  have hev : ∀ᶠ x in 𝓝 S.q₀, x ∈ S.V ∧ (D S.Ψ x).det ≠ 0 ∧ 1 / 2 < S.κ x ∧
      coform S.g x (d S.ψt x) (d S.ψt x) < 0 ∧
      coform S.g x (d S.ψt x) (timeCovector S.g S.Y x) < 0 := by
    filter_upwards [hVn, hDc.eventually_ne hdet,
      hκc.eventually (lt_mem_nhds (show (1 / 2 : ℝ) < S.κ S.q₀ by rw [hκ]; norm_num)),
      hF₁.eventually (gt_mem_nhds hF₁q), hF₂.eventually (gt_mem_nhds hF₂q)] with x h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨R, hR, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  refine ⟨R, ⟨hR, fun x hx => (hball x hx).1, fun x hx => (hball x hx).2.1,
    fun x hx => (hball x hx).2.2.1, fun x hx => ⟨?_, ?_⟩⟩⟩
  · rw [form_neg_grad (hS.lorentzian_g x)]; exact (hball x hx).2.2.2.1
  · rw [form_neg_grad_time (hS.lorentzian_g x)]; exact (hball x hx).2.2.2.2

namespace Ball

variable {R : ℝ} (hB : S.Ball R)
include hB

omit hS hB in
theorem dist_sq_le {ρ : ℝ} {x : E n} (hx : x ∈ S.L R ρ) : ‖x - S.q₀‖ ^ 2 ≤ ρ ^ 2 := by
  have h1 := hx.2.1; have h2 := hx.2.2
  simp only [ψt, τ_def] at h1 h2 ⊢
  linarith

omit hS hB in
theorem L_subset_closedBall {ρ : ℝ} (hρ : 0 ≤ ρ) : S.L R ρ ⊆ closedBall S.q₀ ρ := fun x hx => by
  rw [mem_closedBall, dist_eq_norm]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hρ two_ne_zero).1 (dist_sq_le hx)

theorem continuousOn_ψ : ContinuousOn S.ψ (ball S.q₀ R) :=
  hS.smooth_ψ.continuousOn.mono hB.subset

theorem continuousOn_ψt : ContinuousOn S.ψt (ball S.q₀ R) :=
  hS.contDiffOn_ψt.continuousOn.mono hB.subset

theorem isCompact_L {ρ : ℝ} (hρ : 0 ≤ ρ) (hρR : ρ < R) : IsCompact (S.L R ρ) := by
  have hsub : closedBall S.q₀ ρ ⊆ ball S.q₀ R := closedBall_subset_ball hρR
  have e : S.L R ρ = (closedBall S.q₀ ρ ∩ S.ψ ⁻¹' Iic S.τ) ∩ S.ψt ⁻¹' Ici (S.τ - ρ ^ 2) := by
    ext x
    refine ⟨fun hx => ⟨⟨L_subset_closedBall hρ hx, hx.2.1⟩, hx.2.2⟩,
      fun hx => ⟨hsub hx.1.1, hx.1.2, hx.2⟩⟩
  have h1 : IsClosed (closedBall S.q₀ ρ ∩ S.ψ ⁻¹' Iic S.τ) :=
    ((continuousOn_ψ hS hB).mono hsub).preimage_isClosed_of_isClosed isClosed_closedBall
      isClosed_Iic
  have h2 : IsClosed ((closedBall S.q₀ ρ ∩ S.ψ ⁻¹' Iic S.τ) ∩ S.ψt ⁻¹' Ici (S.τ - ρ ^ 2)) :=
    ((continuousOn_ψt hS hB).mono (inter_subset_left.trans hsub)).preimage_isClosed_of_isClosed
      h1 isClosed_Ici
  rw [e]
  exact (isCompact_closedBall S.q₀ ρ).of_isClosed_subset h2
    (inter_subset_left.trans inter_subset_left)

/-- The setting of the energy inequalities on the lens `L_ρ`. -/
theorem setting {ρ : ℝ} (hρ : 0 ≤ ρ) (hρR : ρ < R) :
    StepEnergySetting (ball S.q₀ R) S.g S.Y S.ψ S.ψt S.τ (S.τ - ρ ^ 2) where
  isOpen := isOpen_ball
  smooth i j := (hS.smooth_g i j).contDiffOn
  lorentzian x _ := hS.lorentzian_g x
  continuousOn_time := hS.time_g.continuous.continuousOn
  timelike x _ := hS.time_g.timelike x
  smooth_ψ := hS.smooth_ψ.mono hB.subset
  smooth_ψ' := hS.contDiffOn_ψt.mono hB.subset
  temporal_ψ x hx := hS.temporal x (hB.subset hx)
  temporal_ψ' := hB.temporal
  isCompact := isCompact_L hS hB hρ hρR

theorem eikonal (a : ι) : StepEikonal (ball S.q₀ R) S.g S.Y (S.φ a) :=
  ⟨(hS.eikonal a).smooth.mono hB.subset, fun x hx => (hS.eikonal a).null x (hB.subset hx),
    fun x hx => (hS.eikonal a).ne_zero x (hB.subset hx),
    fun x hx => (hS.eikonal a).future x (hB.subset hx)⟩

omit hS in
theorem half_pos : 0 < R / 2 := by linarith [hB.pos]

omit hS in
theorem half_lt : R / 2 < R := by linarith [hB.pos]

omit hS in
theorem Vo_subset : S.Vo R ⊆ ball S.q₀ R := fun _ hx => ball_subset_ball (half_lt hB).le hx.1

theorem isOpen_Vo : IsOpen (S.Vo R) :=
  ((continuousOn_ψt hS hB).mono (ball_subset_ball (half_lt hB).le)).isOpen_inter_preimage
    isOpen_ball isOpen_Ioi

omit hS in
theorem mem_Vo : S.q₀ ∈ S.Vo R := by
  refine ⟨mem_ball_self (half_pos hB), ?_⟩
  simp only [ψt, τ_def, sub_self, norm_zero]
  have := half_pos hB
  nlinarith

theorem isOpen_Vlow : IsOpen (S.Vlow R) :=
  ((continuousOn_ψ hS hB).mono (Vo_subset hB)).isOpen_inter_preimage (isOpen_Vo hS hB)
    isOpen_Iio

omit hS in
theorem Vlow_subset_L : S.Vlow R ⊆ S.L R (R / 2) := fun _ hx =>
  ⟨Vo_subset hB hx.1, hx.2.le, hx.1.2.le⟩

omit hS hB in
theorem L_subset_Vo {ρ : ℝ} (hρ : 0 ≤ ρ) (hρr : ρ < R / 2) : S.L R ρ ⊆ S.Vo R := by
  intro x hx
  refine ⟨mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 (L_subset_closedBall hρ hx)) hρr), ?_⟩
  · have h2 := hx.2.2
    have : ρ ^ 2 < (R / 2) ^ 2 := by nlinarith
    linarith

theorem ae_mem_Vlow :
    ∀ᵐ x ∂(volume.restrict (S.L R (R / 2))), x ∈ S.Vlow R := by
  have hset := setting hS hB (half_pos hB).le (half_lt hB)
  have hm : MeasurableSet (S.L R (R / 2)) :=
    (isCompact_L hS hB (half_pos hB).le (half_lt hB)).measurableSet
  filter_upwards [hset.ae_lens_ne, ae_restrict_mem hm] with x hx hxL
  have h1 : S.ψ x < S.τ := lt_of_le_of_ne hxL.2.1 hx.1
  have h2 : S.τ - (R / 2) ^ 2 < S.ψt x := lt_of_le_of_ne hxL.2.2 (Ne.symm hx.2)
  refine ⟨⟨?_, h2⟩, h1⟩
  rw [mem_ball, dist_eq_norm]
  have : ‖x - S.q₀‖ ^ 2 < (R / 2) ^ 2 := by
    simp only [ψt, τ_def] at h1 h2; linarith
  exact (pow_lt_pow_iff_left₀ (norm_nonneg _) (half_pos hB).le two_ne_zero).1 this

end Ball

end StepData

end

end LorentzianCalderon
