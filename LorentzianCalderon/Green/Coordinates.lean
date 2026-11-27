module

public import LorentzianCalderon.Causal.TimeFlow
public import LorentzianCalderon.Green.NarrowMetric
public import LorentzianCalderon.Green.NormalForm
public import LorentzianCalderon.Local.Naturality

public section

/-!
# Coordinates adapted to a standard time

For a standard time `ψ` (`IsStandardTime`), equal to `σ x⁰ + A` outside a compact set `C`, take
`T₁` so large that `C ⊆ {|x⁰| < T₁}` and `A - T₁ < min_C ψ`. Then the slice `{x⁰ = -σT₁}` is the
level set `{ψ = A - T₁}`, and with the flow `Φ` of `N = grad ψ / g(dψ, dψ)` (`timeFlow`)

`χ(z) = Φ_{z⁰ - A + T₁}(-σT₁, z_sp)`  (`adaptedChart`)

is a diffeomorphism of `ℝ^{1+n}` with the explicit smooth inverse
`x ↦ (ψ x, spatial part of Φ_{A - T₁ - ψ x} x)` (`adaptedChartInv`), and `ψ ∘ χ = z⁰`.
Since `∂₀χ = N` is `g`-orthogonal to `ker dψ`, the pulled back metric `ĝ = χ^*g` (`pullMetric`)
has zero shift, `ĝ₀₀ = 1/g(dψ, dψ)`, and the pullback of the narrowed metric `g + ε dψ²` is
`ĝ + ε dt²`. Far out in space the flow lines are the straight lines `s ↦ (s, z_sp)`, so `ĝ` is
the Minkowski metric where `‖z_sp‖ > R`. Everything is collected in `IsAdaptedChart`
(`exists_isAdaptedChart`), and the normal form of `□` in these coordinates is
`IsAdaptedChart.box_narrow_eq_iff`.

Both signs `σ = ±1` are handled directly: the slice is `{x⁰ = -σT₁}` and, far out,
`χ(z) = (σ(z⁰ - A), z_sp)`.
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Set Filter Matrix

variable {n : ℕ}

local notation "e₀" => (EuclideanSpace.single (0 : Fin (_ + 1)) (1 : ℝ) : E _)

/-! ### Time and space coordinates -/

/-- The point with time `c` and the spatial part of `z`. -/
def setTime (c : ℝ) (z : E n) : E n := z + (c - z 0) • EuclideanSpace.single 0 1

/-- The time of `setTime c z` is `c`. -/
@[simp]
theorem setTime_apply_zero (c : ℝ) (z : E n) : setTime c z 0 = c := by
  simp [setTime]

/-- `setTime` keeps the spatial part. -/
@[simp]
theorem spatial_setTime (c : ℝ) (z : E n) : spatial (setTime c z) = spatial z := by
  simp [setTime]

/-- Points with equal time and spatial parts are equal. -/
theorem eq_of_time_spatial {x y : E n} (h0 : x 0 = y 0) (hs : spatial x = spatial y) : x = y := by
  ext i
  refine Fin.cases h0 (fun j => ?_) i
  simpa using congrArg (fun u : EuclideanSpace ℝ (Fin n) => u j) hs

/-- Setting the time twice keeps the last value. -/
@[simp]
theorem setTime_setTime (c c' : ℝ) (z : E n) : setTime c (setTime c' z) = setTime c z :=
  eq_of_time_spatial (by simp) (by simp)

/-- Setting the time of `z` to its own time does nothing. -/
theorem setTime_self (z : E n) : setTime (z 0) z = z := eq_of_time_spatial (by simp) (by simp)

/-- Moving `setTime c z` along `∂₀` by `s` sets the time to `c + s`. -/
theorem setTime_add_smul (c s : ℝ) (z : E n) :
    setTime c z + s • EuclideanSpace.single 0 1 = setTime (c + s) z :=
  eq_of_time_spatial (by simp) (by simp)

/-- `‖x_sp‖ ≤ ‖x‖`. -/
theorem norm_spatial_le (x : E n) : ‖spatial x‖ ≤ ‖x‖ := by
  have := norm_sq_eq_time_sq_add x
  exact le_of_sq_le_sq (by nlinarith [sq_nonneg (x 0)]) (norm_nonneg x)

/-- `|x⁰| ≤ ‖x‖`. -/
theorem abs_time_le_norm (x : E n) : |x 0| ≤ ‖x‖ := by
  have := norm_sq_eq_time_sq_add x
  exact abs_le.2 (abs_le_of_sq_le_sq' (by nlinarith [sq_nonneg ‖spatial x‖]) (norm_nonneg x))

/-- `setTime` is smooth in the time and the point. -/
theorem contDiff_setTime : ContDiff ℝ ∞ fun p : ℝ × E n => setTime p.1 p.2 := by
  unfold setTime
  exact contDiff_snd.add ((contDiff_fst.sub ((contDiff_coordinate 0).comp contDiff_snd)).smul
    contDiff_const)

/-- `{‖z_sp‖ > R}` is open. -/
theorem isOpen_lt_norm_spatial (R : ℝ) : IsOpen {z : E n | R < ‖spatial z‖} :=
  isOpen_lt continuous_const (continuous_norm.comp spatial.continuous)

/-- A derivative along the line `r ↦ z + r w` is the directional derivative. -/
theorem fderiv_apply_eq_of_hasDerivAt {χ : E n → E n} {z w v : E n}
    (hχ : DifferentiableAt ℝ χ z) (h : HasDerivAt (fun r : ℝ => χ (z + r • w)) v 0) :
    fderiv ℝ χ z w = v := by
  have hl : HasDerivAt (fun r : ℝ => z + r • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add z
  have hχ' : HasFDerivAt χ (fderiv ℝ χ z) (z + (0 : ℝ) • w) := by simpa using hχ.hasFDerivAt
  have := hχ'.comp_hasDerivAt (0 : ℝ) hl
  exact this.unique h

/-! ### The flow of a standard time -/

/-- The flow of `N = grad ψ / g(dψ, dψ)`. -/
def timeFlow (g : MatrixField n) (ψ : E n → ℝ) (t : ℝ) (x : E n) : E n :=
  ODEFlow.flow (timeField g ψ) univ (t, x)

section Flow

variable {g : MatrixField n} {Y : E n → E n} {ψ : E n → ℝ}
  (hg : IsSpacetime g Y) (hψ : IsStandardTime g Y ψ)
include hg hψ

/-- `N` is smooth. -/
theorem IsStandardTime.contDiff_timeField : ContDiff ℝ ∞ (timeField g ψ) :=
  LorentzianCalderon.contDiff_timeField hg hψ.past_gradient hψ.smooth

/-- The flow of `N` is global, since `‖N‖ ≤ 1/κ` by steepness. -/
theorem IsStandardTime.dom_timeField : ODEFlow.dom (timeField g ψ) univ = univ := by
  obtain ⟨κ, hκ, hsteep⟩ := hψ.exists_steep hg
  have hNb : ∀ x, ‖timeField g ψ x‖ ≤ κ⁻¹ := fun x => by
    have hT := isFutureTimelike_timeField hg hψ.past_gradient x
    have hn := norm_pos_iff.2 hT.ne_zero
    have := hsteep x _ hT.isFutureCausal
    rw [fderiv_timeField hg hψ.past_gradient] at this
    rw [le_inv_comm₀ hn hκ, ← one_div, le_div_iff₀ hn]
    linarith
  exact ODEFlow.dom_eq_univ ((hψ.contDiff_timeField hg).of_le (by simp)) hNb

/-- `N` is locally Lipschitz. -/
theorem IsStandardTime.locallyLipschitz_timeField :
    LocallyLipschitzOn univ (timeField g ψ) :=
  ODEFlow.locallyLipschitzOn_of_contDiffOn isOpen_univ
    ((hψ.contDiff_timeField hg).of_le (by simp)).contDiffOn

/-- The flow of `N` is smooth in time and point. -/
theorem IsStandardTime.contDiff_timeFlow :
    ContDiff ℝ ∞ fun p : ℝ × E n => timeFlow g ψ p.1 p.2 := by
  have := (ODEFlow.contDiffOn_flow isOpen_univ (hψ.contDiff_timeField hg).contDiffOn).2
  rw [hψ.dom_timeField hg] at this
  exact contDiffOn_univ.1 this

/-- The flow lines solve `ẋ = N(x)`. -/
theorem IsStandardTime.hasDerivAt_timeFlow (t : ℝ) (x : E n) :
    HasDerivAt (fun r => timeFlow g ψ r x) (timeField g ψ (timeFlow g ψ t x)) t :=
  ODEFlow.hasDerivAt_flow ((hψ.contDiff_timeField hg).of_le (by simp)) (hψ.dom_timeField hg) t x

/-- `Φ₀ = id`. -/
theorem IsStandardTime.timeFlow_zero (x : E n) : timeFlow g ψ 0 x = x :=
  ODEFlow.flow_zero (hψ.locallyLipschitz_timeField hg) (mem_univ x)

/-- The group property `Φ_{s+t} = Φ_t ∘ Φ_s`. -/
theorem IsStandardTime.timeFlow_add (s t : ℝ) (x : E n) :
    timeFlow g ψ (s + t) x = timeFlow g ψ t (timeFlow g ψ s x) :=
  (ODEFlow.flow_add (hψ.locallyLipschitz_timeField hg) (hψ.dom_timeField hg ▸ mem_univ _)
    (hψ.dom_timeField hg ▸ mem_univ _)).2

/-- `Φ_{-t} ∘ Φ_t = id`. -/
theorem IsStandardTime.timeFlow_neg_add (t : ℝ) (x : E n) :
    timeFlow g ψ (-t) (timeFlow g ψ t x) = x := by
  rw [← hψ.timeFlow_add hg, add_neg_cancel, hψ.timeFlow_zero hg]

/-- The flow moves the level sets of `ψ`: `ψ ∘ Φ_t = ψ + t`. -/
theorem IsStandardTime.apply_timeFlow (t : ℝ) (x : E n) : ψ (timeFlow g ψ t x) = ψ x + t := by
  have hψd : Differentiable ℝ ψ := hψ.smooth.differentiable (by simp)
  have hder : ∀ r, HasDerivAt (fun r => ψ (timeFlow g ψ r x) - r) 0 r := fun r => by
    have := ((hψd _).hasFDerivAt.comp_hasDerivAt r (hψ.hasDerivAt_timeFlow hg r x)).sub
      (hasDerivAt_id r)
    rwa [fderiv_timeField hg hψ.past_gradient, sub_self] at this
  have := is_const_of_deriv_eq_zero (fun r => (hder r).differentiableAt)
    (fun r => (hder r).deriv) t 0
  simp only [hψ.timeFlow_zero hg, sub_zero] at this
  linarith

/-- Where `N` is the constant `v` along a segment, the flow follows the segment. -/
theorem IsStandardTime.timeFlow_eq_line {t : ℝ} {x v : E n}
    (hv : ∀ s ∈ uIcc 0 t, timeField g ψ (x + s • v) = v) : timeFlow g ψ t x = x + t • v := by
  have hc : ODEFlow.IsSol (timeField g ψ) univ (fun s => x + s • v) (uIcc 0 t) :=
    ⟨ordConnected_uIcc, fun _ _ => mem_univ _, fun s hs => by
      rw [hv s hs]
      simpa using (((hasDerivAt_id s).smul_const v).const_add x).hasDerivWithinAt⟩
  have := ODEFlow.flow_eq (hψ.locallyLipschitz_timeField hg) hc left_mem_uIcc right_mem_uIcc
  simpa [timeFlow] using this

end Flow

/-! ### The data of the chart -/

/-- The choice of the constants of the chart: `ψ = σ x⁰ + A` outside a compact set, the slice
`{x⁰ = -σT₁}` is the level set `{ψ = A - T₁}`, and where `‖x_sp‖ > R`, the metric is Minkowskian
and `N = σ ∂₀`. -/
structure ChartData (g : MatrixField n) (ψ : E n → ℝ) (σ A T₁ R : ℝ) : Prop where
  sign : σ = 1 ∨ σ = -1
  level : ∀ p, ψ p = A - T₁ ↔ p 0 = -(σ * T₁)
  exterior : ∀ x, R < ‖spatial x‖ →
    g x = minkowski n ∧ timeField g ψ x = σ • EuclideanSpace.single 0 1

section Data

variable {g : MatrixField n} {Y : E n → E n} {ψ : E n → ℝ}

/-- Outside a compact set, `g` is Minkowskian, `ψ = σ x⁰ + A` and `N = σ ∂₀`. -/
theorem IsStandardTime.exists_exterior_timeField (hg : IsSpacetime g Y)
    (hψ : IsStandardTime g Y ψ) :
    ∃ (K : Set (E n)) (σ A : ℝ), IsCompact K ∧ (σ = 1 ∨ σ = -1) ∧ ∀ x ∉ K,
      g x = minkowski n ∧ ψ x = σ * x 0 + A ∧
        timeField g ψ x = σ • EuclideanSpace.single 0 1 := by
  obtain ⟨T, σ', hσ', hT⟩ := hg.exterior
  obtain ⟨C, σ, A, hC, hσ, hψC⟩ := hψ.exterior
  refine ⟨C ∪ M0 n T, σ, A, hC.union (isCompact_M0 T), hσ, fun x hx => ?_⟩
  have hgx : g x = minkowski n := (hT x fun h => hx (Or.inr h)).1
  have hev : ψ =ᶠ[𝓝 x] fun y => σ * y 0 + A :=
    eventually_of_mem (hC.isClosed.isOpen_compl.mem_nhds fun h => hx (Or.inl h)) hψC
  have hdx : ∀ k, d ψ x k = if k = 0 then σ else 0 := fun k => by
    rw [d_congr hev]
    have hd : DifferentiableAt ℝ (fun y : E n => y 0) x :=
      (EuclideanSpace.proj (0 : Fin (n + 1)) : E n →L[ℝ] ℝ).differentiableAt
    have := d_add (u := fun y : E n => σ * y 0) (v := fun _ => A) (x := x)
      (hd.const_mul σ) (differentiableAt_const A) k
    simp only at this
    rw [this, d_const_mul hd, d_coord, d_const]
    split_ifs <;> simp
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hs : coform g x (d ψ x) (d ψ x) = -1 := by
    simp only [coform_def, hgx, inv_minkowski, hdx]
    simp only [minkowski_def, diagonal_apply, mul_ite, ite_mul, mul_zero, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rcases hσ with rfl | rfl <;> norm_num
  refine ⟨hgx, hψC x fun h => hx (Or.inl h), ?_⟩
  ext j
  simp only [timeField_def, hs, grad_def, hgx, inv_minkowski, hdx]
  refine Fin.cases ?_ (fun i => ?_) j <;>
    simp [minkowski_def, diagonal_apply, Fin.succ_ne_zero]

/-- The constants of the chart exist. -/
theorem IsStandardTime.exists_chartData (hg : IsSpacetime g Y) (hψ : IsStandardTime g Y ψ) :
    ∃ σ A T₁ R, ChartData g ψ σ A T₁ R := by
  obtain ⟨K, σ, A, hK, hσ, hext⟩ := hψ.exists_exterior_timeField hg
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  obtain ⟨m, hm⟩ := hK.bddBelow_image hψ.smooth.continuous.continuousOn
  set T₁ := max R (A - m) + 1
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hnotK : ∀ x : E n, R < ‖x‖ → x ∉ K := fun x hx hK' => by
    have := hR hK'
    rw [Metric.mem_closedBall, dist_zero_right] at this
    linarith
  refine ⟨σ, A, T₁, R, hσ, fun p => ?_, fun x hx => ?_⟩
  · have hRT : R < T₁ := by simp only [T₁]; linarith [le_max_left R (A - m)]
    have hmT : A - T₁ < m := by simp only [T₁]; linarith [le_max_right R (A - m)]
    by_cases hp : p ∈ K
    · have h1 : m ≤ ψ p := hm ⟨p, hp, rfl⟩
      have h2 : |p 0| ≤ R := by
        have := hR hp
        rw [Metric.mem_closedBall, dist_zero_right] at this
        exact (abs_time_le_norm p).trans this
      constructor
      · intro h
        linarith
      · intro h
        have : |p 0| = T₁ := by
          have hT0 : 0 < T₁ := lt_of_le_of_lt (abs_nonneg _) (h2.trans_lt hRT)
          rw [h, abs_neg, abs_mul, abs_of_pos hT0]
          rcases hσ with rfl | rfl <;> simp
        linarith
    · rw [(hext p hp).2.1]
      constructor
      · intro h
        have h' : σ * p 0 = -T₁ := by linarith
        linear_combination σ * h' - p 0 * hσ2
      · intro h
        rw [h]
        linear_combination (-T₁) * hσ2
  · have := hext x (hnotK x (hx.trans_le (norm_spatial_le x)))
    exact ⟨this.1, this.2.2⟩

end Data

/-! ### The chart and its inverse -/

/-- The adapted chart `χ(z) = Φ_{z⁰ - A + T₁}(-σT₁, z_sp)`. -/
def adaptedChart (g : MatrixField n) (ψ : E n → ℝ) (σ A T₁ : ℝ) (z : E n) : E n :=
  timeFlow g ψ (z 0 - A + T₁) (setTime (-(σ * T₁)) z)

/-- The inverse of the adapted chart, `x ↦ (ψ x, spatial part of Φ_{A - T₁ - ψ x} x)`. -/
def adaptedChartInv (g : MatrixField n) (ψ : E n → ℝ) (A T₁ : ℝ) (x : E n) : E n :=
  setTime (ψ x) (timeFlow g ψ (A - T₁ - ψ x) x)

/-- `det D Ψ(x)` is the determinant of the linear map `DΨ(x)`. -/
theorem det_D_eq_det_fderiv (Ψ : E n → E n) (x : E n) :
    (D Ψ x).det = LinearMap.det (fderiv ℝ Ψ x : E n →ₗ[ℝ] E n) := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis]
  congr 1
  ext i j
  rw [D_def]
  rfl

section Chart

variable {g : MatrixField n} {Y : E n → E n} {ψ : E n → ℝ} {σ A T₁ R : ℝ}
  (hg : IsSpacetime g Y) (hψ : IsStandardTime g Y ψ)
include hg hψ

/-- The chart is smooth. -/
theorem IsStandardTime.contDiff_adaptedChart : ContDiff ℝ ∞ (adaptedChart g ψ σ A T₁) := by
  have h1 : ContDiff ℝ ∞ fun z : E n => z 0 - A + T₁ :=
    ((contDiff_coordinate 0).sub contDiff_const).add contDiff_const
  have h2 : ContDiff ℝ ∞ fun z : E n => setTime (-(σ * T₁)) z :=
    contDiff_setTime.comp (contDiff_const.prodMk contDiff_id)
  exact (hψ.contDiff_timeFlow hg).comp (h1.prodMk h2)

/-- The inverse of the chart is smooth. -/
theorem IsStandardTime.contDiff_adaptedChartInv : ContDiff ℝ ∞ (adaptedChartInv g ψ A T₁) :=
  contDiff_setTime.comp (hψ.smooth.prodMk ((hψ.contDiff_timeFlow hg).comp
    ((contDiff_const.sub hψ.smooth).prodMk contDiff_id)))

/-- `ψ ∘ χ = z⁰`. -/
theorem ChartData.apply_adaptedChart (hD : ChartData g ψ σ A T₁ R) (z : E n) :
    ψ (adaptedChart g ψ σ A T₁ z) = z 0 := by
  rw [adaptedChart, hψ.apply_timeFlow hg, (hD.level _).2 (setTime_apply_zero _ _)]
  ring

/-- `χ⁻¹ ∘ χ = id`. -/
theorem ChartData.adaptedChartInv_adaptedChart (hD : ChartData g ψ σ A T₁ R) (z : E n) :
    adaptedChartInv g ψ A T₁ (adaptedChart g ψ σ A T₁ z) = z := by
  rw [adaptedChartInv, hD.apply_adaptedChart hg hψ, adaptedChart, ← hψ.timeFlow_add hg,
    show z 0 - A + T₁ + (A - T₁ - z 0) = 0 by ring, hψ.timeFlow_zero hg, setTime_setTime,
    setTime_self]

/-- `χ ∘ χ⁻¹ = id`. -/
theorem ChartData.adaptedChart_adaptedChartInv (hD : ChartData g ψ σ A T₁ R) (x : E n) :
    adaptedChart g ψ σ A T₁ (adaptedChartInv g ψ A T₁ x) = x := by
  set q := timeFlow g ψ (A - T₁ - ψ x) x
  have hq : q 0 = -(σ * T₁) := (hD.level q).1 (by rw [hψ.apply_timeFlow hg]; ring)
  rw [adaptedChartInv, adaptedChart, setTime_apply_zero, setTime_setTime, ← hq, setTime_self,
    ← hψ.timeFlow_add hg, show A - T₁ - ψ x + (ψ x - A + T₁) = 0 by ring,
    hψ.timeFlow_zero hg]

/-- `∂₀χ = N ∘ χ`. -/
theorem IsStandardTime.fderiv_adaptedChart_single_zero (z : E n) :
    fderiv ℝ (adaptedChart g ψ σ A T₁) z (EuclideanSpace.single 0 1) =
      timeField g ψ (adaptedChart g ψ σ A T₁ z) := by
  refine fderiv_apply_eq_of_hasDerivAt
    ((hψ.contDiff_adaptedChart hg).differentiable (by simp) z) ?_
  have h := (hψ.hasDerivAt_timeFlow hg (z 0 - A + T₁ + 0) (setTime (-(σ * T₁)) z)).comp_const_add
    (z 0 - A + T₁) 0
  rw [add_zero] at h
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun r => ?_)
  simp only [adaptedChart]
  congr 1
  · simp
    ring
  · exact eq_of_time_spatial (by simp) (by simp)

/-- `dψ(Dχ w) = w⁰`. -/
theorem ChartData.fderiv_apply_adaptedChart (hD : ChartData g ψ σ A T₁ R) (z w : E n) :
    fderiv ℝ ψ (adaptedChart g ψ σ A T₁ z) (fderiv ℝ (adaptedChart g ψ σ A T₁) z w) = w 0 := by
  have hψd : DifferentiableAt ℝ ψ (adaptedChart g ψ σ A T₁ z) :=
    hψ.smooth.differentiable (by simp) _
  have hχd : DifferentiableAt ℝ (adaptedChart g ψ σ A T₁) z :=
    (hψ.contDiff_adaptedChart hg).differentiable (by simp) z
  have h := congrArg (fun f => fderiv ℝ f z w)
    (funext (hD.apply_adaptedChart hg hψ) : ψ ∘ adaptedChart g ψ σ A T₁ = fun z => z 0)
  simp only at h
  rw [fderiv_comp z hψd hχd, (hasFDerivAt_coord z).fderiv] at h
  simpa using h

/-- `Dχ⁻¹ ∘ Dχ = id`. -/
theorem ChartData.fderiv_adaptedChartInv_comp (hD : ChartData g ψ σ A T₁ R) (z : E n) :
    (fderiv ℝ (adaptedChartInv g ψ A T₁) (adaptedChart g ψ σ A T₁ z)).comp
      (fderiv ℝ (adaptedChart g ψ σ A T₁) z) = ContinuousLinearMap.id ℝ (E n) := by
  rw [← fderiv_comp z ((hψ.contDiff_adaptedChartInv hg).differentiable (by simp) _)
    ((hψ.contDiff_adaptedChart hg).differentiable (by simp) z),
    show adaptedChartInv g ψ A T₁ ∘ adaptedChart g ψ σ A T₁ = id from
      funext (hD.adaptedChartInv_adaptedChart hg hψ), fderiv_id]

/-- The Jacobian of the chart is invertible. -/
theorem ChartData.det_D_adaptedChart_ne_zero (hD : ChartData g ψ σ A T₁ R) (z : E n) :
    (D (adaptedChart g ψ σ A T₁) z).det ≠ 0 := by
  have := congrArg (fun L : E n →L[ℝ] E n => LinearMap.det (L : E n →ₗ[ℝ] E n))
    (hD.fderiv_adaptedChartInv_comp hg hψ z)
  simp only [ContinuousLinearMap.coe_id, LinearMap.det_id] at this
  rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp] at this
  rw [det_D_eq_det_fderiv]
  exact right_ne_zero_of_mul_eq_one this

/-- `Dχ` is injective. -/
theorem ChartData.fderiv_adaptedChart_ne_zero (hD : ChartData g ψ σ A T₁ R) (z : E n) {w : E n}
    (hw : w ≠ 0) : fderiv ℝ (adaptedChart g ψ σ A T₁) z w ≠ 0 := by
  intro h
  have := congrArg (fun L : E n →L[ℝ] E n => L w) (hD.fderiv_adaptedChartInv_comp hg hψ z)
  simp only [ContinuousLinearMap.comp_apply, h, map_zero, ContinuousLinearMap.id_apply] at this
  exact hw this.symm

/-- Far out in space, `χ(z) = (σ(z⁰ - A), z_sp)`. -/
theorem ChartData.adaptedChart_of_far (hD : ChartData g ψ σ A T₁ R) {z : E n}
    (hz : R < ‖spatial z‖) : adaptedChart g ψ σ A T₁ z = setTime (σ * (z 0 - A)) z := by
  have hline : ∀ s : ℝ, setTime (-(σ * T₁)) z + s • (σ • EuclideanSpace.single 0 1 : E n) =
      setTime (-(σ * T₁) + s * σ) z := fun s => by
    rw [smul_smul, setTime_add_smul]
  rw [adaptedChart, hψ.timeFlow_eq_line hg (v := σ • EuclideanSpace.single 0 1) fun s _ => by
    rw [hline]
    exact (hD.exterior _ (by simpa using hz)).2, hline]
  congr 1
  ring

/-- Far out in space, `Dχ(z) w = w + (σ - 1) w⁰ ∂₀`. -/
theorem ChartData.fderiv_adaptedChart_of_far (hD : ChartData g ψ σ A T₁ R) {z : E n}
    (hz : R < ‖spatial z‖) (w : E n) :
    fderiv ℝ (adaptedChart g ψ σ A T₁) z w = w + ((σ - 1) * w 0) • EuclideanSpace.single 0 1 := by
  refine fderiv_apply_eq_of_hasDerivAt
    ((hψ.contDiff_adaptedChart hg).differentiable (by simp) z) ?_
  have hl : HasDerivAt (fun r : ℝ => adaptedChart g ψ σ A T₁ z +
      r • (w + ((σ - 1) * w 0) • EuclideanSpace.single 0 1))
      (w + ((σ - 1) * w 0) • EuclideanSpace.single 0 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const
      (w + ((σ - 1) * w 0) • (EuclideanSpace.single 0 1 : E n))).const_add
      (adaptedChart g ψ σ A T₁ z)
  refine hl.congr_of_eventuallyEq ?_
  have hc : Continuous fun r : ℝ => z + r • w := by fun_prop
  filter_upwards [hc.continuousAt.preimage_mem_nhds
    ((isOpen_lt_norm_spatial R).mem_nhds (by simpa using hz))] with r hr
  rw [hD.adaptedChart_of_far hg hψ hr, hD.adaptedChart_of_far hg hψ hz]
  refine eq_of_time_spatial ?_ (by simp)
  simp
  ring

end Chart

/-! ### The pulled back metric -/

/-- The pulled back metric `χ^*G = (Dχ)ᵀ (G ∘ χ) Dχ`. -/
def pullMetric (G : MatrixField n) (χ : E n → E n) : MatrixField n :=
  fun z => (D χ z)ᵀ * G (χ z) * D χ z

theorem pullMetric_def (G : MatrixField n) (χ : E n → E n) :
    pullMetric G χ =
      fun z => (D χ z)ᵀ * G (χ z) * D χ z := by rfl

/-- `Dχ w` is the Jacobian matrix times `w`. -/
theorem ofLp_fderiv_eq_mulVec (χ : E n → E n) (z v : E n) :
    WithLp.ofLp (fderiv ℝ χ z v) = D χ z *ᵥ WithLp.ofLp v := by
  ext a
  rw [clm_apply_eq_sum (fderiv ℝ χ z) v]
  simp [mulVec, dotProduct, D_def, mul_comm]

/-- `χ^*G(v, w) = G(Dχ v, Dχ w)`. -/
theorem form_pullMetric (G : MatrixField n) (χ : E n → E n) (z v w : E n) :
    form (pullMetric G χ z) v w = form (G (χ z)) (fderiv ℝ χ z v) (fderiv ℝ χ z w) := by
  rw [form_eq_bil, form_eq_bil, bil_apply, bil_apply, ofLp_fderiv_eq_mulVec,
    ofLp_fderiv_eq_mulVec, pullMetric, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec,
    vecMul_transpose]

/-- `G(eᵢ, eⱼ) = Gᵢⱼ`. -/
theorem form_single_single (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i j : Fin (n + 1)) :
    form G (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) = G i j := by
  simp [form_def, PiLp.single_apply]

/-- `(χ^*G)ᵢⱼ = G(∂ᵢχ, ∂ⱼχ)`. -/
theorem pullMetric_apply (G : MatrixField n) (χ : E n → E n) (z : E n) (i j : Fin (n + 1)) :
    pullMetric G χ z i j = form (G (χ z)) (fderiv ℝ χ z (EuclideanSpace.single i 1))
      (fderiv ℝ χ z (EuclideanSpace.single j 1)) := by
  rw [← form_pullMetric, form_single_single]

/-- `g(N, v) = dψ(v) / g(dψ, dψ)`. -/
theorem form_timeField_left {g : MatrixField n} {ψ : E n → ℝ} {x : E n}
    (hL : IsLorentzian (g x)) (v : E n) :
    form (g x) (timeField g ψ x) v = (coform g x (d ψ x) (d ψ x))⁻¹ * fderiv ℝ ψ x v := by
  rw [timeField_def, form_smul_left, ← fderiv_eq_form_grad hL]

section Metric

variable {g : MatrixField n} {Y : E n → E n} {ψ : E n → ℝ} {σ A T₁ R : ℝ}
  (hg : IsSpacetime g Y) (hψ : IsStandardTime g Y ψ) (hD : ChartData g ψ σ A T₁ R)
include hg hψ hD

/-- The pulled back metric has zero shift. -/
theorem ChartData.hasZeroShift (z : E n) :
    HasZeroShift (pullMetric g (adaptedChart g ψ σ A T₁) z) where
  left i := by
    rw [pullMetric_apply, hψ.fderiv_adaptedChart_single_zero hg, form_timeField_left
      (hg.lorentzian _), hD.fderiv_apply_adaptedChart hg hψ]
    simp [Fin.succ_ne_zero]
  right i := by
    rw [pullMetric_apply, form_comm (hg.lorentzian _).symm,
      hψ.fderiv_adaptedChart_single_zero hg, form_timeField_left (hg.lorentzian _),
      hD.fderiv_apply_adaptedChart hg hψ]
    simp [Fin.succ_ne_zero]

omit hD in
/-- `ĝ₀₀ = 1 / g(dψ, dψ)`. -/
theorem IsStandardTime.pullMetric_adaptedChart_zero_zero (z : E n) :
    pullMetric g (adaptedChart g ψ σ A T₁) z 0 0 =
      (coform g (adaptedChart g ψ σ A T₁ z) (d ψ (adaptedChart g ψ σ A T₁ z))
        (d ψ (adaptedChart g ψ σ A T₁ z)))⁻¹ := by
  rw [pullMetric_apply, hψ.fderiv_adaptedChart_single_zero hg,
    form_timeField_left (hg.lorentzian _), fderiv_timeField hg hψ.past_gradient, mul_one]

/-- The pullback of the narrowed metric `g + ε dψ²` is `ĝ + ε dt²`. -/
theorem ChartData.pullMetric_narrow (ε : ℝ) (z : E n) :
    pullMetric (narrow g ψ ε) (adaptedChart g ψ σ A T₁) z =
      pullMetric g (adaptedChart g ψ σ A T₁) z + ε • vecMulVec (Pi.single 0 1) (Pi.single 0 1) := by
  ext i j
  rw [Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, pullMetric_apply, pullMetric_apply,
    form_narrow, hD.fderiv_apply_adaptedChart hg hψ, hD.fderiv_apply_adaptedChart hg hψ]
  simp [PiLp.single_apply, Pi.single_apply, eq_comm]

/-- `ĝ` is positive definite on `{w⁰ = 0}`. -/
theorem ChartData.form_pullMetric_pos (z : E n) {w : E n} (hw0 : w 0 = 0) (hw : w ≠ 0) :
    0 < form (pullMetric g (adaptedChart g ψ σ A T₁) z) w w := by
  rw [form_pullMetric]
  set x := adaptedChart g ψ σ A T₁ z
  set v := fderiv ℝ (adaptedChart g ψ σ A T₁) z w
  have hL := hg.lorentzian x
  have hv0 : v ≠ 0 := hD.fderiv_adaptedChart_ne_zero hg hψ z hw
  have hdv : form (g x) v (grad g ψ x) = 0 := by
    rw [form_comm hL.symm, ← fderiv_eq_form_grad hL, hD.fderiv_apply_adaptedChart hg hψ, hw0]
  have hN : form (g x) (grad g ψ x) (grad g ψ x) < 0 := by
    have := (hψ.past_gradient x).timelike
    rwa [form_neg_left, form_neg_right, neg_neg] at this
  by_contra hle
  exact hL.form_ne_zero (not_lt.1 hle) hv0 hN hdv

/-- Far out in space, `ĝ` is the Minkowski metric. -/
theorem ChartData.pullMetric_of_far {z : E n} (hz : R < ‖spatial z‖) :
    pullMetric g (adaptedChart g ψ σ A T₁) z = minkowski n := by
  have hσ2 : σ * σ = 1 := by rcases hD.sign with rfl | rfl <;> norm_num
  have hgz : g (adaptedChart g ψ σ A T₁ z) = minkowski n :=
    (hD.exterior _ (by rw [hD.adaptedChart_of_far hg hψ hz, spatial_setTime]; exact hz)).1
  ext i j
  rw [pullMetric_apply, hgz, hD.fderiv_adaptedChart_of_far hg hψ hz,
    hD.fderiv_adaptedChart_of_far hg hψ hz, ← form_single_single (minkowski n) i j,
    form_minkowski, form_minkowski]
  simp only [map_add, map_smul, spatial_single_zero, smul_zero, add_zero, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul, single_zero_apply_zero, mul_one]
  linear_combination (-((EuclideanSpace.single i 1 : E n) 0 *
    (EuclideanSpace.single j 1 : E n) 0)) * hσ2

end Metric

/-! ### Adapted charts -/

/-- Coordinates `z = (t, y)` adapted to the standard time `ψ`: a diffeomorphism `χ` with inverse
`χinv` and `ψ ∘ χ = t`, for which the pulled back metric `ĝ = χ^*g` has zero shift,
`ĝ₀₀ = 1/g(dψ, dψ) < 0`, is positive definite on `{w⁰ = 0}`, is Minkowskian where `‖y‖ > R`, and
for which `χ^*(g + ε dψ²) = ĝ + ε dt²`. For `ε < ε₀` the narrowed metric is Lorentzian and
`ĝ₀₀ + ε < 0`. -/
structure IsAdaptedChart (g : MatrixField n) (ψ : E n → ℝ) (χ χinv : E n → E n) (ε₀ R : ℝ) :
    Prop where
  smooth : ContDiff ℝ ∞ χ
  smooth_inv : ContDiff ℝ ∞ χinv
  inv_apply : ∀ z, χinv (χ z) = z
  apply_inv : ∀ x, χ (χinv x) = x
  time : ∀ z, ψ (χ z) = z 0
  det_ne_zero : ∀ z, (D χ z).det ≠ 0
  zeroShift : ∀ z, HasZeroShift (pullMetric g χ z)
  zero_zero : ∀ z, pullMetric g χ z 0 0 = (coform g (χ z) (d ψ (χ z)) (d ψ (χ z)))⁻¹
  narrow_eq : ∀ ε z, pullMetric (narrow g ψ ε) χ z =
    pullMetric g χ z + ε • vecMulVec (Pi.single 0 1) (Pi.single 0 1)
  spacelike : ∀ z w, w 0 = 0 → w ≠ 0 → 0 < form (pullMetric g χ z) w w
  flat : ∀ z, R < ‖spatial z‖ → pullMetric g χ z = minkowski n
  ε₀_pos : 0 < ε₀
  ε₀_le_one : ε₀ ≤ 1
  narrow_pos : ∀ ε < ε₀, ∀ x, 0 < 1 + ε * coform g x (d ψ x) (d ψ x)
  zero_zero_add_neg : ∀ ε < ε₀, ∀ z, pullMetric g χ z 0 0 + ε < 0

/-- Every standard time has adapted coordinates. -/
theorem IsStandardTime.exists_isAdaptedChart {g : MatrixField n} {Y : E n → E n} {ψ : E n → ℝ}
    (hg : IsSpacetime g Y) (hψ : IsStandardTime g Y ψ) :
    ∃ χ χinv ε₀ R, IsAdaptedChart g ψ χ χinv ε₀ R := by
  obtain ⟨σ, A, T₁, R, hD⟩ := hψ.exists_chartData hg
  obtain ⟨M, hM, hle⟩ := hψ.exists_neg_coform_le hg
  have hs : ∀ x, coform g x (d ψ x) (d ψ x) < 0 := coform_d_self_neg hg hψ.past_gradient
  have hMinv : ∀ x, (coform g x (d ψ x) (d ψ x))⁻¹ ≤ -M⁻¹ := fun x => by
    have h := inv_anti₀ (neg_pos.2 (hs x)) (hle x)
    rw [inv_neg] at h
    linarith
  refine ⟨adaptedChart g ψ σ A T₁, adaptedChartInv g ψ A T₁, min M⁻¹ 1, R,
    { smooth := hψ.contDiff_adaptedChart hg
      smooth_inv := hψ.contDiff_adaptedChartInv hg
      inv_apply := hD.adaptedChartInv_adaptedChart hg hψ
      apply_inv := hD.adaptedChart_adaptedChartInv hg hψ
      time := hD.apply_adaptedChart hg hψ
      det_ne_zero := hD.det_D_adaptedChart_ne_zero hg hψ
      zeroShift := hD.hasZeroShift hg hψ
      zero_zero := hψ.pullMetric_adaptedChart_zero_zero hg
      narrow_eq := hD.pullMetric_narrow hg hψ
      spacelike := fun z _ hw0 hw => hD.form_pullMetric_pos hg hψ z hw0 hw
      flat := fun _ hz => hD.pullMetric_of_far hg hψ hz
      ε₀_pos := lt_min (inv_pos.2 hM) one_pos
      ε₀_le_one := min_le_right _ _
      narrow_pos := fun ε hε x => ?_
      zero_zero_add_neg := fun ε hε z => ?_ }⟩
  · have hεM : ε * M < 1 := by
      have := mul_lt_mul_of_pos_right (hε.trans_le (min_le_left _ _)) hM
      rwa [inv_mul_cancel₀ hM.ne'] at this
    rcases le_or_gt ε 0 with h0 | h0
    · nlinarith [hs x]
    · nlinarith [mul_le_mul_of_nonneg_left (hle x) h0.le]
  · rw [hψ.pullMetric_adaptedChart_zero_zero hg]
    linarith [hMinv (adaptedChart g ψ σ A T₁ z), hε.trans_le (min_le_left _ _)]

/-- `g_0 = g`. -/
theorem narrow_zero (g : MatrixField n) (ψ : E n → ℝ) : narrow g ψ 0 = g := by
  funext x
  simp [narrow_def]

/-- The entries of the Jacobian of a smooth map are smooth. -/
theorem contDiff_D_apply {χ : E n → E n} (hχ : ContDiff ℝ ∞ χ) (a i : Fin (n + 1)) :
    ContDiff ℝ ∞ fun z => D χ z a i := by
  simp only [D_def]
  exact (contDiff_coordinate a).comp ((contDiff_infty_iff_fderiv.1 hχ).2.clm_apply contDiff_const)

/-- The pullback of a smooth metric by a smooth map is smooth. -/
theorem contDiff_pullMetric {G : MatrixField n} (hG : ∀ i j, ContDiff ℝ ∞ fun x => G x i j)
    {χ : E n → E n} (hχ : ContDiff ℝ ∞ χ) (i j : Fin (n + 1)) :
    ContDiff ℝ ∞ fun z => pullMetric G χ z i j := by
  simp only [pullMetric, mul_apply, transpose_apply]
  exact ContDiff.sum fun b _ => (ContDiff.sum fun a _ => (contDiff_D_apply hχ a i).mul
    ((hG a b).comp hχ)).mul (contDiff_D_apply hχ b j)

namespace IsAdaptedChart

variable {g : MatrixField n} {Y : E n → E n} {ψ : E n → ℝ} {χ χinv : E n → E n} {ε₀ R ε : ℝ}
  (hg : IsSpacetime g Y) (hψ : IsStandardTime g Y ψ) (hχ : IsAdaptedChart g ψ χ χinv ε₀ R)

section

include hχ

/-- The entries of `χ^*(g + ε dψ²) = ĝ + ε dt²`. -/
theorem pullMetric_narrow_apply (ε : ℝ) (z : E n) (i j : Fin (n + 1)) :
    pullMetric (narrow g ψ ε) χ z i j =
      pullMetric g χ z i j +
        ε * ((Pi.single 0 1 : Fin (n + 1) → ℝ) i * (Pi.single 0 1 : Fin (n + 1) → ℝ) j) := by
  rw [hχ.narrow_eq, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]

/-- `χ^*(g + ε dψ²)` has zero shift. -/
theorem hasZeroShift_narrow (ε : ℝ) (z : E n) : HasZeroShift (pullMetric (narrow g ψ ε) χ z) where
  left i := by
    rw [hχ.pullMetric_narrow_apply, (hχ.zeroShift z).left]
    simp [Fin.succ_ne_zero]
  right i := by
    rw [hχ.pullMetric_narrow_apply, (hχ.zeroShift z).right]
    simp [Fin.succ_ne_zero]

/-- `(χ^*(g + ε dψ²))₀₀ = ĝ₀₀ + ε`. -/
theorem narrow_zero_zero (ε : ℝ) (z : E n) :
    pullMetric (narrow g ψ ε) χ z 0 0 = pullMetric g χ z 0 0 + ε := by
  rw [hχ.pullMetric_narrow_apply]
  simp

/-- `(χ^*(g + ε dψ²))₀₀ < 0` for `ε < ε₀`. -/
theorem narrow_zero_zero_neg (hε : ε < ε₀) (z : E n) : pullMetric (narrow g ψ ε) χ z 0 0 < 0 := by
  rw [hχ.narrow_zero_zero]
  exact hχ.zero_zero_add_neg ε hε z

/-- `χ^*(g + ε dψ²)` is positive definite on `{w⁰ = 0}`. -/
theorem form_narrow_pos (ε : ℝ) (z : E n) {w : E n} (hw0 : w 0 = 0) (hw : w ≠ 0) :
    0 < form (pullMetric (narrow g ψ ε) χ z) w w := by
  rw [hχ.narrow_eq, form_eq_bil, bil_add_smul_vecMulVec, ← form_eq_bil, dotProduct_single,
    hw0, zero_mul, zero_mul, mul_zero, add_zero]
  exact hχ.spacelike z w hw0 hw

/-- The entries of `χ^*(g + ε dψ²)` are smooth in `(ε, z)`. -/
theorem contDiff_pullMetric_narrow (hgs : ∀ i j, ContDiff ℝ ∞ fun x => g x i j)
    (i j : Fin (n + 1)) :
    ContDiff ℝ ∞ fun q : ℝ × E n => pullMetric (narrow g ψ q.1) χ q.2 i j := by
  simp only [hχ.pullMetric_narrow_apply]
  exact ((contDiff_pullMetric hgs hχ.smooth i j).comp contDiff_snd).add
    (contDiff_fst.mul contDiff_const)

/-- Far out in space, `χ^*(g + ε dψ²) = diag(-(1 - ε), 1, …, 1)` near `z`. -/
theorem eventually_narrow_eq_lapseDiag {z : E n} (hz : R < ‖spatial z‖) (ε : ℝ) :
    ∀ᶠ w in 𝓝 z, pullMetric (narrow g ψ ε) χ w = lapseDiag (1 - ε) := by
  filter_upwards [(isOpen_lt_norm_spatial R).mem_nhds hz] with w hw
  ext i j
  rw [hχ.pullMetric_narrow_apply, hχ.flat w hw]
  by_cases hij : i = j
  · subst hij
    refine Fin.cases ?_ (fun k => ?_) i <;>
      simp [lapseDiag_def, minkowski_def, Fin.succ_ne_zero]
    ring
  · simp [lapseDiag_def, minkowski_def, diagonal_apply_ne _ hij, Pi.single_apply]
    intro hi hj
    exact absurd (hj.trans hi.symm) hij

end

section

include hg hψ hχ

/-- `g + ε dψ²` is Lorentzian for `ε < ε₀`. -/
theorem isLorentzian_narrow (hε : ε < ε₀) (x : E n) : IsLorentzian (narrow g ψ ε x) :=
  LorentzianCalderon.isLorentzian_narrow (hg.lorentzian x)
    (coform_d_self_neg hg hψ.past_gradient x) (hχ.narrow_pos ε hε x)

/-- `χ^*(g + ε dψ²)` is nondegenerate for `ε < ε₀`. -/
theorem det_narrow_ne_zero (hε : ε < ε₀) (z : E n) :
    (pullMetric (narrow g ψ ε) χ z).det ≠ 0 := by
  simp only [pullMetric, det_mul, det_transpose]
  exact mul_ne_zero (mul_ne_zero (hχ.det_ne_zero z)
    (hχ.isLorentzian_narrow hg hψ hε _).det_neg.ne) (hχ.det_ne_zero z)

/-- Naturality: `□_{χ^*g_ε}(V ∘ χ) = (□_{g_ε} V) ∘ χ`. -/
theorem box_comp (hε : ε < ε₀) {V : E n → ℝ} {z : E n} (hV : ContDiffAt ℝ 2 V (χ z)) :
    box (pullMetric (narrow g ψ ε) χ) (V ∘ χ) z = box (narrow g ψ ε) V (χ z) :=
  box_comp_of_pullback (hχ.smooth.contDiffAt.of_le (by simp)) (hχ.det_ne_zero z)
    (fun i j => (contDiff_narrow hg.smooth hψ.smooth ε i j).differentiable (by simp) _)
    (hχ.isLorentzian_narrow hg hψ hε _).det_neg.ne (Eventually.of_forall fun _ => rfl) hV

/-- The normal form of the narrowed wave equation in adapted coordinates: with `v = V ∘ χ` and
`G = χ^*(g + ε dψ²)`, `□_{g_ε} V = f` at `χ z` if and only if
`∂ₜ²v = a^{ij} ∂ᵢ∂ⱼv + b^μ ∂_μv + N² f` at `z`. -/
theorem box_narrow_eq_iff (hε : ε < ε₀) {V : E n → ℝ} {z : E n} (hV : ContDiffAt ℝ 2 V (χ z))
    (f : ℝ) :
    box (narrow g ψ ε) V (χ z) = f ↔
      d2 (V ∘ χ) z 0 0 = ∑ i, ∑ j, normalA (pullMetric (narrow g ψ ε) χ) z i j *
          d2 (V ∘ χ) z i.succ j.succ +
        ∑ k, normalB (pullMetric (narrow g ψ ε) χ) z k * d (V ∘ χ) z k +
        lapseSq (pullMetric (narrow g ψ ε) χ) z * f := by
  rw [← hχ.box_comp hg hψ hε hV]
  exact box_eq_iff (fun i j => ((hχ.contDiff_pullMetric_narrow hg.smooth i j).comp
      (contDiff_const.prodMk contDiff_id)).differentiable (by simp) z)
    (hχ.det_narrow_ne_zero hg hψ hε z) (hχ.hasZeroShift_narrow ε z)
    (hχ.narrow_zero_zero_neg hε z).ne
    (hV.comp z (hχ.smooth.contDiffAt.of_le (by simp))) f

/-- The principal part of the normal form is positive definite. -/
theorem normalA_pos (hε : ε < ε₀) (z : E n) {ξ : Fin n → ℝ} (hξ : ξ ≠ 0) :
    0 < ∑ i, ∑ j, normalA (pullMetric (narrow g ψ ε) χ) z i j * ξ i * ξ j :=
  LorentzianCalderon.normalA_pos (hχ.det_narrow_ne_zero hg hψ hε z) (hχ.hasZeroShift_narrow ε z)
    (hχ.narrow_zero_zero_neg hε z) (fun _ hw0 hw => hχ.form_narrow_pos ε z hw0 hw) hξ

/-- The coefficients of the normal form are smooth in `(ε, z)` for `ε < ε₀`. -/
theorem contDiffAt_coeffs (hε : ε < ε₀) (z : E n) :
    ContDiffAt ℝ ∞ (fun q : ℝ × E n => lapseSq (pullMetric (narrow g ψ q.1) χ) q.2) (ε, z) ∧
    (∀ i j, ContDiffAt ℝ ∞
      (fun q : ℝ × E n => normalA (pullMetric (narrow g ψ q.1) χ) q.2 i j) (ε, z)) ∧
    ∀ k, ContDiffAt ℝ ∞
      (fun q : ℝ × E n => normalB (pullMetric (narrow g ψ q.1) χ) q.2 k) (ε, z) := by
  have hG := fun i j => (hχ.contDiff_pullMetric_narrow hg.smooth i j).contDiffAt (x := (ε, z))
  have hdet := hχ.det_narrow_ne_zero hg hψ hε z
  exact ⟨contDiffAt_lapseSq (G := fun ε => pullMetric (narrow g ψ ε) χ) hG,
    contDiffAt_normalA (G := fun ε => pullMetric (narrow g ψ ε) χ) hG hdet,
    contDiffAt_normalB (G := fun ε => pullMetric (narrow g ψ ε) χ) hG hdet⟩

end

/-- Far out in space the normal form is that of `diag(-(1 - ε), 1, …, 1)`:
`N² = 1 - ε`, `a = (1 - ε) id` and `b = 0`. -/
theorem coeffs_of_far (hχ : IsAdaptedChart g ψ χ χinv ε₀ R) (hε : ε < ε₀) {z : E n}
    (hz : R < ‖spatial z‖) :
    lapseSq (pullMetric (narrow g ψ ε) χ) z = 1 - ε ∧
    (∀ i j, normalA (pullMetric (narrow g ψ ε) χ) z i j = if i = j then 1 - ε else 0) ∧
    ∀ k, normalB (pullMetric (narrow g ψ ε) χ) z k = 0 := by
  have h := hχ.eventually_narrow_eq_lapseDiag hz ε
  have hc : 1 - ε ≠ 0 := by linarith [hχ.ε₀_le_one]
  exact ⟨lapseSq_of_eq_lapseDiag h.self_of_nhds,
    fun i j => normalA_of_eq_lapseDiag hc h.self_of_nhds i j, fun k => normalB_eq_zero h k⟩

section

include hg hψ hχ

/-- The principal part is uniformly positive definite: for `(ε, t)` in a compact set with
`ε < ε₀`, there is `κ > 0` with `κ |ξ|² ≤ a^{ij}(ε, t, y) ξᵢ ξⱼ` for all `y` and `ξ`. -/
theorem exists_pos_uniform {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKε : ∀ p ∈ K, p.1 < ε₀) :
    ∃ κ > 0, ∀ p ∈ K, ∀ z : E n, z 0 = p.2 → ∀ ξ : Fin n → ℝ,
      κ * ∑ i, ξ i ^ 2 ≤
        ∑ i, ∑ j, normalA (pullMetric (narrow g ψ p.1) χ) z i j * ξ i * ξ j := by
  set Q : (ℝ × E n) × (Fin n → ℝ) → ℝ := fun q =>
    ∑ i, ∑ j, normalA (pullMetric (narrow g ψ q.1.1) χ) q.1.2 i j * q.2 i * q.2 j
  obtain ⟨C, hC⟩ := hK.isBounded.exists_norm_le
  set K' : Set (ℝ × E n) := {q | (q.1, q.2 0) ∈ K ∧ ‖spatial q.2‖ ≤ R}
  set S : Set (Fin n → ℝ) := {ξ | ∑ i, ξ i ^ 2 = 1}
  have hK' : IsCompact K' := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact (hK.isClosed.preimage (continuous_fst.prodMk
        ((contDiff_coordinate 0).continuous.comp continuous_snd))).inter
        (isClosed_le (continuous_norm.comp (spatial.continuous.comp continuous_snd))
          continuous_const)
    · refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨max C (C + R), fun q hq => ?_⟩
      have h1 := hC _ hq.1
      rw [Prod.norm_def] at h1
      have hz : ‖q.2‖ ≤ C + R := by
        have := norm_sq_eq_time_sq_add q.2
        have h0 : |q.2 0| ≤ C := (le_max_right _ _).trans h1
        have hsp := hq.2
        have : ‖q.2‖ ^ 2 ≤ (C + R) ^ 2 := by
          nlinarith [sq_abs (q.2 0), abs_nonneg (q.2 0), norm_nonneg (spatial q.2)]
        exact le_of_sq_le_sq (by linarith)
          (by linarith [abs_nonneg (q.2 0), norm_nonneg (spatial q.2)])
      rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
      exact max_le_max ((le_max_left _ _).trans h1) hz
  have hS : IsCompact S := by
    refine Metric.isCompact_of_isClosed_isBounded
      (isClosed_eq (by fun_prop) continuous_const) ?_
    refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨1, fun ξ hξ => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
    have : ξ i ^ 2 ≤ 1 := hξ ▸ Finset.single_le_sum (fun j _ => sq_nonneg (ξ j))
      (Finset.mem_univ i)
    rw [Real.norm_eq_abs]
    exact abs_le_one_iff_mul_self_le_one.2 (by nlinarith)
  have hQc : ContinuousOn Q (K' ×ˢ S) := fun q hq => by
    have hε : q.1.1 < ε₀ := hKε _ hq.1.1
    refine ContinuousAt.continuousWithinAt ?_
    have ha := fun i j => (hχ.contDiffAt_coeffs hg hψ hε q.1.2).2.1 i j
    have hQd : ContDiffAt ℝ ∞ Q q := ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ =>
      (((ha i j).comp q contDiffAt_fst).mul
        ((contDiff_apply ℝ ℝ i).comp contDiff_snd).contDiffAt).mul
        ((contDiff_apply ℝ ℝ j).comp contDiff_snd).contDiffAt
    exact hQd.continuousAt
  obtain ⟨κ₁, hκ₁, hQ⟩ : ∃ κ₁ > 0, ∀ q ∈ K' ×ˢ S, κ₁ ≤ Q q := by
    rcases (K' ×ˢ S).eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun q hq => by simp [he] at hq⟩
    obtain ⟨q₀, hq₀, hmin⟩ := (hK'.prod hS).exists_isMinOn hne hQc
    refine ⟨Q q₀, ?_, fun q hq => hmin hq⟩
    refine hχ.normalA_pos hg hψ (hKε _ hq₀.1.1) q₀.1.2 fun h => ?_
    have := hq₀.2
    simp [S, h] at this
  obtain ⟨κ₂, hκ₂, hε₂⟩ : ∃ κ₂ > 0, ∀ p ∈ K, κ₂ ≤ 1 - p.1 := by
    rcases K.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun p hp => by simp [he] at hp⟩
    obtain ⟨p₀, hp₀, hmax⟩ := hK.exists_isMaxOn hne continuous_fst.continuousOn
    refine ⟨1 - p₀.1, by linarith [hKε _ hp₀, hχ.ε₀_le_one], fun p hp => ?_⟩
    linarith [show p.1 ≤ p₀.1 from hmax hp]
  refine ⟨min κ₁ κ₂, lt_min hκ₁ hκ₂, fun p hp z hz ξ => ?_⟩
  by_cases hfar : R < ‖spatial z‖
  · simp only [(hχ.coeffs_of_far (hKε p hp) hfar).2.1, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
    rw [show ∑ i, (1 - p.1) * ξ i * ξ i = (1 - p.1) * ∑ i, ξ i ^ 2 by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring]
    exact mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (hε₂ p hp))
      (Finset.sum_nonneg fun i _ => sq_nonneg _)
  · set c := √(∑ i, ξ i ^ 2)
    have hc2 : c ^ 2 = ∑ i, ξ i ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
    rcases (Real.sqrt_nonneg _ : 0 ≤ c).eq_or_lt with hc0 | hc0
    · have hξ0 : ∀ i, ξ i = 0 := fun i => by
        have : ∑ i, ξ i ^ 2 = 0 := by
          rw [← hc2]
          change (0 : ℝ) = c at hc0
          rw [← hc0]
          ring
        exact pow_eq_zero_iff two_ne_zero |>.1
          ((Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (ξ j)).1 this i
            (Finset.mem_univ i))
      simp [hξ0]
    set ξ' := c⁻¹ • ξ
    have hξ' : ∀ i, ξ i = c * ξ' i := fun i => by
      simp only [ξ', Pi.smul_apply, smul_eq_mul]
      rw [mul_inv_cancel_left₀ (show c ≠ 0 from hc0.ne')]
    have hS' : ξ' ∈ S := by
      change ∑ i, ξ' i ^ 2 = 1
      have : ∑ i, ξ i ^ 2 = c ^ 2 * ∑ i, ξ' i ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [hξ' i]; ring
      rw [hc2] at this
      have hpos : 0 < ∑ i, ξ i ^ 2 := by rw [← hc2]; positivity
      field_simp at this
      linarith
    have hq := hQ ((p.1, z), ξ') ⟨⟨by simp only [hz]; exact hp, not_lt.1 hfar⟩, hS'⟩
    have hhom : ∑ i, ∑ j, normalA (pullMetric (narrow g ψ p.1) χ) z i j * ξ i * ξ j =
        c ^ 2 * Q ((p.1, z), ξ') := by
      simp only [Q, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
        rw [hξ' i, hξ' j]; ring
    rw [hhom, ← hc2, mul_comm]
    exact mul_le_mul_of_nonneg_left ((min_le_left _ _).trans hq) (sq_nonneg c)

end

end IsAdaptedChart

end

end LorentzianCalderon
