module

public import LorentzianCalderon.PDE.Galerkin
public import LorentzianCalderon.PDE.Prolong
public import LorentzianCalderon.PDE.SobolevSup

public section

/-!
# Smooth periodic solutions as limits of Galerkin solutions

`exists_periodic_solution`: for good coefficients `A` and a smooth periodic source `F` vanishing
for `t ≤ t₀`, `∂ₜ²V = A V + F` has a smooth periodic solution vanishing for `t ≤ t₀`;
`eq_zero_of_periodic_solution` gives uniqueness.

The Galerkin solutions `V_N` of P6 (`IsGalerkinSol`, with P6's projection identified with P2's,
`galerkinProj_eq_fourierProj`) satisfy, uniformly in `N`, on `K × [t₀, t₁]`:

* `exists_galerkin_bound`: `‖∂^α V_N‖_{L²(cell)} ≤ C` (P5; the orthogonality hypothesis is
  `IsGalerkinSol.orth`);
* `exists_residual_bound`: the residual `R_N = ∂ₜ²V_N - A V_N - F = (P_N - 1)(A V_N + F)` has
  `‖∂^α R_N‖_{L²(cell)} ≤ C / N` (the tail bound of P2, and `exists_iterD_apply_bound`, which
  bounds `∂^β (A V)` by derivatives of `V` of order `≤ |β| + 2` through the prolonged systems);
* `exists_galerkin_cauchy`: `D = V_M - V_N` (`N ≤ M`) solves `∂ₜ²D = A D + (R_M - R_N)` exactly, so
  P5 with zero data at `t₀` gives `‖∂^α D‖_{L²(cell)} ≤ C / N`;
* `exists_galerkin_cauchy_sup`, `exists_residual_sup`: the same in sup norm on
  `K × [t₀, t₁] × ℝⁿ` for every `C^k` norm.

`exists_contDiff_limit` turns locally uniform `C / N` Cauchy bounds of all derivatives into a smooth
limit (`HasFTaylorSeriesUpTo` of the limits of the derivatives, with
`hasFDerivAt_of_tendstoUniformlyOn`); no cut-off is needed. Bounds on `[t₀, t₁]` cover every
neighbourhood since the initial time may be lowered: `V_N` and `F` also vanish for `t ≤ a ≤ t₀`.
-/

namespace LorentzianCalderon.PDE

noncomputable section
open scoped ContDiff RealInnerProductSpace Topology
open Set MeasureTheory Function Real Filter

/-! ## Smooth limits -/

section SmoothLimit

variable {X G : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup G]
  [NormedSpace ℝ G] [CompleteSpace G]

/-- A sequence of smooth functions whose `k`-th derivatives are Cauchy at the rate `C / N`,
uniformly near every point, has a smooth limit, and all derivatives converge. -/
theorem exists_contDiff_limit {f : ℕ → X → G} (hf : ∀ N, ContDiff ℝ ∞ (f N))
    (h : ∀ x, ∃ U ∈ 𝓝 x, ∀ k, ∃ C, ∀ N M, 1 ≤ N → N ≤ M → ∀ z ∈ U,
      ‖iteratedFDeriv ℝ k (f M) z - iteratedFDeriv ℝ k (f N) z‖ ≤ C / N) :
    ∃ g : X → G, ContDiff ℝ ∞ g ∧
      ∀ k x, Tendsto (fun N => iteratedFDeriv ℝ k (f N) x) atTop (𝓝 (iteratedFDeriv ℝ k g x)) := by
  choose U hU C hC using h
  have hsmall : ∀ (c ε : ℝ), 0 < ε → ∀ᶠ N : ℕ in atTop, 1 ≤ N ∧ c / N < ε := fun c ε hε =>
    (eventually_ge_atTop 1).and
      ((tendsto_const_div_atTop_nhds_zero_nat c).eventually (gt_mem_nhds hε))
  have hcauchy : ∀ k x, CauchySeq fun N => iteratedFDeriv ℝ k (f N) x := by
    intro k x
    refine Metric.cauchySeq_iff'.2 fun ε hε => ?_
    obtain ⟨N₀, hN₀⟩ := (hsmall (C x k) ε hε).exists
    refine ⟨N₀, fun N hN => ?_⟩
    rw [dist_eq_norm]
    exact (hC x k N₀ N hN₀.1 hN (x) (mem_of_mem_nhds (hU x))).trans_lt hN₀.2
  set p : X → FormalMultilinearSeries ℝ X G := fun x k =>
    limUnder atTop fun N => iteratedFDeriv ℝ k (f N) x
  have hp : ∀ k x, Tendsto (fun N => iteratedFDeriv ℝ k (f N) x) atTop (𝓝 (p x k)) :=
    fun k x => tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (hcauchy k x))
  have hrate : ∀ x k N, 1 ≤ N → ∀ z ∈ U x,
      ‖p z k - iteratedFDeriv ℝ k (f N) z‖ ≤ C x k / N := fun x k N hN z hz =>
    le_of_tendsto (((hp k z).sub_const _).norm)
      ((eventually_ge_atTop N).mono fun M hM => hC x k N M hN hM z hz)
  have hunif : ∀ x k, TendstoUniformlyOn (fun N => iteratedFDeriv ℝ k (f N)) (fun z => p z k)
      atTop (U x) := fun x k =>
    Metric.tendstoUniformlyOn_iff.2 fun ε hε => (hsmall (C x k) ε hε).mono fun N hN z hz => by
      rw [dist_eq_norm]; exact (hrate x k N hN.1 z hz).trans_lt hN.2
  have hcont : ∀ k, Continuous fun x => p x k := fun k => continuous_iff_continuousAt.2 fun x =>
    ((hunif x k).continuousOn (Eventually.of_forall fun N =>
      ((hf N).continuous_iteratedFDeriv (by exact_mod_cast le_top)).continuousOn).frequently).continuousAt
      (hU x)
  have hderiv : ∀ k x, HasFDerivAt (fun y => p y k) (p x (k + 1)).curryLeft x := by
    intro k x
    have hx : x ∈ interior (U x) := mem_interior_iff_mem_nhds.2 (hU x)
    refine hasFDerivAt_of_tendstoUniformlyOn (f := fun N => iteratedFDeriv ℝ k (f N))
      (f' := fun N z => (iteratedFDeriv ℝ (k + 1) (f N) z).curryLeft) (g := fun z => p z k)
      (g' := fun z => (p z (k + 1)).curryLeft) isOpen_interior ?_
      (fun N z _ => ((hf N).ftaylorSeries.fderiv k (by exact_mod_cast WithTop.coe_lt_top _) z))
      (fun z _ => hp k z) hx
    refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 ((hunif x (k + 1)).mono interior_subset) ε hε]
      with N hN z hz
    have e := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => X) G).dist_map
      (p z (k + 1)) (iteratedFDeriv ℝ (k + 1) (f N) z)
    exact e.trans_lt (hN z hz)
  have hT : HasFTaylorSeriesUpTo (⊤ : ℕ∞) (fun x => (p x 0).curry0) p :=
    ⟨fun x => rfl, fun k _ x => hderiv k x, fun k _ => hcont k⟩
  refine ⟨_, hT.contDiff, fun k x => ?_⟩
  rw [← hT.eq_iteratedFDeriv (by exact_mod_cast le_top) x]
  exact hp k x

end SmoothLimit

/-! ## Algebra of iterated derivatives of families -/

section Families

variable {n p : ℕ} {ι : Type*} [Fintype ι] {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem cellNorm_eq_sqrt_cellNormSq (U : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X) (l : Fin p → ℝ)
    (t : ℝ) : cellNorm (U l t) = √(cellNormSq U l t) := by
  rw [cellNorm_def, cellNormSq_def]

theorem iterD_append (α β : List (Dir n p)) (U : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X) :
    iterD (α ++ β) U = iterD β (iterD α U) := by
  induction α generalizing U with
  | nil => simp only [List.nil_append, iterD_nil]
  | cons s α ih => simpa only [List.cons_append, iterD_cons] using ih (s.d U)

theorem d_sub_family {s : Dir n p} {U W : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X}
    (hU : Differentiable ℝ ↿U) (hW : Differentiable ℝ ↿W) :
    s.d (fun l t y => U l t y - W l t y) = fun l t y => s.d U l t y - s.d W l t y :=
  funext fun _ => funext fun _ => funext fun _ => Dir.d_sub hU hW

theorem d_add_family {s : Dir n p} {U W : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X}
    (hU : Differentiable ℝ ↿U) (hW : Differentiable ℝ ↿W) :
    s.d (fun l t y => U l t y + W l t y) = fun l t y => s.d U l t y + s.d W l t y :=
  funext fun _ => funext fun _ => funext fun _ => Dir.d_add hU hW

theorem iterD_sub {U W : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X} (hU : IsPeriodicSmooth U)
    (hW : IsPeriodicSmooth W) (α : List (Dir n p)) :
    iterD α (fun l t y => U l t y - W l t y) = fun l t y => iterD α U l t y - iterD α W l t y := by
  induction α generalizing U W with
  | nil => simp only [iterD_nil]
  | cons s α ih =>
    simp only [iterD_cons]
    rw [d_sub_family hU.differentiable hW.differentiable]
    exact ih (hU.d s) (hW.d s)

theorem iterD_add {U W : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X} (hU : IsPeriodicSmooth U)
    (hW : IsPeriodicSmooth W) (α : List (Dir n p)) :
    iterD α (fun l t y => U l t y + W l t y) = fun l t y => iterD α U l t y + iterD α W l t y := by
  induction α generalizing U W with
  | nil => simp only [iterD_nil]
  | cons s α ih =>
    simp only [iterD_cons]
    rw [d_add_family hU.differentiable hW.differentiable]
    exact ih (hU.d s) (hW.d s)

theorem iterD_zero (α : List (Dir n p)) :
    iterD α (fun _ _ _ => (0 : X)) = fun _ _ _ => 0 := by
  induction α with
  | nil => simp only [iterD_nil]
  | cons s α ih =>
    simp only [iterD_cons]
    convert ih using 2
    funext l t y
    cases s <;> simp [Dir.d_self, Dir.d_space, Dir.d_time, Dir.d_param, dy_def, dt_def, dpar_def]

/-- A family vanishing for `t ≤ t₀` has derivatives vanishing for `t ≤ t₀`. -/
theorem d_eq_zero_of_le {U : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X} (hU : Differentiable ℝ ↿U)
    {t₀ : ℝ} (h0 : ∀ l t y, t ≤ t₀ → U l t y = 0) (s : Dir n p) :
    ∀ l t y, t ≤ t₀ → s.d U l t y = 0 := by
  intro l t y ht
  cases s with
  | self => simpa only [Dir.d_self] using h0 l t y ht
  | space i =>
    have : U l t = fun _ => 0 := funext fun y => h0 l t y ht
    simp [dy_def, this]
  | time =>
    have hd : Differentiable ℝ fun s => U l s y := hU.comp (f := fun s => (l, s, y)) (by fun_prop)
    have h1 : HasDerivWithinAt (fun s => U l s y) 0 (Iic t₀) t :=
      (hasDerivWithinAt_const t _ (0 : X)).congr (fun s hs => h0 l s y hs) (h0 l t y ht)
    rw [Dir.d_time, dt_apply]
    exact UniqueDiffWithinAt.eq_deriv _ (uniqueDiffOn_Iic t₀ t ht)
      (hd t).hasDerivAt.hasDerivWithinAt h1
  | param k =>
    have : (fun m => U m t y) = fun _ => 0 := funext fun m => h0 m t y ht
    simp [dpar_def, this]

theorem iterD_eq_zero_of_le {U : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X} (hU : IsPeriodicSmooth U)
    {t₀ : ℝ} (h0 : ∀ l t y, t ≤ t₀ → U l t y = 0) (α : List (Dir n p)) :
    ∀ l t y, t ≤ t₀ → iterD α U l t y = 0 := by
  induction α generalizing U with
  | nil => simpa only [iterD_nil] using h0
  | cons s α ih =>
    simpa only [iterD_cons] using ih (hU.d s) (d_eq_zero_of_le hU.differentiable h0 s)

/-- The derivative `dDir d` along an axis is `Dir.d` along the corresponding direction. -/
def axisDir : Axis p n → Dir n p
  | .inl k => .param k
  | .inr (.inl _) => .time
  | .inr (.inr i) => .space i

theorem dWord_eq_iterD (w : List (Axis p n)) (V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X) :
    dWord w V = iterD (w.reverse.map axisDir) V := by
  induction w with
  | nil => simp only [dWord_nil, List.reverse_nil, List.map_nil, iterD_nil]
  | cons d w ih =>
    rw [List.reverse_cons, List.map_append, iterD_append, ← ih]
    rcases d with k | _ | i <;>
      simp only [dWord_cons, dDir_inl, dDir_inr_inl, dDir_inr_inr, List.map_cons, List.map_nil,
        iterD_cons, iterD_nil, axisDir, Dir.d_param, Dir.d_time, Dir.d_space]

/-- `P_N` commutes with every partial derivative of a smooth periodic family. -/
theorem d_fourierProj {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι}
    (hV : IsPeriodicSmooth V) (N : ℕ) (s : Dir n p) :
    s.d (fun l t => fourierProj N (V l t)) = fun l t => fourierProj N (s.d V l t) := by
  cases s with
  | self => simp only [Dir.d_self]
  | space i => simpa only [Dir.d_space] using hV.dy_fourierProj N i
  | time => simpa only [Dir.d_time] using hV.dt_fourierProj N
  | param k => simpa only [Dir.d_param] using hV.dpar_fourierProj N k

theorem iterD_fourierProj {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι}
    (hV : IsPeriodicSmooth V) (N : ℕ) (α : List (Dir n p)) :
    iterD α (fun l t => fourierProj N (V l t)) = fun l t => fourierProj N (iterD α V l t) := by
  induction α generalizing V with
  | nil => simp only [iterD_nil]
  | cons s α ih =>
    simp only [iterD_cons]
    rw [d_fourierProj hV N s]
    exact ih (hV.d s)

/-- Derivatives of a family of trigonometric polynomials of degree `≤ N` are such families. -/
theorem iterD_mem_trigPoly {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι}
    (hV : IsPeriodicSmooth V) {N : ℕ} (hmem : ∀ l t, V l t ∈ trigPoly ι n N)
    (α : List (Dir n p)) (l : Fin p → ℝ) (t : ℝ) : iterD α V l t ∈ trigPoly ι n N := by
  have e : V = fun l t => fourierProj N (V l t) :=
    funext fun l => funext fun t => (fourierProj_eq_self (hmem l t)).symm
  rw [e, iterD_fourierProj hV N α]
  exact fourierProj_mem_trigPoly N _

/-! ### `L²(cell)` norms -/

omit [NormedSpace ℝ X] in
theorem norm_add_sq_le_two (a b : X) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := norm_add_le a b
  have h0 := norm_nonneg (a + b)
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

theorem cellNormSq_add_le {U W : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X} (hU : Continuous ↿U)
    (hW : Continuous ↿W) (l : Fin p → ℝ) (t : ℝ) :
    cellNormSq (fun l t y => U l t y + W l t y) l t ≤ 2 * cellNormSq U l t + 2 * cellNormSq W l t := by
  have hu := continuous_slice hU l t
  have hw := continuous_slice hW l t
  simp only [cellNormSq_def, cellIntegral_def]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (integrableOn_cell (by fun_prop))
    (integrableOn_cell (by fun_prop))]
  exact integral_mono (integrableOn_cell (by fun_prop)) (integrableOn_cell (by fun_prop))
    fun y => norm_add_sq_le_two _ _

theorem cellNormSq_sub_le {U W : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X} (hU : Continuous ↿U)
    (hW : Continuous ↿W) (l : Fin p → ℝ) (t : ℝ) :
    cellNormSq (fun l t y => U l t y - W l t y) l t ≤ 2 * cellNormSq U l t + 2 * cellNormSq W l t := by
  have h := cellNormSq_add_le (W := fun l t y => -W l t y) hU hW.neg l t
  simpa [cellNormSq_def, sub_eq_add_neg] using h

theorem cellNormSq_le_of_norm_le {U : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X} (hU : Continuous ↿U)
    {l : Fin p → ℝ} {t B : ℝ} (h : ∀ y, ‖U l t y‖ ≤ B) : cellNormSq U l t ≤ B ^ 2 := by
  have hu := continuous_slice hU l t
  rw [show B ^ 2 = cellIntegral (fun _ : Fin n → ℝ => B ^ 2) from (cellIntegral_const _).symm,
    cellNormSq_def, cellIntegral_def, cellIntegral_def]
  exact integral_mono (integrableOn_cell (by fun_prop)) (integrableOn_cell continuous_const)
    fun y => pow_le_pow_left₀ (norm_nonneg _) (h y) 2

theorem cellNormSq_le_firstOrderNormSq {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι}
    (hV : IsPeriodicSmooth V) (l : Fin p → ℝ) (t : ℝ) :
    cellNormSq V l t ≤ firstOrderNormSq V l t := by
  rw [firstOrderNormSq_eq hV]
  have := cellNormSq_nonneg (dt V) l t
  have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => cellNormSq_nonneg (dy i V) l t
  linarith

theorem firstOrderNormSq_eq_zero_of_le {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι}
    (hV : IsPeriodicSmooth V) {t₀ : ℝ} (h0 : ∀ l t y, t ≤ t₀ → V l t y = 0) (l : Fin p → ℝ)
    {t : ℝ} (ht : t ≤ t₀) : firstOrderNormSq V l t = 0 := by
  have h1 := d_eq_zero_of_le hV.differentiable h0 Dir.time
  have h2 := fun i => d_eq_zero_of_le hV.differentiable h0 (Dir.space i)
  simp only [Dir.d_time, Dir.d_space] at h1 h2
  simp [firstOrderNormSq_def, firstOrderDensity_def, h1 l t _ ht, h2 _ l t _ ht, h0 l t _ ht,
    cellIntegral_def]

/-- Derivatives up to order `m` of a smooth periodic family are bounded on `K × ℝⁿ`. -/
theorem exists_iterD_norm_le {U : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X} (hU : IsPeriodicSmooth U)
    {K : Set ((Fin p → ℝ) × ℝ)} (hK : IsCompact K) (m : ℕ) :
    ∃ B, ∀ α : List (Dir n p), α.length ≤ m → ∀ l t, (l, t) ∈ K → ∀ y, ‖iterD α U l t y‖ ≤ B := by
  have h : ∀ α : List (Dir n p), ∃ B, ∀ x ∈ K, ∀ y, ‖iterD α U x.1 x.2 y‖ ≤ B := fun α =>
    exists_bound_of_isPeriodic (f := fun x : (Fin p → ℝ) × ℝ => iterD α U x.1 x.2)
      ((hU.iterD α).smooth.continuous.comp (f := fun q : ((Fin p → ℝ) × ℝ) × (Fin n → ℝ) =>
        (q.1.1, q.1.2, q.2)) (by fun_prop)) (fun x => (hU.iterD α).periodic x.1 x.2) hK
  choose B hB using h
  set S := (List.finite_length_le (Dir n p) m).toFinset
  refine ⟨∑ α ∈ S, |B α|, fun α hα l t hlt y => ?_⟩
  have hαS : α ∈ S := (Set.Finite.mem_toFinset _).2 hα
  exact (hB α (l, t) hlt y).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun α => |B α|) (fun _ _ => abs_nonneg _) hαS))

end Families

/-! ## Linearity of the operator, and bounds of its derivatives -/

section Operator

variable {n p : ℕ} {ι : Type*} [Fintype ι]

theorem dt_sub_family {U W : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι}
    (hU : IsPeriodicSmooth U) (hW : IsPeriodicSmooth W) :
    dt (fun l t y => U l t y - W l t y) = fun l t y => dt U l t y - dt W l t y := by
  simpa only [Dir.d_time] using d_sub_family (s := Dir.time) hU.differentiable hW.differentiable

theorem dy_sub_family {U W : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι}
    (hU : IsPeriodicSmooth U) (hW : IsPeriodicSmooth W) (i : Fin n) :
    dy i (fun l t y => U l t y - W l t y) = fun l t y => dy i U l t y - dy i W l t y := by
  simpa only [Dir.d_space] using d_sub_family (s := Dir.space i) hU.differentiable hW.differentiable

/-- The operator is linear on smooth families. -/
theorem HypCoeffs.apply_sub (A : HypCoeffs p n ι)
    {V W : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι} (hV : IsPeriodicSmooth V)
    (hW : IsPeriodicSmooth W) :
    A.apply (fun l t y => V l t y - W l t y) = fun l t y => A.apply V l t y - A.apply W l t y := by
  have hdyy : ∀ i j, dy i (dy j (fun l t y => V l t y - W l t y)) =
      fun l t y => dy i (dy j V) l t y - dy i (dy j W) l t y := fun i j => by
    rw [dy_sub_family hV hW j]; exact dy_sub_family (hV.dy j) (hW.dy j) i
  funext l t y
  simp only [HypCoeffs.apply_def]
  simp only [hdyy]
  simp only [dt_sub_family hV hW, dy_sub_family hV hW, map_sub, smul_sub, Finset.sum_sub_distrib]
  abel

/-- Order zero: `‖A V‖_{L²(cell)}` is bounded by the `L²(cell)` norms of the derivatives of `V`
of order `≤ 2`, uniformly for `(l, t)` in a compact set. -/
theorem HypCoeffs.IsGood.exists_apply_bound {A : HypCoeffs p n ι} (hA : A.IsGood)
    {K : Set ((Fin p → ℝ) × ℝ)} (hK : IsCompact K) :
    ∃ C, ∀ l t, (l, t) ∈ K → ∀ (V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι) (ε : ℝ),
      IsPeriodicSmooth V → (∀ γ : List (Dir n p), γ.length ≤ 2 → cellNormSq (iterD γ V) l t ≤ ε) →
      cellNormSq (A.apply V) l t ≤ C * ε := by
  obtain ⟨M, hM0, hM⟩ := hA.exists_coeffBound hK
  set Q := (List.finite_length_le (Dir n p) 2).toFinset
  set c : ℝ := n * n + 1 + n + 1
  refine ⟨M ^ 2 * c ^ 2 * Q.card, fun l t hlt V ε hV hε => ?_⟩
  set S : (Fin n → ℝ) → ℝ := fun y => ∑ γ ∈ Q, ‖iterD γ V l t y‖ ^ 2
  have hQ : ∀ γ : List (Dir n p), γ.length ≤ 2 → γ ∈ Q := fun γ hγ =>
    (Set.Finite.mem_toFinset _).2 hγ
  have hw : ∀ γ : List (Dir n p), γ.length ≤ 2 → ∀ y, ‖iterD γ V l t y‖ ≤ √(S y) :=
    fun γ hγ y => by
      rw [← Real.sqrt_sq (norm_nonneg (iterD γ V l t y))]
      exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun γ => ‖iterD γ V l t y‖ ^ 2)
        (fun _ _ => sq_nonneg _) (hQ γ hγ))
  have hpt : ∀ y, ‖A.apply V l t y‖ ^ 2 ≤ M ^ 2 * c ^ 2 * S y := by
    intro y
    have hb := hM l t hlt y
    have e1 : ∀ i j, ‖A.a i j l t y • dy i (dy j V) l t y‖ ≤ M * √(S y) := fun i j => by
      have h := hw [Dir.space j, Dir.space i] (by simp) y
      simp only [iterD_cons, iterD_nil, Dir.d_space] at h
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hb.a i j) h (norm_nonneg _) hM0
    have e2 : ‖A.bt l t y (dt V l t y)‖ ≤ M * √(S y) := by
      have h := hw [Dir.time] (by simp) y
      simp only [iterD_cons, iterD_nil, Dir.d_time] at h
      exact ((A.bt l t y).le_opNorm _).trans (mul_le_mul hb.bt h (norm_nonneg _) hM0)
    have e3 : ∀ i, ‖A.b i l t y (dy i V l t y)‖ ≤ M * √(S y) := fun i => by
      have h := hw [Dir.space i] (by simp) y
      simp only [iterD_cons, iterD_nil, Dir.d_space] at h
      exact ((A.b i l t y).le_opNorm _).trans (mul_le_mul (hb.b i) h (norm_nonneg _) hM0)
    have e4 : ‖A.c l t y (V l t y)‖ ≤ M * √(S y) := by
      have h := hw [] (by simp) y
      simp only [iterD_nil] at h
      exact ((A.c l t y).le_opNorm _).trans (mul_le_mul hb.c h (norm_nonneg _) hM0)
    have h1 : ‖A.apply V l t y‖ ≤ M * c * √(S y) := by
      simp only [HypCoeffs.apply_def]
      refine norm_add₄_le.trans ((add_le_add (add_le_add (add_le_add
        ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => e1 i j))) e2)
        ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => e3 i))) e4).trans_eq ?_)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, c]
      ring
    have hS : 0 ≤ S y := Finset.sum_nonneg fun _ _ => sq_nonneg _
    calc ‖A.apply V l t y‖ ^ 2 ≤ (M * c * √(S y)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = M ^ 2 * c ^ 2 * S y := by rw [mul_pow, mul_pow, Real.sq_sqrt hS]
  have hcont : ∀ γ : List (Dir n p), Continuous fun y => ‖iterD γ V l t y‖ ^ 2 := fun γ =>
    (continuous_slice (hV.iterD γ).smooth.continuous l t).norm.pow 2
  calc cellNormSq (A.apply V) l t ≤ cellIntegral fun y => M ^ 2 * c ^ 2 * S y := by
        rw [cellNormSq_def, cellIntegral_def, cellIntegral_def]
        exact integral_mono (integrableOn_cell
          ((continuous_slice (hA.apply hV).smooth.continuous l t).norm.pow 2))
          (integrableOn_cell (continuous_const.mul (continuous_finsetSum _ fun γ _ => hcont γ)))
          hpt
    _ = M ^ 2 * c ^ 2 * ∑ γ ∈ Q, cellNormSq (iterD γ V) l t := by
        rw [cellIntegral_def, integral_const_mul, integral_finsetSum _ fun γ _ =>
          integrableOn_cell (hcont γ)]
        simp only [cellNormSq_def, cellIntegral_def]
    _ ≤ M ^ 2 * c ^ 2 * ∑ _γ ∈ Q, ε := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun γ hγ => hε γ ?_) (by positivity)
        have : γ ∈ {l : List (Dir n p) | l.length ≤ 2} := (Set.Finite.mem_toFinset _).1 hγ
        exact this
    _ = M ^ 2 * c ^ 2 * Q.card * ε := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **Derivatives of `A V`**: `‖∂^β (A V)‖_{L²(cell)}` with `|β| ≤ k` is bounded by the
`L²(cell)` norms of the derivatives of `V` of order `≤ k + 2`, uniformly for `(l, t)` in a
compact set (by the prolonged systems, as in `exists_iterD_bound`). -/
theorem HypCoeffs.IsGood.exists_iterD_apply_bound {A : HypCoeffs p n ι} (hA : A.IsGood)
    {K : Set ((Fin p → ℝ) × ℝ)} (hK : IsCompact K) (k : ℕ) :
    ∃ C, ∀ l t, (l, t) ∈ K → ∀ (V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι) (ε : ℝ),
      IsPeriodicSmooth V →
      (∀ γ : List (Dir n p), γ.length ≤ k + 2 → cellNormSq (iterD γ V) l t ≤ ε) →
      ∀ β : List (Dir n p), β.length ≤ k → cellNormSq (iterD β (A.apply V)) l t ≤ C * ε := by
  induction k generalizing ι with
  | zero =>
    obtain ⟨C, hC⟩ := hA.exists_apply_bound hK
    refine ⟨C, fun l t hlt V ε hV hε β hβ => ?_⟩
    obtain rfl : β = [] := List.length_eq_zero_iff.1 (Nat.le_zero.1 hβ)
    simpa only [iterD_nil] using hC l t hlt V ε hV hε
  | succ k ih =>
    obtain ⟨C₁, hC₁⟩ := ih hA
    obtain ⟨C₂, hC₂⟩ := ih hA.prolong
    set c : ℝ := (Fintype.card (Dir n p) : ℝ)
    refine ⟨|C₁| + |C₂| * c, fun l t hlt V ε hV hε β hβ => ?_⟩
    have hε0 : 0 ≤ ε := (cellNormSq_nonneg _ l t).trans (hε [] (by simp))
    have hc0 : 0 ≤ c := Nat.cast_nonneg _
    cases β with
    | nil =>
      refine (hC₁ l t hlt V ε hV (fun γ hγ => hε γ (by omega)) [] (by simp)).trans ?_
      have h1 := mul_le_mul_of_nonneg_right (le_abs_self C₁) hε0
      have h2 := mul_nonneg (mul_nonneg (abs_nonneg C₂) hc0) hε0
      nlinarith
    | cons s β =>
      have hβ' : β.length ≤ k := by simpa using hβ
      have hW := isPeriodicSmooth_prol hV
      have hεW : ∀ γ : List (Dir n p), γ.length ≤ k + 2 →
          cellNormSq (iterD γ (prol V)) l t ≤ c * ε := fun γ hγ => by
        rw [cellNormSq_eq_sum_block (hW.iterD γ).smooth.continuous]
        simp only [slot_iterD_prol hV]
        refine (Finset.sum_le_sum fun s _ => hε (s :: γ) (by simp; omega)).trans ?_
        simp [c]
      have key := hC₂ l t hlt (prol V) (c * ε) hW hεW β hβ'
      rw [prolong_apply_prol hA hV] at key
      have hAV := isPeriodicSmooth_prol (hA.apply hV)
      calc cellNormSq (iterD (s :: β) (A.apply V)) l t
          = cellNormSq (fun l t y => block s (iterD β (prol (A.apply V)) l t y)) l t := by
            rw [slot_iterD_prol (hA.apply hV)]
        _ ≤ ∑ s', cellNormSq (fun l t y => block s' (iterD β (prol (A.apply V)) l t y)) l t :=
            Finset.single_le_sum (f := fun s' => cellNormSq
              (fun l t y => block s' (iterD β (prol (A.apply V)) l t y)) l t)
              (fun _ _ => cellNormSq_nonneg _ _ _) (Finset.mem_univ s)
        _ = cellNormSq (iterD β (prol (A.apply V))) l t :=
            (cellNormSq_eq_sum_block (hAV.iterD β).smooth.continuous l t).symm
        _ ≤ C₂ * (c * ε) := key
        _ ≤ (|C₁| + |C₂| * c) * ε := by
            have h1 := mul_le_mul_of_nonneg_right (le_abs_self C₂) (mul_nonneg hc0 hε0)
            have h2 := mul_nonneg (abs_nonneg C₁) hε0
            nlinarith

end Operator

/-! ## Galerkin solutions and their estimates -/

section Galerkin

variable {n p : ℕ} {ι : Type*} [Fintype ι] {A : HypCoeffs p n ι}
  {F : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι}

/-- The right-hand side `A V + F` of the equation. -/
def galerkinRhs (A : HypCoeffs p n ι) (V F : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι) :
    (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι :=
  fun l t y => A.apply V l t y + F l t y

theorem isPeriodicSmooth_galerkinRhs (hA : A.IsGood)
    {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι} (hV : IsPeriodicSmooth V)
    (hF : IsPeriodicSmooth F) : IsPeriodicSmooth (galerkinRhs A V F) :=
  ⟨(hA.apply hV).smooth.add hF.smooth, fun l t => isPeriodic_iff.2 fun k y => by
    simp only [galerkinRhs, ((hA.apply hV).periodic l t).add_single k y,
      (hF.periodic l t).add_single k y]⟩

/-- The Galerkin projection of P6 is the Fourier projection of P2. -/
theorem galerkinProj_eq_fourierProj {u : (Fin n → ℝ) → EuclideanSpace ℝ ι} (hu : Continuous u)
    (N : ℕ) : galerkinProj N u = fourierProj N u :=
  (eq_galerkinProj hu (fourierProj_mem_trigPoly N u) fun _ hw =>
    cellIntegral_inner_sub_fourierProj hu hw).symm

/-- `V` is a Galerkin solution of order `N` vanishing for `t ≤ t₀`: `∂ₜ²V = P_N (A V + F)` with
values in `trigPoly ι n N`. -/
structure IsGalerkinSol (A : HypCoeffs p n ι)
    (F : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι) (t₀ : ℝ) (N : ℕ)
    (V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι) : Prop where
  smooth : IsPeriodicSmooth V
  mem : ∀ l t, V l t ∈ trigPoly ι n N
  zero : ∀ l t y, t ≤ t₀ → V l t y = 0
  eq : ∀ l t, dt (dt V) l t = fourierProj N (galerkinRhs A V F l t)

theorem exists_isGalerkinSol (hA : A.IsGood) (hF : IsPeriodicSmooth F) {t₀ : ℝ}
    (hF0 : ∀ l t y, t ≤ t₀ → F l t y = 0) (N : ℕ) : ∃ V, IsGalerkinSol A F t₀ N V := by
  obtain ⟨V, hV, hmem, -, h0, heq, -⟩ := exists_galerkin hA hF hF0 N
  refine ⟨V, hV, hmem, h0, fun l t => ?_⟩
  funext y
  rw [heq]
  exact congrFun (galerkinProj_eq_fourierProj (u := A.apply V l t + F l t)
    (continuous_slice (isPeriodicSmooth_galerkinRhs hA hV hF).smooth.continuous l t) N) y

theorem IsGalerkinSol.mono {t₀ t₀' : ℝ} {N : ℕ}
    {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι} (hV : IsGalerkinSol A F t₀ N V)
    (h : t₀' ≤ t₀) : IsGalerkinSol A F t₀' N V :=
  ⟨hV.smooth, hV.mem, fun l t y ht => hV.zero l t y (ht.trans h), hV.eq⟩

theorem IsGalerkinSol.residual_eq {t₀ : ℝ} {N : ℕ}
    {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι} (hV : IsGalerkinSol A F t₀ N V) :
    residual A V F =
      fun l t y => fourierProj N (galerkinRhs A V F l t) y - galerkinRhs A V F l t y := by
  funext l t y
  simp only [residual_def, hV.eq l t]
  rw [sub_sub]
  rfl

/-- The orthogonality hypothesis of `exists_iterD_bound` holds for Galerkin solutions:
`∂^α ∂ₜV` is a trigonometric polynomial of degree `≤ N` and `∂^α` of the residual is
`(P_N - 1) ∂^α (A V + F)`. -/
theorem IsGalerkinSol.orth (hA : A.IsGood) (hF : IsPeriodicSmooth F) {t₀ : ℝ} {N : ℕ}
    {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι} (hV : IsGalerkinSol A F t₀ N V)
    (α : List (Dir n p)) (l : Fin p → ℝ) (t : ℝ) :
    cellIntegral (fun y => ⟪iterD α (dt V) l t y, iterD α (residual A V F) l t y⟫) = 0 := by
  have hX := isPeriodicSmooth_galerkinRhs hA hV.smooth hF
  rw [hV.residual_eq, iterD_sub (isPeriodicSmooth_fourierProj hX.smooth N) hX,
    iterD_fourierProj hX]
  have hw : iterD α (dt V) l t ∈ trigPoly ι n N :=
    iterD_mem_trigPoly hV.smooth.dt (fun l t => by
      simpa only [iterD_cons, iterD_nil, Dir.d_time] using
        iterD_mem_trigPoly hV.smooth hV.mem [Dir.time] l t)
      α l t
  have h := cellIntegral_inner_sub_fourierProj
    (continuous_slice (hX.iterD α).smooth.continuous l t) hw
  have e : (fun y => ⟪iterD α (dt V) l t y,
      fourierProj N (iterD α (galerkinRhs A V F) l t) y - iterD α (galerkinRhs A V F) l t y⟫) =
      fun y => -⟪iterD α (galerkinRhs A V F) l t y -
        fourierProj N (iterD α (galerkinRhs A V F) l t) y, iterD α (dt V) l t y⟫ :=
    funext fun y => by rw [real_inner_comm, ← inner_neg_left, neg_sub]
  rw [cellIntegral_def] at h
  simp only [e, cellIntegral_def, integral_neg, h, neg_zero]

variable {t₀ t₁ : ℝ} {K : Set (Fin p → ℝ)}

/-- **A priori bounds** of Galerkin solutions: every derivative is bounded in `L²(cell)` on
`K × [t₀, t₁]`, uniformly in `N`. -/
theorem exists_galerkin_bound (hA : A.IsGood) (hF : IsPeriodicSmooth F) (ht : t₀ ≤ t₁)
    (hK : IsCompact K) (m : ℕ) :
    ∃ C, ∀ N V, IsGalerkinSol A F t₀ N V → ∀ α : List (Dir n p), α.length ≤ m →
      ∀ l ∈ K, ∀ t ∈ Icc t₀ t₁, cellNormSq (iterD α V) l t ≤ C := by
  obtain ⟨C₅, hC₅⟩ := hA.exists_iterD_bound hK t₀ t₁ m
  obtain ⟨B, hB⟩ := exists_iterD_norm_le hF (hK.prod isCompact_Icc) m
  refine ⟨C₅ * ((t₁ - t₀) * B ^ 2), fun N V hV α hα l hl t ht' => ?_⟩
  have hD : ∀ α : List (Dir n p), α.length ≤ m →
      firstOrderNormSq (iterD α V) l t₀ ≤ (t₁ - t₀) * B ^ 2 ∧
        ∫ s in t₀..t₁, cellNormSq (iterD α F) l s ≤ (t₁ - t₀) * B ^ 2 := by
    intro α hα
    constructor
    · rw [firstOrderNormSq_eq_zero_of_le (hV.smooth.iterD α)
        (iterD_eq_zero_of_le hV.smooth hV.zero α) l le_rfl]
      exact mul_nonneg (sub_nonneg.2 ht) (sq_nonneg B)
    · have := intervalIntegral.integral_mono_on (μ := volume) ht
        ((continuous_cellNormSq (hF.iterD α).smooth.continuous l).intervalIntegrable _ _)
        intervalIntegrable_const (fun s hs => cellNormSq_le_of_norm_le
          (hF.iterD α).smooth.continuous fun y => hB α hα l s ⟨hl, hs⟩ y)
      simpa using this
  exact (cellNormSq_le_firstOrderNormSq (hV.smooth.iterD α) l t).trans
    (hC₅ l hl V F _ hV.smooth hF (fun α _ t _ => hV.orth hA hF α l t) hD α hα t ht')

/-- **The residual of Galerkin solutions** `∂ₜ²V - A V - F = (P_N - 1)(A V + F)` is `O(N⁻¹)` in
`L²(cell)` with all its derivatives, on `K × [t₀, t₁]` and uniformly in `N`. -/
theorem exists_residual_bound (hA : A.IsGood) (hF : IsPeriodicSmooth F) (ht : t₀ ≤ t₁)
    (hK : IsCompact K) (m : ℕ) :
    ∃ C, ∀ N V, IsGalerkinSol A F t₀ N V → ∀ α : List (Dir n p), α.length ≤ m →
      ∀ l ∈ K, ∀ t ∈ Icc t₀ t₁,
        (2 * π * N) ^ 2 * cellNormSq (iterD α (residual A V F)) l t ≤ C := by
  obtain ⟨C₀, hC₀⟩ := exists_galerkin_bound hA hF ht hK (m + 3)
  obtain ⟨Cₜ, hCₜ⟩ := hA.exists_iterD_apply_bound (hK.prod isCompact_Icc) (m + 1)
  obtain ⟨B, hB⟩ := exists_iterD_norm_le hF (hK.prod isCompact_Icc) (m + 1)
  refine ⟨n * (2 * (Cₜ * C₀) + 2 * B ^ 2), fun N V hV α hα l hl t ht' => ?_⟩
  have hX := isPeriodicSmooth_galerkinRhs hA hV.smooth hF
  have hY : IsPeriodicSmooth (iterD α (galerkinRhs A V F)) := hX.iterD α
  have e : iterD α (residual A V F) = fun l t y =>
      fourierProj N (iterD α (galerkinRhs A V F) l t) y - iterD α (galerkinRhs A V F) l t y := by
    rw [hV.residual_eq, iterD_sub (isPeriodicSmooth_fourierProj hX.smooth N) hX,
      iterD_fourierProj hX]
  have hdy : ∀ i, cellNormSq (dy i (iterD α (galerkinRhs A V F))) l t ≤
      2 * (Cₜ * C₀) + 2 * B ^ 2 := by
    intro i
    have e2 : dy i (iterD α (galerkinRhs A V F)) = fun l t y =>
        iterD (α ++ [Dir.space i]) (A.apply V) l t y + iterD (α ++ [Dir.space i]) F l t y := by
      rw [show dy i (iterD α (galerkinRhs A V F)) =
        iterD (α ++ [Dir.space i]) (galerkinRhs A V F) by
          rw [iterD_append]; simp only [iterD_cons, iterD_nil, Dir.d_space]]
      exact iterD_add (hA.apply hV.smooth) hF _
    rw [e2]
    refine (cellNormSq_add_le ((hA.apply hV.smooth).iterD _).smooth.continuous
      (hF.iterD _).smooth.continuous l t).trans ?_
    have hlen : (α ++ [Dir.space i]).length ≤ m + 1 := by simp; omega
    have h1 := hCₜ l t ⟨hl, ht'⟩ V C₀ hV.smooth
      (fun γ hγ => hC₀ N V hV γ (by omega) l hl t ht') _ hlen
    have h2 := cellNormSq_le_of_norm_le (hF.iterD _).smooth.continuous
      fun y => hB _ hlen l t ⟨hl, ht'⟩ y
    linarith
  have htail := sq_mul_cellIntegral_sub_fourierProj_le
    ((hY.contDiff_slice l t).of_le (by exact_mod_cast le_top)) (hY.periodic l t) N
  rw [e]
  calc (2 * π * N) ^ 2 * cellNormSq (fun l t y =>
        fourierProj N (iterD α (galerkinRhs A V F) l t) y - iterD α (galerkinRhs A V F) l t y) l t
      = (2 * π * N) ^ 2 * cellIntegral (fun y => ‖iterD α (galerkinRhs A V F) l t y -
          fourierProj N (iterD α (galerkinRhs A V F) l t) y‖ ^ 2) := by
        simp only [cellNormSq_def, norm_sub_rev]
    _ ≤ ∑ i, cellNormSq (dy i (iterD α (galerkinRhs A V F))) l t := by
        simp only [cellNormSq_def, dy_def]
        exact htail
    _ ≤ ∑ _i : Fin n, (2 * (Cₜ * C₀) + 2 * B ^ 2) := Finset.sum_le_sum fun i _ => hdy i
    _ = _ := by simp; ring

theorem IsGalerkinSol.isPeriodicSmooth_sub {t₀ : ℝ} {N M : ℕ}
    {V W : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι} (hV : IsGalerkinSol A F t₀ N V)
    (hW : IsGalerkinSol A F t₀ M W) : IsPeriodicSmooth fun l t y => W l t y - V l t y :=
  ⟨hW.smooth.smooth.sub hV.smooth.smooth, fun l t => isPeriodic_iff.2 fun k y => by
    simp only [(hW.smooth.periodic l t).add_single k y, (hV.smooth.periodic l t).add_single k y]⟩

/-- **The Cauchy estimate.** For `N ≤ M`, `D = V_M - V_N` solves `∂ₜ²D = A D + G` with
`G = R_M - R_N` the difference of the residuals, so by `exists_iterD_bound` (with zero data at
`t₀`) and `exists_residual_bound`, `N² ‖∂^α D‖²_{L²(cell)}` is bounded on `K × [t₀, t₁]`
uniformly in `N` and `M`. -/
theorem exists_galerkin_cauchy (hA : A.IsGood) (hF : IsPeriodicSmooth F) (ht : t₀ ≤ t₁)
    (hK : IsCompact K) (m : ℕ) :
    ∃ C, ∀ N M V W, 1 ≤ N → N ≤ M → IsGalerkinSol A F t₀ N V → IsGalerkinSol A F t₀ M W →
      ∀ α : List (Dir n p), α.length ≤ m → ∀ l ∈ K, ∀ t ∈ Icc t₀ t₁,
        (N : ℝ) ^ 2 * cellNormSq (iterD α (fun l t y => W l t y - V l t y)) l t ≤ C := by
  obtain ⟨C₁, hC₁⟩ := exists_residual_bound hA hF ht hK m
  obtain ⟨C₅, hC₅⟩ := hA.exists_iterD_bound hK t₀ t₁ m
  set C₁' := max C₁ 0
  refine ⟨C₅ * ((t₁ - t₀) * (4 * C₁' / (2 * π) ^ 2)),
    fun N M V W hN hNM hV hW α hα l hl t ht' => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hres : ∀ (L : ℕ) U, N ≤ L → IsGalerkinSol A F t₀ L U →
      ∀ α : List (Dir n p), α.length ≤ m → ∀ s ∈ Icc t₀ t₁,
        cellNormSq (iterD α (residual A U F)) l s ≤ C₁' / (2 * π * N) ^ 2 := by
    intro L U hNL hU α hα s hs
    have h := (hC₁ L U hU α hα l hl s hs).trans (le_max_left C₁ 0)
    have hNL' : (N : ℝ) ≤ L := by exact_mod_cast hNL
    rw [le_div_iff₀ (by positivity)]
    have : (2 * π * N) ^ 2 ≤ (2 * π * L) ^ 2 := pow_le_pow_left₀ (by positivity) (by gcongr) 2
    nlinarith [cellNormSq_nonneg (iterD α (residual A U F)) l s]
  have hD := hV.isPeriodicSmooth_sub hW
  have hRW := isPeriodicSmooth_residual hA hW.smooth hF
  have hRV := isPeriodicSmooth_residual hA hV.smooth hF
  have hG : IsPeriodicSmooth fun l t y => residual A W F l t y - residual A V F l t y :=
    ⟨hRW.smooth.sub hRV.smooth, fun l t => isPeriodic_iff.2 fun k y => by
      simp only [(hRW.periodic l t).add_single k y, (hRV.periodic l t).add_single k y]⟩
  have hres0 : residual A (fun l t y => W l t y - V l t y)
      (fun l t y => residual A W F l t y - residual A V F l t y) = fun _ _ _ => 0 := by
    funext l t y
    simp only [residual_def]
    rw [dt_sub_family hW.smooth hV.smooth, dt_sub_family hW.smooth.dt hV.smooth.dt,
      A.apply_sub hW.smooth hV.smooth]
    beta_reduce
    abel
  set Dat : ℝ := (t₁ - t₀) * (4 * C₁' / (2 * π * N) ^ 2)
  have hdata : ∀ α : List (Dir n p), α.length ≤ m →
      firstOrderNormSq (iterD α (fun l t y => W l t y - V l t y)) l t₀ ≤ Dat ∧
        ∫ s in t₀..t₁, cellNormSq (iterD α
          (fun l t y => residual A W F l t y - residual A V F l t y)) l s ≤ Dat := by
    intro α hα
    constructor
    · rw [firstOrderNormSq_eq_zero_of_le (hD.iterD α) (iterD_eq_zero_of_le hD
        (fun l t y h => by simp [hW.zero l t y h, hV.zero l t y h]) α) l le_rfl]
      exact mul_nonneg (sub_nonneg.2 ht) (by positivity)
    · rw [iterD_sub hRW hRV]
      have := intervalIntegral.integral_mono_on (μ := volume) ht
        ((continuous_cellNormSq ((hRW.iterD α).smooth.sub (hRV.iterD α).smooth).continuous
          l).intervalIntegrable _ _)
        intervalIntegrable_const (fun s hs => (cellNormSq_sub_le (hRW.iterD α).smooth.continuous
          (hRV.iterD α).smooth.continuous l s).trans (by
            have h1 := hres M W hNM hW α hα s hs
            have h2 := hres N V le_rfl hV α hα s hs
            show _ ≤ 4 * C₁' / (2 * π * N) ^ 2
            rw [show 4 * C₁' / (2 * π * N) ^ 2 =
              2 * (C₁' / (2 * π * N) ^ 2) + 2 * (C₁' / (2 * π * N) ^ 2) by ring]
            linarith))
      rwa [intervalIntegral.integral_const, smul_eq_mul] at this
  have horth : ∀ α : List (Dir n p), α.length ≤ m → ∀ t ∈ Icc t₀ t₁,
      cellIntegral (fun y => ⟪iterD α (dt (fun l t y => W l t y - V l t y)) l t y,
        iterD α (residual A (fun l t y => W l t y - V l t y)
          (fun l t y => residual A W F l t y - residual A V F l t y)) l t y⟫) = 0 := by
    intro α _ t _
    simp [hres0, iterD_zero, cellIntegral_def]
  have key := hC₅ l hl _ _ Dat hD hG horth hdata α hα t ht'
  calc (N : ℝ) ^ 2 * cellNormSq (iterD α (fun l t y => W l t y - V l t y)) l t
      ≤ (N : ℝ) ^ 2 * (C₅ * Dat) :=
        mul_le_mul_of_nonneg_left ((cellNormSq_le_firstOrderNormSq (hD.iterD α) l t).trans key)
          (sq_nonneg _)
    _ = _ := by simp only [Dat]; field_simp

/-- **`C^k` Cauchy estimate in sup norm** on `K × [t₀, t₁] × ℝⁿ` (P3 applied to `V_M - V_N`). -/
theorem exists_galerkin_cauchy_sup (hA : A.IsGood) (hF : IsPeriodicSmooth F) (ht : t₀ ≤ t₁)
    (hK : IsCompact K) (k : ℕ) :
    ∃ C, ∀ N M V W, 1 ≤ N → N ≤ M → IsGalerkinSol A F t₀ N V → IsGalerkinSol A F t₀ M W →
      ∀ l ∈ K, ∀ t ∈ Icc t₀ t₁, ∀ y,
        ‖iteratedFDeriv ℝ k ↿W (l, t, y) - iteratedFDeriv ℝ k ↿V (l, t, y)‖ ≤ C / N := by
  obtain ⟨C₆, hC₆⟩ := exists_galerkin_cauchy hA hF ht hK (k + n)
  refine ⟨(p + 1 + n) ^ k * 2 ^ n * √(max C₆ 0),
    fun N M V W hN hNM hV hW l hl t ht' y => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hD := hV.isPeriodicSmooth_sub hW
  have hε : ∀ w : List (Axis p n), w.length ≤ k + n →
      cellNorm (dWord w (fun l t y => W l t y - V l t y) l t) ≤ √(max C₆ 0) / N := by
    intro w hw
    rw [dWord_eq_iterD]
    have h := hC₆ N M V W hN hNM hV hW (w.reverse.map axisDir) (by simpa using hw) l hl t ht'
    rw [cellNorm_eq_sqrt_cellNormSq]
    rw [le_div_iff₀ hNpos, ← Real.sqrt_sq hNpos.le, ← Real.sqrt_mul (cellNormSq_nonneg _ _ _)]
    exact Real.sqrt_le_sqrt (by nlinarith [le_max_left C₆ 0])
  have h := norm_iteratedFDeriv_le_of_cellNorm_le hD k hε y
  have e : iteratedFDeriv ℝ k ↿(fun l t y => W l t y - V l t y) (l, t, y) =
      iteratedFDeriv ℝ k ↿W (l, t, y) - iteratedFDeriv ℝ k ↿V (l, t, y) :=
    iteratedFDeriv_sub_apply (f := ↿W) (g := ↿V)
      (hW.smooth.smooth.contDiffAt.of_le (by exact_mod_cast le_top))
      (hV.smooth.smooth.contDiffAt.of_le (by exact_mod_cast le_top))
  rw [e] at h
  exact h.trans_eq (by ring)

/-- The residual of Galerkin solutions is `O(N⁻¹)` in sup norm on `K × [t₀, t₁] × ℝⁿ`. -/
theorem exists_residual_sup (hA : A.IsGood) (hF : IsPeriodicSmooth F) (ht : t₀ ≤ t₁)
    (hK : IsCompact K) :
    ∃ C, ∀ N V, 1 ≤ N → IsGalerkinSol A F t₀ N V → ∀ l ∈ K, ∀ t ∈ Icc t₀ t₁, ∀ y,
      ‖residual A V F l t y‖ ≤ C / N := by
  obtain ⟨C₁, hC₁⟩ := exists_residual_bound hA hF ht hK n
  refine ⟨2 ^ n * (√(max C₁ 0) / (2 * π)), fun N V hN hV l hl t ht' y => ?_⟩
  have hNpos : (0 : ℝ) < 2 * π * N := by have : (0 : ℝ) < N := by exact_mod_cast hN
                                         positivity
  have hR := isPeriodicSmooth_residual hA hV.smooth hF
  have hε : ∀ w : List (Axis p n), w.length ≤ 0 + n →
      cellNorm (dWord w (residual A V F) l t) ≤ √(max C₁ 0) / (2 * π * N) := by
    intro w hw
    rw [dWord_eq_iterD]
    have h := hC₁ N V hV (w.reverse.map axisDir) (by simpa using hw) l hl t ht'
    rw [cellNorm_eq_sqrt_cellNormSq]
    rw [le_div_iff₀ hNpos, ← Real.sqrt_sq hNpos.le, ← Real.sqrt_mul (cellNormSq_nonneg _ _ _)]
    exact Real.sqrt_le_sqrt (by nlinarith [le_max_left C₁ 0])
  have h := norm_iteratedFDeriv_le_of_cellNorm_le hR 0 hε y
  rw [norm_iteratedFDeriv_zero] at h
  refine h.trans_eq ?_
  have : (N : ℝ) ≠ 0 := by have : (0 : ℝ) < N := by exact_mod_cast hN
                           exact this.ne'
  field_simp

end Galerkin

/-! ## Existence and uniqueness -/

section Solution

variable {n p : ℕ} {ι : Type*} [Fintype ι] {A : HypCoeffs p n ι}

/-- **Existence of smooth periodic solutions**: for good coefficients and a smooth periodic
source vanishing for `t ≤ t₀`, `∂ₜ²V = A V + F` has a smooth periodic solution vanishing for
`t ≤ t₀`. It is the limit of the Galerkin solutions `V_N` (`exists_isGalerkinSol`), which
converge with all derivatives locally uniformly (`exists_galerkin_cauchy_sup`,
`exists_contDiff_limit`); the residuals converge to `0` (`exists_residual_sup`). -/
theorem exists_periodic_solution (hA : A.IsGood)
    {F : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι} (hF : IsPeriodicSmooth F)
    {t₀ : ℝ} (hF0 : ∀ l t y, t ≤ t₀ → F l t y = 0) :
    ∃ V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι, IsPeriodicSmooth V ∧
      (∀ l t y, t ≤ t₀ → V l t y = 0) ∧ ∀ l t y, dt (dt V) l t y = A.apply V l t y + F l t y := by
  choose V hV using fun N => exists_isGalerkinSol hA hF hF0 N
  have hloc : ∀ x : (Fin p → ℝ) × ℝ × (Fin n → ℝ), ∃ U ∈ 𝓝 x, ∀ k, ∃ C, ∀ N M, 1 ≤ N → N ≤ M →
      ∀ z ∈ U, ‖iteratedFDeriv ℝ k ↿(V M) z - iteratedFDeriv ℝ k ↿(V N) z‖ ≤ C / N := by
    rintro ⟨l₀, τ, y₀⟩
    have hab : min (τ - 1) t₀ ≤ τ + 1 := (min_le_left _ _).trans (by linarith)
    refine ⟨Metric.closedBall l₀ 1 ×ˢ Icc (τ - 1) (τ + 1) ×ˢ univ, ?_, fun k => ?_⟩
    · exact prod_mem_nhds (Metric.closedBall_mem_nhds _ one_pos)
        (prod_mem_nhds (Icc_mem_nhds (by linarith) (by linarith)) univ_mem)
    · obtain ⟨C, hC⟩ := exists_galerkin_cauchy_sup hA hF hab (isCompact_closedBall l₀ 1) k
      refine ⟨C, fun N M hN hNM z hz => ?_⟩
      obtain ⟨hz1, hz2, -⟩ := hz
      exact hC N M (V N) (V M) hN hNM ((hV N).mono (min_le_right _ _))
        ((hV M).mono (min_le_right _ _)) z.1 hz1 z.2.1 ⟨(min_le_left _ _).trans hz2.1, hz2.2⟩ z.2.2
  obtain ⟨g, hg, hlim⟩ := exists_contDiff_limit (fun N => (hV N).smooth.smooth) hloc
  set U : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι := fun l t y => g (l, t, y)
  have hpt : ∀ x, Tendsto (fun N => ↿(V N) x) atTop (𝓝 (g x)) := fun x => by
    have := ((continuous_eval_const
      (fun _ : Fin 0 => (0 : (Fin p → ℝ) × ℝ × (Fin n → ℝ)))).tendsto _).comp (hlim 0 x)
    simpa [Function.comp_def] using this
  have hU : IsPeriodicSmooth U := ⟨hg, fun l t => isPeriodic_iff.2 fun i y =>
    tendsto_nhds_unique (hpt (l, t, y + Pi.single i 1))
      (by simpa [((hV _).smooth.periodic l t).add_single i y] using hpt (l, t, y))⟩
  have hU0 : ∀ l t y, t ≤ t₀ → U l t y = 0 := fun l t y ht =>
    tendsto_nhds_unique (hpt (l, t, y)) (by simp [(hV _).zero l t y ht])
  have hword : ∀ (w : List (Axis p n)) l t y,
      Tendsto (fun N => dWord w (V N) l t y) atTop (𝓝 (dWord w U l t y)) := by
    intro w l t y
    have key : ∀ W : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι, IsPeriodicSmooth W →
        dWord w W l t y = iteratedFDeriv ℝ (w.map dirVec).length ↿W (l, t, y) (w.map dirVec).get :=
      fun W hW => by
        rw [iteratedFDeriv_eq_dirDeriv hW.smooth, List.ofFn_get, ← uncurry_dWord hW]; rfl
    simp only [key _ (hV _).smooth, key U hU]
    exact ((continuous_eval_const _).tendsto _).comp (hlim _ (l, t, y))
  refine ⟨U, hU, hU0, fun l t y => ?_⟩
  have hres : Tendsto (fun N => residual A (V N) F l t y) atTop (𝓝 (residual A U F l t y)) := by
    have hTT : Tendsto (fun N => dt (dt (V N)) l t y) atTop (𝓝 (dt (dt U) l t y)) := by
      simpa only [dWord_cons, dWord_nil, dDir_inr_inl] using
        hword [Sum.inr (Sum.inl ()), Sum.inr (Sum.inl ())] l t y
    have hT : Tendsto (fun N => dt (V N) l t y) atTop (𝓝 (dt U l t y)) := by
      simpa only [dWord_cons, dWord_nil, dDir_inr_inl] using hword [Sum.inr (Sum.inl ())] l t y
    have hYY : ∀ i j, Tendsto (fun N => dy i (dy j (V N)) l t y) atTop
        (𝓝 (dy i (dy j U) l t y)) := fun i j => by
      simpa only [dWord_cons, dWord_nil, dDir_inr_inr] using
        hword [Sum.inr (Sum.inr i), Sum.inr (Sum.inr j)] l t y
    have hY : ∀ i, Tendsto (fun N => dy i (V N) l t y) atTop (𝓝 (dy i U l t y)) := fun i => by
      simpa only [dWord_cons, dWord_nil, dDir_inr_inr] using hword [Sum.inr (Sum.inr i)] l t y
    have h0 : Tendsto (fun N => V N l t y) atTop (𝓝 (U l t y)) := by
      simpa only [dWord_nil] using hword [] l t y
    simp only [residual_def, HypCoeffs.apply_def]
    refine (hTT.sub ?_).sub tendsto_const_nhds
    exact (((tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
      (hYY i j).const_smul (A.a i j l t y)).add
      (((A.bt l t y).continuous.tendsto _).comp hT)).add
      (tendsto_finsetSum _ fun i _ =>
        ((A.b i l t y).continuous.tendsto _).comp (hY i))).add
      (((A.c l t y).continuous.tendsto _).comp h0)
  have hsmall : Tendsto (fun N => residual A (V N) F l t y) atTop (𝓝 0) := by
    obtain ⟨C, hC⟩ := exists_residual_sup hA hF (min_le_max (a := t) (b := t₀))
      (isCompact_singleton (x := l))
    refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat C)
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact hC N (V N) hN ((hV N).mono (min_le_right _ _)) l rfl t
      ⟨min_le_left _ _, le_max_left _ _⟩ y
  have h := tendsto_nhds_unique hres hsmall
  simp only [residual_def] at h
  rwa [sub_sub, sub_eq_zero] at h

/-- **Uniqueness**: a smooth periodic solution of `∂ₜ²V = A V` vanishing for `t ≤ t₀` vanishes
(the energy estimate with zero data). -/
theorem eq_zero_of_periodic_solution (hA : A.IsGood)
    {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι} (hV : IsPeriodicSmooth V) {t₀ : ℝ}
    (hV0 : ∀ l t y, t ≤ t₀ → V l t y = 0) (heq : ∀ l t y, dt (dt V) l t y = A.apply V l t y)
    (l : Fin p → ℝ) (t : ℝ) (y : Fin n → ℝ) : V l t y = 0 := by
  rcases le_or_gt t t₀ with ht | ht
  · exact hV0 l t y ht
  obtain ⟨C, hC⟩ := hA.exists_firstOrder_bound (isCompact_singleton (x := l)) t₀ t
  have h := hC l rfl V (fun _ _ _ => 0) 0 hV continuous_const
    (fun s _ => by simp [residual_def, heq, cellIntegral_def])
    (firstOrderNormSq_eq_zero_of_le hV hV0 l le_rfl).le (by simp [cellNormSq_def,
      cellIntegral_def]) t
    ⟨ht.le, le_rfl⟩
  have h0 : cellIntegral (fun y => ⟪V l t y, V l t y⟫) = 0 := by
    have := (cellNormSq_le_firstOrderNormSq hV l t).trans (h.trans_eq (mul_zero C))
    simp only [real_inner_self_eq_norm_sq]
    rw [cellNormSq_def] at this
    exact le_antisymm this (by simpa only [cellNormSq_def] using cellNormSq_nonneg V l t)
  exact congrFun (eq_zero_of_cellIntegral_inner_self (continuous_slice hV.smooth.continuous l t)
    (hV.periodic l t) h0) y

end Solution

end

end LorentzianCalderon.PDE
