module

public import LorentzianCalderon.PDE.Partial

public section

/-!
# The energy estimate of the periodic core

For `∂ₜ²V = a^{ij} ∂ᵢ∂ⱼV + Bₜ ∂ₜV + Bⁱ ∂ᵢV + C V + F` on the torus,
the energy

`E(t) = ∫_cell (|∂ₜV|² + a^{ij} ⟨∂ᵢV, ∂ⱼV⟩ + |V|²)`

satisfies `E' ≤ C E + ‖F‖²_{L²(cell)}` on `K × [t₀, t₁]`, hence the Grönwall bound
`energy_le`. Only the orthogonality `∫_cell ⟨∂ₜV, ∂ₜ²V - A V - F⟩ = 0` is used, which holds for
exact solutions and for Galerkin solutions alike.

The proof is pointwise: `∂ₜ e = 2⟨∂ₜV, ∂ₜ²V - A V - F⟩ + 2 ∂ᵢΦⁱ + q` with
`Φⁱ = a^{ij} ⟨∂ₜV, ∂ⱼV⟩` (`a` symmetric), and `|q| ≤ K (|∂ₜV|² + Σ|∂ᵢV|² + |V|²) + |F|²`; the
divergence integrates to zero over the cell. With the uniform positivity of `a`,
`energy_ge` bounds `|∂ₜV|² + Σ|∂ᵢV|² + |V|²` in `L²(cell)` by the energy, and `energy_le_mul`
bounds the energy by it.
-/

namespace LorentzianCalderon.PDE

noncomputable section
open scoped ContDiff RealInnerProductSpace Topology
open Set MeasureTheory Function Real

variable {n p : ℕ} {ι : Type*} [Fintype ι]

/-- `‖U(l, t)‖²_{L²(cell)}`. -/
def cellNormSq {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (U : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X) (l : Fin p → ℝ) (t : ℝ) : ℝ :=
  cellIntegral fun y => ‖U l t y‖ ^ 2

theorem cellNormSq_def {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (U : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X) (l : Fin p → ℝ) (t : ℝ) :
    cellNormSq U l t =
      cellIntegral fun y => ‖U l t y‖ ^ 2 := by rfl

/-- The density `|∂ₜV|² + Σᵢ |∂ᵢV|² + |V|²`. -/
def firstOrderDensity (V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι) :
    (Fin p → ℝ) → ℝ → (Fin n → ℝ) → ℝ :=
  fun l t y => ‖dt V l t y‖ ^ 2 + ∑ i, ‖dy i V l t y‖ ^ 2 + ‖V l t y‖ ^ 2

theorem firstOrderDensity_def (V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι) :
    firstOrderDensity V =
      fun l t y => ‖dt V l t y‖ ^ 2 + ∑ i, ‖dy i V l t y‖ ^ 2 + ‖V l t y‖ ^ 2 := by rfl

/-- `‖∂ₜV‖² + Σᵢ ‖∂ᵢV‖² + ‖V‖²` in `L²(cell)` (see `firstOrderNormSq_eq`). -/
def firstOrderNormSq (V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι)
    (l : Fin p → ℝ) (t : ℝ) : ℝ :=
  cellIntegral (firstOrderDensity V l t)

theorem firstOrderNormSq_def (V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι)
    (l : Fin p → ℝ) (t : ℝ) :
    firstOrderNormSq V l t =
      cellIntegral (firstOrderDensity V l t) := by rfl

/-- The energy density `|∂ₜV|² + a^{ij} ⟨∂ᵢV, ∂ⱼV⟩ + |V|²`. -/
def energyDensity (A : HypCoeffs p n ι)
    (V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι) :
    (Fin p → ℝ) → ℝ → (Fin n → ℝ) → ℝ :=
  fun l t y => ‖dt V l t y‖ ^ 2 +
    ∑ i, ∑ j, A.a i j l t y * ⟪dy i V l t y, dy j V l t y⟫ + ‖V l t y‖ ^ 2

/-- The energy `E(t) = ∫_cell (|∂ₜV|² + a^{ij} ⟨∂ᵢV, ∂ⱼV⟩ + |V|²)`. -/
def energy (A : HypCoeffs p n ι) (V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι)
    (l : Fin p → ℝ) (t : ℝ) : ℝ :=
  cellIntegral (energyDensity A V l t)

/-! ## Elementary facts -/

theorem IsPeriodicSmooth.differentiable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X} (hV : IsPeriodicSmooth V) :
    Differentiable ℝ ↿V :=
  hV.smooth.differentiable (by simp)

theorem continuous_slice {X : Type*} [TopologicalSpace X]
    {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X} (hV : Continuous ↿V) (l : Fin p → ℝ) (t : ℝ) :
    Continuous (V l t) :=
  hV.comp (f := fun y => (l, t, y)) (by fun_prop)

theorem contDiff_slice {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X} {m : ℕ∞ω} (hV : ContDiff ℝ m ↿V) (l : Fin p → ℝ)
    (t : ℝ) : ContDiff ℝ m (V l t) :=
  hV.comp (f := fun y => (l, t, y)) (by fun_prop)

theorem cellNormSq_nonneg {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (U : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X) (l : Fin p → ℝ) (t : ℝ) : 0 ≤ cellNormSq U l t := by
  rw [cellNormSq, cellIntegral_def]
  exact setIntegral_nonneg measurableSet_cell fun _ _ => sq_nonneg _

theorem continuous_cellNormSq {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {U : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X} (hU : Continuous ↿U) (l : Fin p → ℝ) :
    Continuous (cellNormSq U l) := by
  have h : Continuous fun q : ℝ × (Fin n → ℝ) => U l q.1 q.2 :=
    hU.comp (f := fun q : ℝ × (Fin n → ℝ) => (l, q.1, q.2)) (by fun_prop)
  show Continuous fun t => cellIntegral fun y => ‖U l t y‖ ^ 2
  simp only [cellIntegral_def]
  exact continuous_parametric_integral_of_continuous (f := fun t y => ‖U l t y‖ ^ 2)
    (by fun_prop) isCompact_cell

theorem firstOrderNormSq_eq {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι}
    (hV : IsPeriodicSmooth V) (l : Fin p → ℝ) (t : ℝ) :
    firstOrderNormSq V l t = cellNormSq (dt V) l t + ∑ i, cellNormSq (dy i V) l t +
      cellNormSq V l t := by
  have h0 := continuous_slice hV.smooth.continuous l t
  have ht := continuous_slice hV.dt.smooth.continuous l t
  have hy i := continuous_slice (hV.dy i).smooth.continuous l t
  simp only [firstOrderNormSq, firstOrderDensity, cellNormSq, cellIntegral_def]
  rw [integral_add (f := fun y => ‖dt V l t y‖ ^ 2 + ∑ i, ‖dy i V l t y‖ ^ 2)
      (g := fun y => ‖V l t y‖ ^ 2) (integrableOn_cell (by fun_prop))
      (integrableOn_cell (by fun_prop)),
    integral_add (f := fun y => ‖dt V l t y‖ ^ 2) (g := fun y => ∑ i, ‖dy i V l t y‖ ^ 2)
      (integrableOn_cell (by fun_prop)) (integrableOn_cell (by fun_prop)),
    integral_finsetSum _ fun i _ => integrableOn_cell (by fun_prop)]

theorem mul_le_of_sq_le {x y S : ℝ} (_hx0 : 0 ≤ x) (_hy0 : 0 ≤ y) (hx : x ^ 2 ≤ S)
    (hy : y ^ 2 ≤ S) : x * y ≤ S := by
  nlinarith [sq_nonneg (x - y)]

theorem abs_inner_le_of_sq_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x y : E} {S : ℝ} (hx : ‖x‖ ^ 2 ≤ S) (hy : ‖y‖ ^ 2 ≤ S) : |⟪x, y⟫| ≤ S :=
  (abs_real_inner_le_norm x y).trans (mul_le_of_sq_le (norm_nonneg _) (norm_nonneg _) hx hy)

theorem abs_mul_inner_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x y : E} {c M S : ℝ} (hc : |c| ≤ M) (hx : ‖x‖ ^ 2 ≤ S) (hy : ‖y‖ ^ 2 ≤ S) :
    |c * ⟪x, y⟫| ≤ M * S := by
  rw [abs_mul]
  exact mul_le_mul hc (abs_inner_le_of_sq_le hx hy) (abs_nonneg _) ((abs_nonneg c).trans hc)

theorem abs_inner_clm_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x y : E} {L : E →L[ℝ] E} {M S : ℝ} (hL : ‖L‖ ≤ M) (hx : ‖x‖ ^ 2 ≤ S) (hy : ‖y‖ ^ 2 ≤ S) :
    |⟪x, L y⟫| ≤ M * S := by
  have hxy := mul_le_of_sq_le (norm_nonneg x) (norm_nonneg y) hx hy
  calc |⟪x, L y⟫| ≤ ‖x‖ * ‖L y‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖x‖ * (M * ‖y‖) := mul_le_mul_of_nonneg_left
        ((L.le_opNorm y).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))) (norm_nonneg _)
    _ = M * (‖x‖ * ‖y‖) := by ring
    _ ≤ M * S := mul_le_mul_of_nonneg_left hxy ((norm_nonneg L).trans hL)

/-- A positive definite scalar matrix acts positively on vectors of `EuclideanSpace`:
`κ Σᵢ |Xᵢ|² ≤ a^{ij} ⟨Xᵢ, Xⱼ⟩`, coordinatewise. -/
theorem le_sum_mul_inner (a : Fin n → Fin n → ℝ) {κ : ℝ}
    (h : ∀ ξ : Fin n → ℝ, κ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a i j * ξ i * ξ j)
    (X : Fin n → EuclideanSpace ℝ ι) :
    κ * ∑ i, ‖X i‖ ^ 2 ≤ ∑ i, ∑ j, a i j * ⟪X i, X j⟫ := by
  simp only [EuclideanSpace.norm_sq_eq, PiLp.inner_apply, Real.norm_eq_abs, sq_abs]
  have hl : κ * ∑ i, ∑ r, (X i).ofLp r ^ 2 = ∑ r, κ * ∑ i, (X i).ofLp r ^ 2 := by
    conv_lhs => rw [Finset.sum_comm]
    rw [Finset.mul_sum]
  have hr : ∑ i, ∑ j, a i j * ∑ r, ⟪(X i).ofLp r, (X j).ofLp r⟫ =
      ∑ r, ∑ i, ∑ j, a i j * (X i).ofLp r * (X j).ofLp r := by
    simp only [Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun r _ => ?_
    simp only [inner_apply]
    ring
  rw [hl, hr]
  exact Finset.sum_le_sum fun r _ => h fun i => (X i).ofLp r

/-! ## Bounds of the coefficients -/

theorem HypCoeffs.IsGood.isPeriodicSmooth_a {A : HypCoeffs p n ι} (hA : A.IsGood) (i j : Fin n) :
    IsPeriodicSmooth (A.a i j) :=
  ⟨hA.smooth_a i j, hA.periodic_a i j⟩

theorem HypCoeffs.IsGood.isPeriodicSmooth_bt {A : HypCoeffs p n ι} (hA : A.IsGood) :
    IsPeriodicSmooth A.bt :=
  ⟨hA.smooth_bt, hA.periodic_bt⟩

theorem HypCoeffs.IsGood.isPeriodicSmooth_b {A : HypCoeffs p n ι} (hA : A.IsGood) (i : Fin n) :
    IsPeriodicSmooth (A.b i) :=
  ⟨hA.smooth_b i, hA.periodic_b i⟩

theorem HypCoeffs.IsGood.isPeriodicSmooth_c {A : HypCoeffs p n ι} (hA : A.IsGood) :
    IsPeriodicSmooth A.c :=
  ⟨hA.smooth_c, hA.periodic_c⟩

/-- Uniform bounds of the coefficients used by the energy estimate. -/
structure CoeffBound (A : HypCoeffs p n ι) (M : ℝ) (l : Fin p → ℝ) (t : ℝ) (y : Fin n → ℝ) :
    Prop where
  a : ∀ i j, |A.a i j l t y| ≤ M
  dt_a : ∀ i j, |dt (A.a i j) l t y| ≤ M
  dy_a : ∀ k i j, |dy k (A.a i j) l t y| ≤ M
  bt : ‖A.bt l t y‖ ≤ M
  b : ∀ i, ‖A.b i l t y‖ ≤ M
  c : ‖A.c l t y‖ ≤ M

private theorem continuous_param {X : Type*} [TopologicalSpace X]
    {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X} (hV : Continuous ↿V) :
    Continuous fun q : ((Fin p → ℝ) × ℝ) × (Fin n → ℝ) => V q.1.1 q.1.2 q.2 :=
  hV.comp (f := fun q : ((Fin p → ℝ) × ℝ) × (Fin n → ℝ) => (q.1.1, q.1.2, q.2)) (by fun_prop)

/-- The coefficients, and the derivatives of `a` used by the energy estimate, are bounded on
`K × ℝⁿ` for compact `K` (periodicity). -/
theorem HypCoeffs.IsGood.exists_coeffBound {A : HypCoeffs p n ι} (hA : A.IsGood)
    {K : Set ((Fin p → ℝ) × ℝ)} (hK : IsCompact K) :
    ∃ M, 0 ≤ M ∧ ∀ l t, (l, t) ∈ K → ∀ y, CoeffBound A M l t y := by
  set f : (Fin p → ℝ) × ℝ → (Fin n → ℝ) →
      ((Fin n → Fin n → ℝ) × (Fin n → Fin n → ℝ) × (Fin n → Fin n → Fin n → ℝ)) ×
        ((EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) ×
          (Fin n → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) ×
          (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)) :=
    fun x y => ((fun i j => A.a i j x.1 x.2 y, fun i j => dt (A.a i j) x.1 x.2 y,
      fun k i j => dy k (A.a i j) x.1 x.2 y),
      (A.bt x.1 x.2 y, fun i => A.b i x.1 x.2 y, A.c x.1 x.2 y))
  have hc : Continuous (uncurry f) := by
    refine Continuous.prodMk (Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_))
      (Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_))
    · exact continuous_pi fun i => continuous_pi fun j =>
        continuous_param (hA.smooth_a i j).continuous
    · exact continuous_pi fun i => continuous_pi fun j =>
        continuous_param (hA.isPeriodicSmooth_a i j).dt.smooth.continuous
    · exact continuous_pi fun k => continuous_pi fun i => continuous_pi fun j =>
        continuous_param ((hA.isPeriodicSmooth_a i j).dy k).smooth.continuous
    · exact continuous_param hA.smooth_bt.continuous
    · exact continuous_pi fun i => continuous_param (hA.smooth_b i).continuous
    · exact continuous_param hA.smooth_c.continuous
  have hp : ∀ x, IsPeriodic (f x) := fun x => isPeriodic_iff.2 fun k y => by
    simp only [f, (hA.periodic_a _ _ _ _).add_single k y,
      ((hA.isPeriodicSmooth_a _ _).dt.periodic _ _).add_single k y,
      (((hA.isPeriodicSmooth_a _ _).dy _).periodic _ _).add_single k y,
      (hA.periodic_bt _ _).add_single k y, (hA.periodic_b _ _ _).add_single k y,
      (hA.periodic_c _ _).add_single k y]
  obtain ⟨M, hM⟩ := exists_bound_of_isPeriodic hc hp hK
  refine ⟨max M 0, le_max_right _ _, fun l t hlt y => ?_⟩
  have h := (hM (l, t) hlt y).trans (le_max_left M 0)
  have h1 := (norm_fst_le _).trans h
  have h2 := (norm_snd_le _).trans h
  have h11 := (norm_fst_le _).trans h1
  have h12 := (norm_fst_le _).trans ((norm_snd_le _).trans h1)
  have h13 := (norm_snd_le _).trans ((norm_snd_le _).trans h1)
  have h21 := (norm_fst_le _).trans h2
  have h22 := (norm_fst_le _).trans ((norm_snd_le _).trans h2)
  have h23 := (norm_snd_le _).trans ((norm_snd_le _).trans h2)
  have pi2 : ∀ (g : Fin n → Fin n → ℝ) i j, ‖g‖ ≤ max M 0 → |g i j| ≤ max M 0 :=
    fun g i j hg => ((norm_le_pi_norm (g i) j).trans (norm_le_pi_norm g i)).trans hg
  refine ⟨fun i j => pi2 _ i j h11, fun i j => pi2 _ i j h12, fun k i j => ?_, h21,
    fun i => (norm_le_pi_norm _ i).trans h22, h23⟩
  exact pi2 _ i j ((norm_le_pi_norm _ k).trans h13)

/-! ## The pointwise inequality -/

/-- The algebra behind `∂ₜ e ≤ 2⟨∂ₜV, R⟩ + 2 ∂ᵢΦⁱ + K S + |F|²`, with `vt = ∂ₜV`,
`vtt = ∂ₜ²V`, `X i = ∂ᵢV`, `Xt i = ∂ᵢ∂ₜV`, `Y i j = ∂ᵢ∂ⱼV`, `at = ∂ₜa`, `ad k = ∂ₖa`. -/
theorem energy_pointwise {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a at' : Fin n → Fin n → ℝ) (ad : Fin n → Fin n → Fin n → ℝ) (hsym : ∀ i j, a i j = a j i)
    (vt vtt v f : E) (X Xt : Fin n → E) (Y : Fin n → Fin n → E) (bt c : E →L[ℝ] E)
    (b : Fin n → E →L[ℝ] E) {M : ℝ} (hat : ∀ i j, |at' i j| ≤ M)
    (had : ∀ k i j, |ad k i j| ≤ M) (hbt : ‖bt‖ ≤ M) (hb : ∀ i, ‖b i‖ ≤ M) (hc : ‖c‖ ≤ M) :
    2 * ⟪vt, vtt⟫ + ∑ i, ∑ j, (at' i j * ⟪X i, X j⟫ + a i j * (⟪X i, Xt j⟫ + ⟪Xt i, X j⟫)) +
        2 * ⟪v, vt⟫ ≤
      2 * ⟪vt, vtt - (∑ i, ∑ j, a i j • Y i j + bt vt + ∑ i, b i (X i) + c v) - f⟫ +
        2 * ∑ i, ∑ j, (ad i i j * ⟪vt, X j⟫ + a i j * (⟪vt, Y i j⟫ + ⟪Xt i, X j⟫)) +
        (3 + (4 + 2 * n + 3 * (n * n)) * M) * (‖vt‖ ^ 2 + ∑ i, ‖X i‖ ^ 2 + ‖v‖ ^ 2) +
        ‖f‖ ^ 2 := by
  set S := ‖vt‖ ^ 2 + ∑ i, ‖X i‖ ^ 2 + ‖v‖ ^ 2
  have hXs : ∀ i, ‖X i‖ ^ 2 ≤ ∑ i, ‖X i‖ ^ 2 := fun i =>
    Finset.single_le_sum (f := fun i => ‖X i‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have hS0 : 0 ≤ ∑ i, ‖X i‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hvt : ‖vt‖ ^ 2 ≤ S := by have := sq_nonneg ‖v‖; linarith
  have hv : ‖v‖ ^ 2 ≤ S := by have := sq_nonneg ‖vt‖; linarith
  have hX : ∀ i, ‖X i‖ ^ 2 ≤ S := fun i => by
    have := sq_nonneg ‖v‖; have := sq_nonneg ‖vt‖; linarith [hXs i]
  have hswap : ∑ i, ∑ j, a i j * ⟪X i, Xt j⟫ = ∑ i, ∑ j, a i j * ⟪Xt i, X j⟫ := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hsym, real_inner_comm]
  have hF : 2 * ⟪vt, f⟫ ≤ S + ‖f‖ ^ 2 := by
    have h1 := real_inner_le_norm vt f
    nlinarith [sq_nonneg (‖vt‖ - ‖f‖)]
  have hBt : |⟪vt, bt vt⟫| ≤ M * S := abs_inner_clm_le hbt hvt hvt
  have hC : |⟪vt, c v⟫| ≤ M * S := abs_inner_clm_le hc hvt hv
  have hB : |∑ i, ⟪vt, b i (X i)⟫| ≤ n * (M * S) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => abs_inner_clm_le (hb i) hvt (hX i)).trans ?_
    simp
  have hAd : |∑ i, ∑ j, ad i i j * ⟪vt, X j⟫| ≤ n * (n * (M * S)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun j _ => abs_mul_inner_le (had i i j) hvt (hX j))).trans ?_
    simp
  have hAt : |∑ i, ∑ j, at' i j * ⟪X i, X j⟫| ≤ n * (n * (M * S)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun j _ => abs_mul_inner_le (hat i j) (hX i) (hX j))).trans ?_
    simp
  have hV : |⟪v, vt⟫| ≤ S := abs_inner_le_of_sq_le hv hvt
  simp only [inner_sub_right, inner_add_right, inner_sum, real_inner_smul_right, mul_add,
    Finset.sum_add_distrib] at hswap ⊢
  have hK : (3 + (4 + 2 * (n : ℝ) + 3 * (n * n)) * M) * S =
      3 * S + 4 * (M * S) + 2 * (n * (M * S)) + 3 * (n * (n * (M * S))) := by ring
  rw [hK]
  have := abs_le.1 hBt; have := abs_le.1 hC; have := abs_le.1 hB; have := abs_le.1 hAd
  have := abs_le.1 hAt; have := abs_le.1 hV
  linarith

/-! ## Lower and upper bounds of the energy -/

/-- The energy density bounds `|∂ₜV|² + Σ|∂ᵢV|² + |V|²` from below and above, uniformly on a
compact set of `(l, t)`. -/
theorem HypCoeffs.IsGood.exists_density_bounds {A : HypCoeffs p n ι} (hA : A.IsGood)
    {K : Set ((Fin p → ℝ) × ℝ)} (hK : IsCompact K) :
    ∃ c > 0, ∃ M, ∀ l t, (l, t) ∈ K → ∀ V y,
      c * firstOrderDensity V l t y ≤ energyDensity A V l t y ∧
      energyDensity A V l t y ≤ M * firstOrderDensity V l t y := by
  obtain ⟨κ, hκ, hpos⟩ := hA.pos K hK
  obtain ⟨M, hM0, hM⟩ := hA.exists_coeffBound hK
  refine ⟨min 1 κ, lt_min one_pos hκ, 1 + n * (n * M), fun l t hlt V y => ⟨?_, ?_⟩⟩
  · have h := le_sum_mul_inner (fun i j => A.a i j l t y) (hpos l t hlt y)
      (fun i => dy i V l t y)
    have h1 : min 1 κ ≤ 1 := min_le_left _ _
    have h2 : min 1 κ ≤ κ := min_le_right _ _
    have hS0 : 0 ≤ ∑ i, ‖dy i V l t y‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    simp only [firstOrderDensity, energyDensity]
    nlinarith [sq_nonneg ‖dt V l t y‖, sq_nonneg ‖V l t y‖]
  · set S := firstOrderDensity V l t y
    have hXs : ∀ i, ‖dy i V l t y‖ ^ 2 ≤ ∑ i, ‖dy i V l t y‖ ^ 2 := fun i =>
      Finset.single_le_sum (f := fun i => ‖dy i V l t y‖ ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ i)
    have hX : ∀ i, ‖dy i V l t y‖ ^ 2 ≤ S := fun i => by
      have := sq_nonneg ‖V l t y‖; have := sq_nonneg ‖dt V l t y‖
      simp only [S, firstOrderDensity]; linarith [hXs i]
    have hQ : |∑ i, ∑ j, A.a i j l t y * ⟪dy i V l t y, dy j V l t y⟫| ≤ n * (n * (M * S)) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun j _ => abs_mul_inner_le ((hM l t hlt y).a i j) (hX i)
          (hX j))).trans ?_
      simp
    have hS : S = ‖dt V l t y‖ ^ 2 + ∑ i, ‖dy i V l t y‖ ^ 2 + ‖V l t y‖ ^ 2 := rfl
    have hS0 : 0 ≤ ∑ i, ‖dy i V l t y‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    simp only [energyDensity]
    have := (abs_le.1 hQ).2
    nlinarith [sq_nonneg ‖dt V l t y‖, sq_nonneg ‖V l t y‖]

theorem continuous_firstOrderDensity
    {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι} (hV : IsPeriodicSmooth V)
    (l : Fin p → ℝ) (t : ℝ) : Continuous (firstOrderDensity V l t) :=
  have h0 := continuous_slice hV.smooth.continuous l t
  have ht := continuous_slice hV.dt.smooth.continuous l t
  have hy i := continuous_slice (hV.dy i).smooth.continuous l t
  by unfold firstOrderDensity; fun_prop

theorem contDiff_energyDensity {A : HypCoeffs p n ι} (hA : A.IsGood)
    {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι} (hV : IsPeriodicSmooth V) :
    ContDiff ℝ ∞ ↿(energyDensity A V) :=
  ((hV.dt.smooth.norm_sq ℝ).add (ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
    (hA.smooth_a i j).mul ((hV.dy i).smooth.inner ℝ (hV.dy j).smooth))).add
    (hV.smooth.norm_sq ℝ)

/-- Lower bound: `c (‖∂ₜV‖² + Σ‖∂ᵢV‖² + ‖V‖²) ≤ E` in `L²(cell)`, uniformly for `(l, t)` in a
compact set. -/
theorem HypCoeffs.IsGood.energy_ge {A : HypCoeffs p n ι} (hA : A.IsGood)
    {K : Set ((Fin p → ℝ) × ℝ)} (hK : IsCompact K) :
    ∃ c > 0, ∀ l t, (l, t) ∈ K → ∀ V, IsPeriodicSmooth V →
      c * firstOrderNormSq V l t ≤ energy A V l t := by
  obtain ⟨c, hc, M, h⟩ := hA.exists_density_bounds hK
  refine ⟨c, hc, fun l t hlt V hV => ?_⟩
  rw [firstOrderNormSq, cellIntegral_def, ← integral_const_mul, energy, cellIntegral_def]
  exact integral_mono (integrableOn_cell ((continuous_firstOrderDensity hV l t).const_mul c))
    (integrableOn_cell (continuous_slice (contDiff_energyDensity hA hV).continuous l t))
    fun y => (h l t hlt V y).1

/-- Upper bound: `E ≤ M (‖∂ₜV‖² + Σ‖∂ᵢV‖² + ‖V‖²)` in `L²(cell)`, uniformly for `(l, t)` in a
compact set. -/
theorem HypCoeffs.IsGood.energy_le_mul {A : HypCoeffs p n ι} (hA : A.IsGood)
    {K : Set ((Fin p → ℝ) × ℝ)} (hK : IsCompact K) :
    ∃ M, ∀ l t, (l, t) ∈ K → ∀ V, IsPeriodicSmooth V →
      energy A V l t ≤ M * firstOrderNormSq V l t := by
  obtain ⟨c, hc, M, h⟩ := hA.exists_density_bounds hK
  refine ⟨M, fun l t hlt V hV => ?_⟩
  rw [firstOrderNormSq, cellIntegral_def, ← integral_const_mul, energy, cellIntegral_def]
  exact integral_mono
    (integrableOn_cell (continuous_slice (contDiff_energyDensity hA hV).continuous l t))
    (integrableOn_cell ((continuous_firstOrderDensity hV l t).const_mul M))
    fun y => (h l t hlt V y).2

/-! ## The energy estimate -/

/-- The flux `Φⁱ = a^{ij} ⟨∂ₜV, ∂ⱼV⟫`, whose divergence absorbs the principal part. -/
def energyFlux (A : HypCoeffs p n ι)
    (V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι) (i : Fin n) :
    (Fin p → ℝ) → ℝ → (Fin n → ℝ) → ℝ :=
  fun l t y => ∑ j, A.a i j l t y * ⟪dt V l t y, dy j V l t y⟫

theorem isPeriodicSmooth_energyFlux {A : HypCoeffs p n ι} (hA : A.IsGood)
    {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι} (hV : IsPeriodicSmooth V)
    (i : Fin n) : IsPeriodicSmooth (energyFlux A V i) where
  smooth := ContDiff.sum (s := Finset.univ) fun j _ => (hA.smooth_a i j).mul (hV.dt.smooth.inner ℝ (hV.dy j).smooth)
  periodic l t := isPeriodic_iff.2 fun k y => by
    simp only [energyFlux, (hA.periodic_a _ _ l t).add_single k y,
      (hV.dt.periodic l t).add_single k y, ((hV.dy _).periodic l t).add_single k y]

theorem dt_energyDensity {A : HypCoeffs p n ι} (hA : A.IsGood)
    {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι} (hV : IsPeriodicSmooth V)
    (l : Fin p → ℝ) (t : ℝ) (y : Fin n → ℝ) :
    dt (energyDensity A V) l t y = 2 * ⟪dt V l t y, dt (dt V) l t y⟫ +
      ∑ i, ∑ j, (dt (A.a i j) l t y * ⟪dy i V l t y, dy j V l t y⟫ +
        A.a i j l t y * (⟪dy i V l t y, dy j (dt V) l t y⟫ +
          ⟪dy i (dt V) l t y, dy j V l t y⟫)) +
      2 * ⟪V l t y, dt V l t y⟫ := by
  have hs : (Dir.time : Dir n p) ≠ Dir.self := nofun
  have hcomm : ∀ i, dt (dy i V) = dy i (dt V) := fun i => by
    simpa only [Dir.d_time, Dir.d_space] using Dir.d_comm hV.smooth Dir.time (Dir.space i)
  have h := (((Dir.hasDerivAt_line hs hV.dt.differentiable l t y).norm_sq).fun_add
    (HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
      HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
      (Dir.hasDerivAt_line hs (hA.isPeriodicSmooth_a i j).differentiable l t y).fun_mul
        ((Dir.hasDerivAt_line hs (hV.dy i).differentiable l t y).inner ℝ
          (Dir.hasDerivAt_line hs (hV.dy j).differentiable l t y)))).fun_add
    (Dir.hasDerivAt_line hs hV.differentiable l t y).norm_sq
  simp only [zero_smul, add_zero, uncurry_apply_triple] at h
  have := Dir.d_eq_of_hasDerivAt hs ((contDiff_energyDensity hA hV).differentiable (by simp)) h
  simp only [Dir.d_time, hcomm] at this
  exact this

theorem dy_energyFlux {A : HypCoeffs p n ι} (hA : A.IsGood)
    {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι} (hV : IsPeriodicSmooth V)
    (i : Fin n) (l : Fin p → ℝ) (t : ℝ) (y : Fin n → ℝ) :
    dy i (energyFlux A V i) l t y = ∑ j, (dy i (A.a i j) l t y * ⟪dt V l t y, dy j V l t y⟫ +
      A.a i j l t y * (⟪dt V l t y, dy i (dy j V) l t y⟫ + ⟪dy i (dt V) l t y, dy j V l t y⟫)) := by
  have hs : (Dir.space i : Dir n p) ≠ Dir.self := nofun
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
    (Dir.hasDerivAt_line hs (hA.isPeriodicSmooth_a i j).differentiable l t y).fun_mul
      ((Dir.hasDerivAt_line hs hV.dt.differentiable l t y).inner ℝ
        (Dir.hasDerivAt_line hs (hV.dy j).differentiable l t y))
  simp only [zero_smul, add_zero, uncurry_apply_triple] at h
  simpa only [Dir.d_space] using
    Dir.d_eq_of_hasDerivAt hs (isPeriodicSmooth_energyFlux hA hV i).differentiable h

/-- The differential inequality `E' ≤ C E + ‖F‖²` behind `energy_le`, at a time `t` where the
orthogonality `∫_cell ⟨∂ₜV, ∂ₜ²V - A V - F⟩ = 0` holds. -/
theorem HypCoeffs.IsGood.exists_dt_energy_le {A : HypCoeffs p n ι} (hA : A.IsGood)
    {K : Set ((Fin p → ℝ) × ℝ)} (hK : IsCompact K) :
    ∃ C, 0 ≤ C ∧ ∀ l t, (l, t) ∈ K → ∀ V F, IsPeriodicSmooth V → Continuous ↿F →
      cellIntegral (fun y => ⟪dt V l t y, dt (dt V) l t y - A.apply V l t y - F l t y⟫) = 0 →
      cellIntegral (dt (energyDensity A V) l t) ≤ C * energy A V l t + cellNormSq F l t := by
  obtain ⟨c, hc, hlow⟩ := hA.energy_ge hK
  obtain ⟨M, hM0, hM⟩ := hA.exists_coeffBound hK
  set K₁ : ℝ := 3 + (4 + 2 * n + 3 * (n * n)) * M
  have hK₁ : 0 ≤ K₁ := by positivity
  refine ⟨K₁ / c, by positivity, fun l t hlt V F hV hF horth => ?_⟩
  have hpt : ∀ y, dt (energyDensity A V) l t y ≤
      2 * ⟪dt V l t y, dt (dt V) l t y - A.apply V l t y - F l t y⟫ +
        2 * ∑ i, dy i (energyFlux A V i) l t y + K₁ * firstOrderDensity V l t y +
        ‖F l t y‖ ^ 2 := fun y => by
    rw [dt_energyDensity hA hV]
    simp only [dy_energyFlux hA hV, HypCoeffs.apply_def]
    have hb := hM l t hlt y
    exact energy_pointwise (fun i j => A.a i j l t y) (fun i j => dt (A.a i j) l t y)
      (fun k i j => dy k (A.a i j) l t y) (fun i j => congrFun (congrFun (congrFun
        (hA.symm i j) l) t) y) _ _ _ _ _ _ (fun i j => dy i (dy j V) l t y) _ _ _
      hb.dt_a hb.dy_a hb.bt hb.b hb.c
  have h0 := continuous_slice hV.smooth.continuous l t
  have ht := continuous_slice hV.dt.smooth.continuous l t
  have htt := continuous_slice hV.dt.dt.smooth.continuous l t
  have hAV := continuous_slice (hA.apply hV).smooth.continuous l t
  have hF' := continuous_slice hF l t
  have hΦ i := continuous_slice ((isPeriodicSmooth_energyFlux hA hV i).dy i).smooth.continuous l t
  have hfo := continuous_firstOrderDensity hV l t
  have hdiv : ∀ i, cellIntegral (dy i (energyFlux A V i) l t) = 0 := fun i => by
    rw [dy_def]
    exact cellIntegral_fderiv_eq_zero
      ((contDiff_slice (isPeriodicSmooth_energyFlux hA hV i).smooth l t).of_le (by simp))
      ((isPeriodicSmooth_energyFlux hA hV i).periodic l t) i
  have hint : cellIntegral (fun y =>
      2 * ⟪dt V l t y, dt (dt V) l t y - A.apply V l t y - F l t y⟫ +
        2 * ∑ i, dy i (energyFlux A V i) l t y + K₁ * firstOrderDensity V l t y +
        ‖F l t y‖ ^ 2) = K₁ * firstOrderNormSq V l t + cellNormSq F l t := by
    simp only [cellIntegral_def] at horth hdiv ⊢
    rw [integral_add (f := fun y => 2 * ⟪dt V l t y, dt (dt V) l t y - A.apply V l t y - F l t y⟫ +
        2 * ∑ i, dy i (energyFlux A V i) l t y + K₁ * firstOrderDensity V l t y)
        (g := fun y => ‖F l t y‖ ^ 2) (integrableOn_cell (by fun_prop))
        (integrableOn_cell (by fun_prop)),
      integral_add (f := fun y => 2 * ⟪dt V l t y, dt (dt V) l t y - A.apply V l t y - F l t y⟫ +
        2 * ∑ i, dy i (energyFlux A V i) l t y)
        (g := fun y => K₁ * firstOrderDensity V l t y) (integrableOn_cell (by fun_prop))
        (integrableOn_cell (by fun_prop)),
      integral_add (f := fun y => 2 * ⟪dt V l t y, dt (dt V) l t y - A.apply V l t y - F l t y⟫)
        (g := fun y => 2 * ∑ i, dy i (energyFlux A V i) l t y) (integrableOn_cell (by fun_prop))
        (integrableOn_cell (by fun_prop)),
      integral_const_mul, integral_const_mul, integral_const_mul,
      integral_finsetSum _ fun i _ => integrableOn_cell (hΦ i), horth]
    simp only [hdiv, Finset.sum_const_zero, mul_zero, zero_add, firstOrderNormSq, cellNormSq,
      cellIntegral_def]
  have hle : cellIntegral (dt (energyDensity A V) l t) ≤
      K₁ * firstOrderNormSq V l t + cellNormSq F l t := by
    rw [← hint, cellIntegral_def, cellIntegral_def]
    exact integral_mono
      (integrableOn_cell (by
        simpa only [Dir.d_time] using continuous_slice
          (Dir.contDiff_d (contDiff_energyDensity hA hV) Dir.time).continuous l t))
      (integrableOn_cell (by fun_prop)) hpt
  have hE := hlow l t hlt V hV
  calc cellIntegral (dt (energyDensity A V) l t)
      ≤ K₁ * firstOrderNormSq V l t + cellNormSq F l t := hle
    _ = K₁ / c * (c * firstOrderNormSq V l t) + cellNormSq F l t := by field_simp
    _ ≤ K₁ / c * energy A V l t + cellNormSq F l t := by gcongr

theorem hasDerivAt_energy {A : HypCoeffs p n ι} (hA : A.IsGood)
    {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι} (hV : IsPeriodicSmooth V)
    (l : Fin p → ℝ) (t : ℝ) :
    HasDerivAt (energy A V l) (cellIntegral (dt (energyDensity A V) l t)) t := by
  rw [show dt (energyDensity A V) l t = fun y => deriv (fun t => energyDensity A V l t y) t from
    funext fun y => dt_apply _ _ _ _]
  exact hasDerivAt_cellIntegral (f := fun t y => energyDensity A V l t y)
    (((contDiff_energyDensity hA hV).comp
      (f := fun q : ℝ × (Fin n → ℝ) => (l, q.1, q.2)) (by fun_prop)).of_le (by simp)) t

/-- **The energy estimate.** For `(l, t) ∈ K × [t₀, t₁]`, a smooth periodic `V` and a source `F`
such that `∫_cell ⟨∂ₜV, ∂ₜ²V - A V - F⟩ = 0` (true for exact and Galerkin solutions),
`E(t) ≤ e^{C (t - t₀)} (E(t₀) + ∫_{t₀}^t ‖F(s)‖²_{L²(cell)} ds)`, with `C` depending only on
`A`, `K`, `t₀`, `t₁`. -/
theorem HypCoeffs.IsGood.energy_le {A : HypCoeffs p n ι} (hA : A.IsGood) {K : Set (Fin p → ℝ)}
    (hK : IsCompact K) (t₀ t₁ : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ l ∈ K, ∀ V F, IsPeriodicSmooth V → Continuous ↿F →
      (∀ t ∈ Icc t₀ t₁, cellIntegral
        (fun y => ⟪dt V l t y, dt (dt V) l t y - A.apply V l t y - F l t y⟫) = 0) →
      ∀ t ∈ Icc t₀ t₁, energy A V l t ≤
        exp (C * (t - t₀)) * (energy A V l t₀ + ∫ s in t₀..t, cellNormSq F l s) := by
  obtain ⟨C, hC, h⟩ := hA.exists_dt_energy_le (hK.prod isCompact_Icc)
  exact ⟨C, hC, fun l hl V F hV hF horth => le_exp_mul_of_hasDerivAt_le hC
    (fun t _ => hasDerivAt_energy hA hV l t) (continuous_cellNormSq hF l)
    (fun t _ => cellNormSq_nonneg F l t)
    (fun t ht => h l t ⟨hl, Ioo_subset_Icc_self ht⟩ V F hV hF (horth t (Ioo_subset_Icc_self ht)))⟩

end

end LorentzianCalderon.PDE
