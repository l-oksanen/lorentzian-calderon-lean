module

public import LorentzianCalderon.PDE.Periodic

public section

/-!
# Fourier projection on the unit cell

`fourierProj N u y = ∑_{|kᵢ| ≤ N} (cos (2π k·y) ĉₖ(u) + sin (2π k·y) ŝₖ(u))` with the cell
integrals `ĉₖ(u) = ∫_cell cos (2π k·z) u z dz` (`cosCoeff`) and `ŝₖ(u)` (`sinCoeff`); this is the
real form of `∑_{|kᵢ| ≤ N} û k e^{2πik·y}`.

Main results:
* `fourierProj_mem_trigPoly`, `fourierProj_eq_self` (`P_N` is the identity on `trigPoly ι n N`),
  `cellIntegral_inner_fourierProj_comm` (symmetry), `cellIntegral_inner_sub_fourierProj`
  (`u - P_N u ⟂ trigPoly ι n N`);
* `contDiff_fourierProj`, `isPeriodic_fourierProj`, `isPeriodicSmooth_fourierProj` (smooth in
  all variables for smooth families);
* commutation with derivatives: `fderiv_fourierProj` (in `y`), `fderiv_fourierProj_param` (in a
  parameter), and for families `dt_fourierProj`, `dy_fourierProj`, `dpar_fourierProj`;
* Parseval (`hasSum_norm_sq_coeff`, from `UnitAddTorus.hasSum_sq_mFourierCoeff`) and the tail
  bounds `sq_mul_cellIntegral_sub_fourierProj_le`:
  `(2πN)² ∫_cell ‖u - P_N u‖² ≤ ∑ᵢ ∫_cell ‖∂ᵢu‖²`, and `mul_cellNorm_sub_fourierProj_le`.
-/

namespace LorentzianCalderon.PDE

noncomputable section
open scoped ContDiff RealInnerProductSpace Topology
open Set MeasureTheory Function Real

variable {n : ℕ}

/-! The normalized Haar measure on `ℝ / ℤ`, as in `Mathlib.Analysis.Fourier.AddCircleMulti`
(where it is a local instance too), so that `volume` on `UnitAddTorus` means the same here. -/

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ## Phases -/

/-- The phase `y ↦ 2π k·y` as a continuous linear map. -/
def phaseCLM (k : Fin n → ℤ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ i, (2 * π * k i) • ContinuousLinearMap.proj i

/-- The phase is the linear map `phaseCLM`. -/
theorem phaseCLM_apply (k : Fin n → ℤ) (y : Fin n → ℝ) : phaseCLM k y = phase k y := by
  simp [phaseCLM, phase_def, Finset.mul_sum, mul_assoc]

/-- The phase is the linear map `phaseCLM`, as functions. -/
theorem phase_eq_phaseCLM (k : Fin n → ℤ) : phase k = ⇑(phaseCLM k) :=
  funext fun y => (phaseCLM_apply k y).symm

/-- `∂ᵢ` of the phase: `2π kᵢ`. -/
theorem phaseCLM_single (k : Fin n → ℤ) (i : Fin n) :
    phaseCLM k (Pi.single i 1) = 2 * π * k i := by
  simp [phaseCLM, Pi.single_apply]

/-- The derivative of the (linear) phase is `phaseCLM`. -/
theorem hasFDerivAt_phase (k : Fin n → ℤ) (y : Fin n → ℝ) :
    HasFDerivAt (phase k) (phaseCLM k) y := by
  rw [phase_eq_phaseCLM]; exact (phaseCLM k).hasFDerivAt

/-- The phase is smooth. -/
@[fun_prop]
theorem contDiff_phase (k : Fin n → ℤ) {m : WithTop ℕ∞} : ContDiff ℝ m (phase k) := by
  rw [phase_eq_phaseCLM]; exact (phaseCLM k).contDiff

/-- The phase is continuous. -/
@[fun_prop]
theorem continuous_phase (k : Fin n → ℤ) : Continuous (phase k) :=
  (contDiff_phase k (m := 0)).continuous

/-- The phase is additive in the frequency. -/
theorem phase_add (k m : Fin n → ℤ) (y : Fin n → ℝ) :
    phase (k + m) y = phase k y + phase m y := by
  simp only [phase_def, Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]; ring

/-- The phase is odd in the frequency. -/
theorem phase_neg (k : Fin n → ℤ) (y : Fin n → ℝ) : phase (-k) y = -phase k y := by
  simp only [phase_def, Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib]; ring

/-- The phase is additive in the frequency (difference form). -/
theorem phase_sub (k m : Fin n → ℤ) (y : Fin n → ℝ) :
    phase (k - m) y = phase k y - phase m y := by
  rw [sub_eq_add_neg, phase_add, phase_neg]; ring

@[simp] theorem phase_zero (y : Fin n → ℝ) : phase 0 y = 0 := by simp [phase_def]

/-- The unit cell has volume `1`. -/
theorem volume_cell : volume (cell n) = 1 := by
  simp [cell_def, Real.volume_Icc_pi]

/-- The cell integral of a constant is the constant (the cell has volume `1`). -/
theorem cellIntegral_const {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (c : G) :
    cellIntegral (fun _ : Fin n → ℝ => c) = c := by
  rw [cellIntegral_def, setIntegral_const, Measure.real, volume_cell]; simp

/-- The `L²(cell)` norm `(∫_cell ‖u‖²)^{1/2}`. -/
def cellNorm {G : Type*} [NormedAddCommGroup G] (u : (Fin n → ℝ) → G) : ℝ :=
  √(cellIntegral fun y => ‖u y‖ ^ 2)

theorem cellNorm_def {G : Type*} [NormedAddCommGroup G] (u : (Fin n → ℝ) → G) :
    cellNorm u =
      √(cellIntegral fun y => ‖u y‖ ^ 2) := by rfl

/-- The `L²(cell)` norm is nonnegative. -/
theorem cellNorm_nonneg {G : Type*} [NormedAddCommGroup G] (u : (Fin n → ℝ) → G) :
    0 ≤ cellNorm u := Real.sqrt_nonneg _

/-- `∫_cell cos (2π j·y) dy` is `1` for `j = 0` and `0` otherwise. -/
theorem cellIntegral_cos_phase (j : Fin n → ℤ) :
    cellIntegral (fun y => Real.cos (phase j y)) = if j = 0 then 1 else 0 := by
  split_ifs with hj
  · simp [hj, cellIntegral_const]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hj
  have h := cellIntegral_fderiv_eq_zero (u := fun y => Real.sin (phase j y))
    (by fun_prop) (isPeriodic_iff.2 fun i y => by
      simp [phase_add_single, Real.sin_add_int_mul_two_pi]) i
  simp only [fun y => ((hasFDerivAt_phase j y).sin).fderiv, smul_apply,
    phaseCLM_single, smul_eq_mul, cellIntegral_def] at h
  rw [integral_mul_const] at h
  have : (2 * π * (j i : ℝ)) ≠ 0 := by
    have : (j i : ℝ) ≠ 0 := by exact_mod_cast hi
    positivity
  rw [cellIntegral_def]
  exact (mul_eq_zero.mp h).resolve_right this

/-- `∫_cell sin (2π j·y) dy = 0`. -/
theorem cellIntegral_sin_phase (j : Fin n → ℤ) :
    cellIntegral (fun y => Real.sin (phase j y)) = 0 := by
  by_cases hj : j = 0
  · simp [hj, cellIntegral_const]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hj
  have h := cellIntegral_fderiv_eq_zero (u := fun y => Real.cos (phase j y))
    (by fun_prop) (isPeriodic_iff.2 fun i y => by
      simp [phase_add_single, Real.cos_add_int_mul_two_pi]) i
  simp only [fun y => ((hasFDerivAt_phase j y).cos).fderiv, smul_apply,
    phaseCLM_single, smul_eq_mul, cellIntegral_def, neg_mul] at h
  rw [integral_neg, integral_mul_const, neg_eq_zero] at h
  have : (2 * π * (j i : ℝ)) ≠ 0 := by
    have : (j i : ℝ) ≠ 0 := by exact_mod_cast hi
    positivity
  rw [cellIntegral_def]
  exact (mul_eq_zero.mp h).resolve_right this

/-- Orthogonality: `∫_cell cos (2π k·y) cos (2π m·y) dy = ([k = m] + [k = -m]) / 2`. -/
theorem cellIntegral_cos_mul_cos (k m : Fin n → ℤ) :
    cellIntegral (fun y => Real.cos (phase k y) * Real.cos (phase m y)) =
      ((if k = m then 1 else 0) + (if k = -m then 1 else 0)) / 2 := by
  have h : (fun y => Real.cos (phase k y) * Real.cos (phase m y)) =
      fun y => (Real.cos (phase (k - m) y) + Real.cos (phase (k + m) y)) / 2 := by
    funext y; rw [phase_sub, phase_add, Real.cos_sub, Real.cos_add]; ring
  have h1 := cellIntegral_cos_phase (k - m)
  have h2 := cellIntegral_cos_phase (k + m)
  simp only [cellIntegral_def] at h1 h2 ⊢
  rw [h, integral_div, integral_add (integrableOn_cell (by fun_prop))
    (integrableOn_cell (by fun_prop)), h1, h2]
  simp only [sub_eq_zero, add_eq_zero_iff_eq_neg]

/-- Orthogonality: `∫_cell sin (2π k·y) sin (2π m·y) dy = ([k = m] - [k = -m]) / 2`. -/
theorem cellIntegral_sin_mul_sin (k m : Fin n → ℤ) :
    cellIntegral (fun y => Real.sin (phase k y) * Real.sin (phase m y)) =
      ((if k = m then 1 else 0) - (if k = -m then 1 else 0)) / 2 := by
  have h : (fun y => Real.sin (phase k y) * Real.sin (phase m y)) =
      fun y => (Real.cos (phase (k - m) y) - Real.cos (phase (k + m) y)) / 2 := by
    funext y; rw [phase_sub, phase_add, Real.cos_sub, Real.cos_add]; ring
  have h1 := cellIntegral_cos_phase (k - m)
  have h2 := cellIntegral_cos_phase (k + m)
  simp only [cellIntegral_def] at h1 h2 ⊢
  rw [h, integral_div, integral_sub (integrableOn_cell (by fun_prop))
    (integrableOn_cell (by fun_prop)), h1, h2]
  simp only [sub_eq_zero, add_eq_zero_iff_eq_neg]

/-- Orthogonality: `∫_cell cos (2π k·y) sin (2π m·y) dy = 0`. -/
theorem cellIntegral_cos_mul_sin (k m : Fin n → ℤ) :
    cellIntegral (fun y => Real.cos (phase k y) * Real.sin (phase m y)) = 0 := by
  have h : (fun y => Real.cos (phase k y) * Real.sin (phase m y)) =
      fun y => (Real.sin (phase (m + k) y) + Real.sin (phase (m - k) y)) / 2 := by
    funext y; rw [phase_sub, phase_add, Real.sin_sub, Real.sin_add]; ring
  have h1 := cellIntegral_sin_phase (m + k)
  have h2 := cellIntegral_sin_phase (m - k)
  simp only [cellIntegral_def] at h1 h2 ⊢
  rw [h, integral_div, integral_add (integrableOn_cell (by fun_prop))
    (integrableOn_cell (by fun_prop)), h1, h2]
  simp

/-- Orthogonality: `∫_cell sin (2π k·y) cos (2π m·y) dy = 0`. -/
theorem cellIntegral_sin_mul_cos (k m : Fin n → ℤ) :
    cellIntegral (fun y => Real.sin (phase k y) * Real.cos (phase m y)) = 0 := by
  simpa only [mul_comm] using cellIntegral_cos_mul_sin m k

/-! ## Fourier coefficients and the projection -/

/-- The frequencies `k ∈ ℤⁿ` with `|kᵢ| ≤ N` for all `i`. -/
def freqBox (n N : ℕ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(N : ℤ)) N

/-- Membership in the frequency box. -/
theorem mem_freqBox {N : ℕ} {k : Fin n → ℤ} : k ∈ freqBox n N ↔ ∀ i, |k i| ≤ N := by
  simp [freqBox, abs_le]

/-- The frequency box is symmetric. -/
theorem neg_mem_freqBox {N : ℕ} {k : Fin n → ℤ} (hk : k ∈ freqBox n N) : -k ∈ freqBox n N :=
  mem_freqBox.2 fun i => by simpa using mem_freqBox.1 hk i

section Coeff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The cosine coefficient `∫_cell cos (2π k·y) u y dy`. -/
def cosCoeff (k : Fin n → ℤ) (u : (Fin n → ℝ) → E) : E :=
  cellIntegral fun y => Real.cos (phase k y) • u y

/-- The sine coefficient `∫_cell sin (2π k·y) u y dy`. -/
def sinCoeff (k : Fin n → ℤ) (u : (Fin n → ℝ) → E) : E :=
  cellIntegral fun y => Real.sin (phase k y) • u y

/-- The Fourier projection of `u` onto the trigonometric polynomials of degree `≤ N`:
`P_N u y = ∑_{|kᵢ| ≤ N} (cos (2π k·y) ĉₖ + sin (2π k·y) ŝₖ)`, i.e. `∫_cell D_N (y - z) u z dz` with
the Dirichlet kernel `D_N y = ∑_{|kᵢ| ≤ N} cos (2π k·y)`. Each `k ≠ 0` appears together with `-k`,
which contributes the same term; this is the real form of `∑_{|kᵢ| ≤ N} û k e^{2πik·y}`. -/
def fourierProj (N : ℕ) (u : (Fin n → ℝ) → E) (y : Fin n → ℝ) : E :=
  ∑ k ∈ freqBox n N, (Real.cos (phase k y) • cosCoeff k u + Real.sin (phase k y) • sinCoeff k u)

/-- The cosine coefficient is additive on continuous functions. -/
theorem cosCoeff_add {u v : (Fin n → ℝ) → E} (hu : Continuous u) (hv : Continuous v)
    (k : Fin n → ℤ) : cosCoeff k (fun y => u y + v y) = cosCoeff k u + cosCoeff k v := by
  simp only [cosCoeff, cellIntegral_def, smul_add]
  exact integral_add (integrableOn_cell (by fun_prop)) (integrableOn_cell (by fun_prop))

/-- The sine coefficient is additive on continuous functions. -/
theorem sinCoeff_add {u v : (Fin n → ℝ) → E} (hu : Continuous u) (hv : Continuous v)
    (k : Fin n → ℤ) : sinCoeff k (fun y => u y + v y) = sinCoeff k u + sinCoeff k v := by
  simp only [sinCoeff, cellIntegral_def, smul_add]
  exact integral_add (integrableOn_cell (by fun_prop)) (integrableOn_cell (by fun_prop))

/-- The cosine coefficient is homogeneous. -/
theorem cosCoeff_smul (c : ℝ) (u : (Fin n → ℝ) → E) (k : Fin n → ℤ) :
    cosCoeff k (fun y => c • u y) = c • cosCoeff k u := by
  simp only [cosCoeff, cellIntegral_def, smul_comm _ c]
  exact integral_smul c _

/-- The sine coefficient is homogeneous. -/
theorem sinCoeff_smul (c : ℝ) (u : (Fin n → ℝ) → E) (k : Fin n → ℤ) :
    sinCoeff k (fun y => c • u y) = c • sinCoeff k u := by
  simp only [sinCoeff, cellIntegral_def, smul_comm _ c]
  exact integral_smul c _

/-- `P_N` is additive on continuous functions. -/
theorem fourierProj_add {u v : (Fin n → ℝ) → E} (hu : Continuous u) (hv : Continuous v)
    (N : ℕ) : fourierProj N (fun y => u y + v y) = fourierProj N u + fourierProj N v := by
  funext y
  simp only [fourierProj, cosCoeff_add hu hv, sinCoeff_add hu hv, Pi.add_apply,
    ← Finset.sum_add_distrib, smul_add]
  refine Finset.sum_congr rfl fun k _ => by abel

/-- `P_N` is homogeneous. -/
theorem fourierProj_smul (c : ℝ) (u : (Fin n → ℝ) → E) (N : ℕ) :
    fourierProj N (fun y => c • u y) = c • fourierProj N u := by
  funext y
  simp only [fourierProj, cosCoeff_smul, sinCoeff_smul, Pi.smul_apply, Finset.smul_sum,
    smul_add, smul_comm c]

variable [CompleteSpace E]

/-- The cosine coefficient commutes with continuous linear maps. -/
theorem map_cosCoeff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F]
    (L : E →L[ℝ] F) {u : (Fin n → ℝ) → E} (hu : Continuous u) (k : Fin n → ℤ) :
    L (cosCoeff k u) = cosCoeff k (fun y => L (u y)) := by
  simp only [cosCoeff, cellIntegral_def, ← L.map_smul]
  exact (L.integral_comp_comm (integrableOn_cell (by fun_prop))).symm

/-- The sine coefficient commutes with continuous linear maps. -/
theorem map_sinCoeff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F]
    (L : E →L[ℝ] F) {u : (Fin n → ℝ) → E} (hu : Continuous u) (k : Fin n → ℤ) :
    L (sinCoeff k u) = sinCoeff k (fun y => L (u y)) := by
  simp only [sinCoeff, cellIntegral_def, ← L.map_smul]
  exact (L.integral_comp_comm (integrableOn_cell (by fun_prop))).symm

/-- `P_N` commutes with continuous linear maps (applied pointwise). -/
theorem map_fourierProj {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F]
    (L : E →L[ℝ] F) {u : (Fin n → ℝ) → E} (hu : Continuous u) (N : ℕ) (y : Fin n → ℝ) :
    L (fourierProj N u y) = fourierProj N (fun z => L (u z)) y := by
  simp [fourierProj, map_cosCoeff L hu, map_sinCoeff L hu]

/-- Cosine coefficients of a cosine mode. -/
theorem cosCoeff_cos (k m : Fin n → ℤ) (v : E) :
    cosCoeff k (fun y => Real.cos (phase m y) • v) =
      (((if k = m then 1 else 0) + (if k = -m then 1 else 0)) / 2 : ℝ) • v := by
  simp only [cosCoeff, cellIntegral_def, smul_smul]
  rw [integral_smul_const, ← cellIntegral_def, cellIntegral_cos_mul_cos]

/-- Sine coefficients of a cosine mode vanish. -/
theorem sinCoeff_cos (k m : Fin n → ℤ) (v : E) :
    sinCoeff k (fun y => Real.cos (phase m y) • v) = 0 := by
  simp only [sinCoeff, cellIntegral_def, smul_smul]
  rw [integral_smul_const, ← cellIntegral_def, cellIntegral_sin_mul_cos, zero_smul]

/-- Cosine coefficients of a sine mode vanish. -/
theorem cosCoeff_sin (k m : Fin n → ℤ) (v : E) :
    cosCoeff k (fun y => Real.sin (phase m y) • v) = 0 := by
  simp only [cosCoeff, cellIntegral_def, smul_smul]
  rw [integral_smul_const, ← cellIntegral_def, cellIntegral_cos_mul_sin, zero_smul]

/-- Sine coefficients of a sine mode. -/
theorem sinCoeff_sin (k m : Fin n → ℤ) (v : E) :
    sinCoeff k (fun y => Real.sin (phase m y) • v) =
      (((if k = m then 1 else 0) - (if k = -m then 1 else 0)) / 2 : ℝ) • v := by
  simp only [sinCoeff, cellIntegral_def, smul_smul]
  rw [integral_smul_const, ← cellIntegral_def, cellIntegral_sin_mul_sin]

/-- `P_N` fixes the cosine modes of degree `≤ N`. -/
theorem fourierProj_cos {N : ℕ} {m : Fin n → ℤ} (hm : m ∈ freqBox n N) (v : E) :
    fourierProj N (fun y => Real.cos (phase m y) • v) = fun y => Real.cos (phase m y) • v := by
  funext y
  simp only [fourierProj, cosCoeff_cos, sinCoeff_cos, smul_zero, add_zero, smul_smul,
    ← Finset.sum_smul]
  congr 1
  simp only [mul_div_assoc', mul_add, add_div, Finset.sum_add_distrib, mul_ite, mul_one,
    mul_zero, ite_div, zero_div]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [hm, neg_mem_freqBox hm, ↓reduceIte, phase_neg, Real.cos_neg]
  ring

/-- `P_N` fixes the sine modes of degree `≤ N`. -/
theorem fourierProj_sin {N : ℕ} {m : Fin n → ℤ} (hm : m ∈ freqBox n N) (v : E) :
    fourierProj N (fun y => Real.sin (phase m y) • v) = fun y => Real.sin (phase m y) • v := by
  funext y
  simp only [fourierProj, sinCoeff_sin, cosCoeff_sin, smul_zero, zero_add, smul_smul,
    ← Finset.sum_smul]
  congr 1
  simp only [mul_div_assoc', mul_sub, sub_div, Finset.sum_sub_distrib, mul_ite, mul_one,
    mul_zero, ite_div, zero_div]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [hm, neg_mem_freqBox hm, ↓reduceIte, phase_neg, Real.sin_neg]
  ring

omit [CompleteSpace E] in
/-- The coefficients of `0` vanish. -/
theorem cosCoeff_zero (k : Fin n → ℤ) : cosCoeff k (fun _ => (0 : E)) = 0 := by
  simp [cosCoeff, cellIntegral_def]

omit [CompleteSpace E] in
/-- The coefficients of `0` vanish. -/
theorem sinCoeff_zero (k : Fin n → ℤ) : sinCoeff k (fun _ => (0 : E)) = 0 := by
  simp [sinCoeff, cellIntegral_def]

omit [CompleteSpace E] in
/-- `P_N u` is smooth for every `u`. -/
@[fun_prop]
theorem contDiff_fourierProj (N : ℕ) (u : (Fin n → ℝ) → E) {m : WithTop ℕ∞} :
    ContDiff ℝ m (fourierProj N u) := by
  unfold fourierProj
  exact ContDiff.sum fun k _ =>
    ((contDiff_phase k).cos.smul contDiff_const).add ((contDiff_phase k).sin.smul contDiff_const)

omit [CompleteSpace E] in
/-- `P_N u` is continuous for every `u`. -/
@[fun_prop]
theorem continuous_fourierProj (N : ℕ) (u : (Fin n → ℝ) → E) : Continuous (fourierProj N u) :=
  (contDiff_fourierProj N u (m := 0)).continuous

omit [CompleteSpace E] in
/-- `P_N u` is periodic for every `u`. -/
theorem isPeriodic_fourierProj (N : ℕ) (u : (Fin n → ℝ) → E) : IsPeriodic (fourierProj N u) :=
  isPeriodic_iff.2 fun i y => by
    simp only [fourierProj, phase_add_single, Real.cos_add_int_mul_two_pi,
      Real.sin_add_int_mul_two_pi]

/-- `∂ᵢ` of the cosine coefficients: `ĉₖ(∂ᵢu) = 2πkᵢ ŝₖ(u)` (integration by parts). -/
theorem cosCoeff_fderiv {u : (Fin n → ℝ) → E} (hu : ContDiff ℝ 1 u) (hp : IsPeriodic u)
    (k : Fin n → ℤ) (i : Fin n) :
    cosCoeff k (fun y => fderiv ℝ u y (Pi.single i 1)) = (2 * π * k i) • sinCoeff k u := by
  have hdu : Continuous fun y => fderiv ℝ u y (Pi.single i 1) :=
    (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have huc := hu.continuous
  have hd : ∀ y, HasFDerivAt (fun y => Real.cos (phase k y) • u y)
      (Real.cos (phase k y) • fderiv ℝ u y +
        (-Real.sin (phase k y) • phaseCLM k).smulRight (u y)) y := fun y =>
    ((hasFDerivAt_phase k y).cos).smul (hu.differentiable one_ne_zero y).hasFDerivAt
  have e : (fun y => fderiv ℝ (fun y => Real.cos (phase k y) • u y) y (Pi.single i 1)) =
      fun y => Real.cos (phase k y) • fderiv ℝ u y (Pi.single i 1) -
        (2 * π * k i) • (Real.sin (phase k y) • u y) := funext fun y => by
    rw [(hd y).fderiv]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, phaseCLM_single, smul_eq_mul, smul_smul]
    module
  have h := cellIntegral_fderiv_eq_zero (u := fun y => Real.cos (phase k y) • u y)
    ((contDiff_phase k).cos.smul hu)
    (isPeriodic_iff.2 fun j y => by
      simp only [phase_add_single, Real.cos_add_int_mul_two_pi, hp.add_single j y]) i
  rw [e, cellIntegral_def, integral_sub (integrableOn_cell (by fun_prop))
    (integrableOn_cell (by fun_prop)), integral_smul, sub_eq_zero] at h
  simp only [cosCoeff, sinCoeff, cellIntegral_def]
  exact h

/-- `∂ᵢ` of the sine coefficients: `ŝₖ(∂ᵢu) = -2πkᵢ ĉₖ(u)`. -/
theorem sinCoeff_fderiv {u : (Fin n → ℝ) → E} (hu : ContDiff ℝ 1 u) (hp : IsPeriodic u)
    (k : Fin n → ℤ) (i : Fin n) :
    sinCoeff k (fun y => fderiv ℝ u y (Pi.single i 1)) = -(2 * π * k i) • cosCoeff k u := by
  have hdu : Continuous fun y => fderiv ℝ u y (Pi.single i 1) :=
    (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have huc := hu.continuous
  have hd : ∀ y, HasFDerivAt (fun y => Real.sin (phase k y) • u y)
      (Real.sin (phase k y) • fderiv ℝ u y +
        (Real.cos (phase k y) • phaseCLM k).smulRight (u y)) y := fun y =>
    ((hasFDerivAt_phase k y).sin).smul (hu.differentiable one_ne_zero y).hasFDerivAt
  have e : (fun y => fderiv ℝ (fun y => Real.sin (phase k y) • u y) y (Pi.single i 1)) =
      fun y => Real.sin (phase k y) • fderiv ℝ u y (Pi.single i 1) +
        (2 * π * k i) • (Real.cos (phase k y) • u y) := funext fun y => by
    rw [(hd y).fderiv]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, phaseCLM_single, smul_eq_mul, smul_smul]
    module
  have h := cellIntegral_fderiv_eq_zero (u := fun y => Real.sin (phase k y) • u y)
    ((contDiff_phase k).sin.smul hu)
    (isPeriodic_iff.2 fun j y => by
      simp only [phase_add_single, Real.sin_add_int_mul_two_pi, hp.add_single j y]) i
  rw [e, cellIntegral_def, integral_add (integrableOn_cell (by fun_prop))
    (integrableOn_cell (by fun_prop)), integral_smul, add_eq_zero_iff_eq_neg] at h
  rw [neg_smul]
  simp only [cosCoeff, sinCoeff, cellIntegral_def]
  exact h

/-- `P_N` commutes with `∂ᵢ` on periodic `C¹` functions. -/
theorem fderiv_fourierProj {u : (Fin n → ℝ) → E} (hu : ContDiff ℝ 1 u) (hp : IsPeriodic u)
    (N : ℕ) (i : Fin n) (y : Fin n → ℝ) :
    fderiv ℝ (fourierProj N u) y (Pi.single i 1) =
      fourierProj N (fun z => fderiv ℝ u z (Pi.single i 1)) y := by
  have hd : HasFDerivAt (fourierProj N u) (∑ k ∈ freqBox n N,
      ((-Real.sin (phase k y) • phaseCLM k).smulRight (cosCoeff k u) +
        (Real.cos (phase k y) • phaseCLM k).smulRight (sinCoeff k u))) y := by
    unfold fourierProj
    exact HasFDerivAt.fun_sum fun k _ =>
      ((hasFDerivAt_phase k y).cos.smul_const _).add ((hasFDerivAt_phase k y).sin.smul_const _)
  rw [hd.fderiv]
  simp only [fourierProj, cosCoeff_fderiv hu hp, sinCoeff_fderiv hu hp,
    sum_apply, add_apply,
    ContinuousLinearMap.smulRight_apply, smul_apply, phaseCLM_single,
    smul_eq_mul, smul_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  module

/-- `∂ᵢ P_N u = P_N ∂ᵢ u` as functions. -/
theorem fderiv_fourierProj' {u : (Fin n → ℝ) → E} (hu : ContDiff ℝ 1 u) (hp : IsPeriodic u)
    (N : ℕ) (i : Fin n) :
    (fun y => fderiv ℝ (fourierProj N u) y (Pi.single i 1)) =
      fourierProj N (fun z => fderiv ℝ u z (Pi.single i 1)) :=
  funext (fderiv_fourierProj hu hp N i)

/-! ### Dependence on parameters -/

/-- The partial derivative in the first variable of a jointly `C¹` function is continuous in
the second. -/
theorem continuous_fderiv_param {X Y G : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : X → Y → G} (hf : ContDiff ℝ 1 (uncurry f)) (x₀ : X) :
    Continuous fun y => fderiv ℝ (fun x => f x y) x₀ :=
  (ContDiff.fderiv (n := 0) (f := fun (y : Y) (x : X) => f x y)
    (hf.comp (f := fun q : Y × X => (q.2, q.1)) (by fun_prop)) contDiff_const
    (by simp)).continuous

omit [CompleteSpace E] in
/-- Differentiation of `P_N` in a finite-dimensional parameter: `P_N` commutes with `∂_x`. -/
theorem fderiv_fourierProj_param {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] {f : X → (Fin n → ℝ) → E} (hf : ContDiff ℝ 1 (uncurry f))
    (N : ℕ) (x₀ v : X) (y : Fin n → ℝ) :
    fderiv ℝ (fun x => fourierProj N (f x) y) x₀ v =
      fourierProj N (fun z => fderiv ℝ (fun x => f x z) x₀ v) y := by
  have hdiff : ∀ z, DifferentiableAt ℝ (fun x => f x z) x₀ := fun z =>
    (hf.comp (contDiff_id.prodMk contDiff_const)).differentiable one_ne_zero x₀
  have hcont := continuous_fderiv_param hf x₀
  have hcos : ∀ k, HasFDerivAt (fun x => cosCoeff k (f x))
      (cellIntegral fun z => Real.cos (phase k z) • fderiv ℝ (fun x => f x z) x₀) x₀ := by
    intro k
    have := hasFDerivAt_cellIntegral (f := fun x z => Real.cos (phase k z) • f x z)
      (((contDiff_phase k).comp contDiff_snd).cos.smul hf) x₀
    refine this.congr_fderiv (congrArg cellIntegral (funext fun z => ?_))
    exact fderiv_fun_const_smul (hdiff z) _
  have hsin : ∀ k, HasFDerivAt (fun x => sinCoeff k (f x))
      (cellIntegral fun z => Real.sin (phase k z) • fderiv ℝ (fun x => f x z) x₀) x₀ := by
    intro k
    have := hasFDerivAt_cellIntegral (f := fun x z => Real.sin (phase k z) • f x z)
      (((contDiff_phase k).comp contDiff_snd).sin.smul hf) x₀
    refine this.congr_fderiv (congrArg cellIntegral (funext fun z => ?_))
    exact fderiv_fun_const_smul (hdiff z) _
  have hP := HasFDerivAt.fun_sum (u := freqBox n N) (x := x₀)
    (A := fun k x => Real.cos (phase k y) • cosCoeff k (f x) +
      Real.sin (phase k y) • sinCoeff k (f x)) fun k _ =>
    ((hcos k).fun_const_smul (Real.cos (phase k y))).add
      ((hsin k).fun_const_smul (Real.sin (phase k y)))
  rw [show (fun x => fourierProj N (f x) y) = fun x => ∑ k ∈ freqBox n N,
    (Real.cos (phase k y) • cosCoeff k (f x) + Real.sin (phase k y) • sinCoeff k (f x)) from rfl,
    hP.fderiv]
  simp only [fourierProj, sum_apply, add_apply,
    smul_apply, cosCoeff, sinCoeff, cellIntegral_def]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ContinuousLinearMap.integral_apply (integrableOn_cell (by fun_prop)).integrable,
    ContinuousLinearMap.integral_apply (integrableOn_cell (by fun_prop)).integrable]
  simp only [smul_apply]

end Coeff

/-! ## Families -/

section Families

variable {p : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → E}

omit [CompleteSpace E] in
/-- `P_N` commutes with `∂ₜ`. -/
theorem dt_fourierProj (hV : ContDiff ℝ 1 ↿V) (N : ℕ) :
    dt (fun l t => fourierProj N (V l t)) = fun l t => fourierProj N (dt V l t) := by
  funext l t y
  simp only [dt_def]
  exact fderiv_fourierProj_param (f := fun s => V l s)
    (hV.comp (f := fun q : ℝ × (Fin n → ℝ) => (l, q.1, q.2)) (by fun_prop)) N t 1 y

omit [CompleteSpace E] in
/-- `P_N` commutes with `∂_{lₖ}`. -/
theorem dpar_fourierProj (hV : ContDiff ℝ 1 ↿V) (N : ℕ) (k : Fin p) :
    dpar k (fun l t => fourierProj N (V l t)) = fun l t => fourierProj N (dpar k V l t) := by
  funext l t y
  simp only [dpar_def]
  exact fderiv_fourierProj_param (f := fun m => V m t)
    (hV.comp (f := fun q : (Fin p → ℝ) × (Fin n → ℝ) => (q.1, t, q.2)) (by fun_prop)) N l
    (Pi.single k 1) y

/-- `P_N` commutes with `∂_{yᵢ}`. -/
theorem dy_fourierProj (hV : ∀ l t, ContDiff ℝ 1 (V l t)) (hp : ∀ l t, IsPeriodic (V l t))
    (N : ℕ) (i : Fin n) :
    dy i (fun l t => fourierProj N (V l t)) = fun l t => fourierProj N (dy i V l t) := by
  funext l t y
  simp only [dy_def]
  exact fderiv_fourierProj (hV l t) (hp l t) N i y

omit [CompleteSpace E] in
/-- `P_N` commutes with `∂ₜ` on smooth periodic families. -/
theorem IsPeriodicSmooth.dt_fourierProj (hV : IsPeriodicSmooth V) (N : ℕ) :
    PDE.dt (fun l t => fourierProj N (V l t)) = fun l t => fourierProj N (PDE.dt V l t) :=
  PDE.dt_fourierProj (hV.smooth.of_le (by exact_mod_cast le_top)) N

omit [CompleteSpace E] in
/-- `P_N` commutes with `∂_{lₖ}` on smooth periodic families. -/
theorem IsPeriodicSmooth.dpar_fourierProj (hV : IsPeriodicSmooth V) (N : ℕ) (k : Fin p) :
    PDE.dpar k (fun l t => fourierProj N (V l t)) = fun l t => fourierProj N (PDE.dpar k V l t) :=
  PDE.dpar_fourierProj (hV.smooth.of_le (by exact_mod_cast le_top)) N k

/-- `P_N` commutes with `∂_{yᵢ}` on smooth periodic families. -/
theorem IsPeriodicSmooth.dy_fourierProj (hV : IsPeriodicSmooth V) (N : ℕ) (i : Fin n) :
    PDE.dy i (fun l t => fourierProj N (V l t)) = fun l t => fourierProj N (PDE.dy i V l t) :=
  PDE.dy_fourierProj (fun l t => (hV.contDiff_slice l t).of_le (by exact_mod_cast le_top))
    hV.periodic N i

end Families


/-! ## Parseval's identity on the cell -/

/-- Parseval's identity on the cell for real functions, in the real form of the coefficients:
`∑_{k ∈ ℤⁿ} ((∫ cos (2π k·y) u)² + (∫ sin (2π k·y) u)²) = ∫_cell u²`. Transferred from
`UnitAddTorus.hasSum_sq_mFourierCoeff` through the measurable equivalence of the torus with
`(0, 1]ⁿ`; no periodicity is needed. -/
theorem hasSum_sq_cell {u : (Fin n → ℝ) → ℝ} (hu : Continuous u) :
    HasSum (fun k : Fin n → ℤ => (cellIntegral fun y => Real.cos (phase k y) * u y) ^ 2 +
      (cellIntegral fun y => Real.sin (phase k y) * u y) ^ 2) (cellIntegral fun y => u y ^ 2) := by
  set F : UnitAddTorus (Fin n) → ℂ := fun x => (u fun i => (AddCircle.equivIoc 1 0 (x i) : ℝ) : ℂ)
  obtain ⟨C, hC⟩ := isCompact_cell.exists_bound_of_continuousOn hu.continuousOn
  have hFm : Measurable F := by
    have : F = (fun x : {x : Fin n → ℝ //
        ∀ i, x i ∈ Ioc ((0 : Fin n → ℝ) i) ((0 : Fin n → ℝ) i + 1)} =>
        (u x.1 : ℂ)) ∘ UnitAddTorus.measurableEquivPiIoc (0 : Fin n → ℝ) := rfl
    rw [this]
    exact (Complex.continuous_ofReal.comp (hu.comp continuous_subtype_val)).measurable.comp
      (UnitAddTorus.measurableEquivPiIoc _).measurable
  have hbox : ∀ x : UnitAddTorus (Fin n), (fun i => (AddCircle.equivIoc 1 0 (x i) : ℝ)) ∈ cell n :=
    fun x => mem_cell.2 ⟨fun i => by simpa using (AddCircle.equivIoc 1 0 (x i)).2.1.le,
      fun i => by simpa using (AddCircle.equivIoc 1 0 (x i)).2.2⟩
  have hFL := MemLp.of_bound (μ := volume) (p := 2) hFm.aestronglyMeasurable C
    (ae_of_all _ fun x => by
    simpa [F] using hC _ (hbox x))
  have key := UnitAddTorus.hasSum_sq_mFourierCoeff (hFL.toLp F)
  have hset : (volume.restrict {x : Fin n → ℝ | ∀ i, x i ∈ Ioc ((0 : Fin n → ℝ) i)
      ((0 : Fin n → ℝ) i + 1)}) = volume.restrict (cell n) := by
    refine Measure.restrict_congr_set ?_
    have : {x : Fin n → ℝ | ∀ i, x i ∈ Ioc ((0 : Fin n → ℝ) i) ((0 : Fin n → ℝ) i + 1)} =
        univ.pi fun _ => Ioc 0 1 := by ext; simp
    rw [this, cell_def, volume_pi]
    exact Measure.univ_pi_Ioc_ae_eq_Icc
  have hmem : ∀ x ∈ {x : Fin n → ℝ | ∀ i, x i ∈ Ioc ((0 : Fin n → ℝ) i) ((0 : Fin n → ℝ) i + 1)},
      F (fun i => (x i : UnitAddCircle)) = u x := fun x hx => by
    simp only [F]
    congr 2
    funext i
    exact AddCircle.equivIoc_coe_of_mem (p := (1 : ℝ)) (a := 0) (hx i)
  have hmeas : MeasurableSet {x : Fin n → ℝ | ∀ i, x i ∈ Ioc ((0 : Fin n → ℝ) i)
      ((0 : Fin n → ℝ) i + 1)} := MeasurableSet.univ_pi' fun _ => measurableSet_Ioc
  have hsum : (∫ t, ‖(hFL.toLp F) t‖ ^ 2) = cellIntegral fun y => u y ^ 2 := by
    rw [integral_congr_ae ((hFL.coeFn_toLp).mono fun t ht => by rw [ht]),
      UnitAddTorus.integral_preimage _ 0, cellIntegral_def, ← hset]
    refine setIntegral_congr_fun hmeas fun x hx => ?_
    simp [hmem x hx]
  have hexp : ∀ (k : Fin n → ℤ) (x : Fin n → ℝ),
      UnitAddTorus.mFourier (-k) (fun i => (x i : UnitAddCircle)) =
        (Real.cos (phase k x) : ℂ) - (Real.sin (phase k x) : ℂ) * Complex.I := by
    intro k x
    have h : (∑ i, 2 * π * Complex.I * ((-k i : ℤ) : ℂ) * (x i : ℂ) / ((1 : ℝ) : ℂ)) =
        (-(phase k x) : ℝ) * Complex.I := by
      simp only [phase_def, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_sum,
        Complex.ofReal_intCast, Complex.ofReal_one, div_one, Int.cast_neg, Finset.mul_sum,
        ← Finset.sum_neg_distrib, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast; ring
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.neg_apply, fourier_coe_apply,
      ← Complex.exp_sum, h, Complex.exp_mul_I, Complex.ofReal_neg, Complex.cos_neg,
      Complex.sin_neg, Complex.ofReal_cos, Complex.ofReal_sin]
    ring
  have hcont : ∀ k : Fin n → ℤ, Continuous fun x => Real.cos (phase k x) * u x := fun k => by
    simp only [phase_def]; fun_prop
  have hcont' : ∀ k : Fin n → ℤ, Continuous fun x => Real.sin (phase k x) * u x := fun k => by
    simp only [phase_def]; fun_prop
  have hcoef : ∀ k, UnitAddTorus.mFourierCoeff (hFL.toLp F) k =
      ((cellIntegral fun y => Real.cos (phase k y) * u y : ℝ) : ℂ) -
        ((cellIntegral fun y => Real.sin (phase k y) * u y : ℝ) : ℂ) * Complex.I := by
    intro k
    rw [show UnitAddTorus.mFourierCoeff (hFL.toLp F) k = UnitAddTorus.mFourierCoeff F k from
      integral_congr_ae ((hFL.coeFn_toLp).mono fun t ht => by simp only [ht]),
      UnitAddTorus.mFourierCoeff_eq_integral _ _ 0]
    rw [setIntegral_congr_fun hmeas (g := fun x => (((Real.cos (phase k x) * u x : ℝ) : ℂ) -
        ((Real.sin (phase k x) * u x : ℝ) : ℂ) * Complex.I)) fun x hx => by
      rw [hmem x hx, hexp]; push_cast; ring]
    rw [hset, integral_sub, integral_mul_const, integral_complex_ofReal, integral_complex_ofReal]
    · simp only [cellIntegral_def]
    · exact integrableOn_cell (by fun_prop)
    · exact integrableOn_cell (by fun_prop)
  rw [← hsum]
  refine key.congr_fun fun k => ?_
  rw [hcoef, Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

/-! ## The `L²(cell)` structure -/

section Inner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- `∫_cell ⟪P_N u, w⟫ = ∑_{|kᵢ| ≤ N} (⟪ĉₖu, ĉₖw⟫ + ⟪ŝₖu, ŝₖw⟫)`. -/
theorem cellIntegral_inner_fourierProj {u w : (Fin n → ℝ) → E} (hw : Continuous w) (N : ℕ) :
    cellIntegral (fun y => ⟪fourierProj N u y, w y⟫) = ∑ k ∈ freqBox n N,
      (⟪cosCoeff k u, cosCoeff k w⟫ + ⟪sinCoeff k u, sinCoeff k w⟫) := by
  have hc : ∀ k (a : E), cellIntegral (fun y => Real.cos (phase k y) * ⟪a, w y⟫) =
      ⟪a, cosCoeff k w⟫ := fun k a => by
    simp only [cosCoeff, cellIntegral_def, ← real_inner_smul_right]
    exact integral_inner (integrableOn_cell (by fun_prop)) a
  have hs : ∀ k (a : E), cellIntegral (fun y => Real.sin (phase k y) * ⟪a, w y⟫) =
      ⟪a, sinCoeff k w⟫ := fun k a => by
    simp only [sinCoeff, cellIntegral_def, ← real_inner_smul_right]
    exact integral_inner (integrableOn_cell (by fun_prop)) a
  simp only [fourierProj, sum_inner, inner_add_left, real_inner_smul_left]
  rw [cellIntegral_def, integral_finsetSum _ (fun k _ => integrableOn_cell (by fun_prop))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_add (integrableOn_cell (by fun_prop)) (integrableOn_cell (by fun_prop))]
  simp only [cellIntegral_def] at hc hs
  exact congrArg₂ (· + ·) (hc k _) (hs k _)

/-- `P_N` is symmetric in `L²(cell)`. -/
theorem cellIntegral_inner_fourierProj_comm {u w : (Fin n → ℝ) → E} (hu : Continuous u)
    (hw : Continuous w) (N : ℕ) :
    cellIntegral (fun y => ⟪fourierProj N u y, w y⟫) =
      cellIntegral (fun y => ⟪u y, fourierProj N w y⟫) := by
  rw [show (fun y => ⟪u y, fourierProj N w y⟫) = fun y => ⟪fourierProj N w y, u y⟫ from
    funext fun y => real_inner_comm _ _, cellIntegral_inner_fourierProj (u := u) hw,
    cellIntegral_inner_fourierProj (u := w) hu]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [real_inner_comm (cosCoeff k u), real_inner_comm (sinCoeff k u)]

end Inner

section Euclidean

variable {ι : Type*} [Fintype ι]

/-- `P_N u` is a trigonometric polynomial of degree `≤ N`. -/
theorem fourierProj_mem_trigPoly (N : ℕ) (u : (Fin n → ℝ) → EuclideanSpace ℝ ι) :
    fourierProj N u ∈ trigPoly ι n N := by
  have : fourierProj N u = ∑ k ∈ freqBox n N, ((fun y => Real.cos (phase k y) • cosCoeff k u) +
      (fun y => Real.sin (phase k y) • sinCoeff k u)) := by
    funext y; simp [fourierProj, Finset.sum_apply]
  rw [this, trigPoly_def]
  refine Submodule.sum_mem _ fun k hk => Submodule.add_mem _ ?_ ?_
  · exact Submodule.subset_span ⟨k, mem_freqBox.1 hk, _, Or.inl rfl⟩
  · exact Submodule.subset_span ⟨k, mem_freqBox.1 hk, _, Or.inr rfl⟩

/-- `P_N` is the identity on trigonometric polynomials of degree `≤ N`. -/
theorem fourierProj_eq_self {N : ℕ} {f : (Fin n → ℝ) → EuclideanSpace ℝ ι}
    (hf : f ∈ trigPoly ι n N) : fourierProj N f = f := by
  rw [trigPoly_def] at hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨k, hk, v, rfl | rfl⟩ := hg
    · exact fourierProj_cos (mem_freqBox.2 hk) v
    · exact fourierProj_sin (mem_freqBox.2 hk) v
  | zero =>
    funext y
    simp [fourierProj, show (0 : (Fin n → ℝ) → EuclideanSpace ℝ ι) = fun _ => 0 from rfl,
      cosCoeff_zero, sinCoeff_zero]
  | add f g hf hg ihf ihg =>
    rw [show f + g = fun y => f y + g y from rfl,
      fourierProj_add
        (contDiff_isPeriodic_of_mem_trigPoly
          (by rwa [trigPoly_def] : f ∈ trigPoly ι n N)).1.continuous
        (contDiff_isPeriodic_of_mem_trigPoly
          (by rwa [trigPoly_def] : g ∈ trigPoly ι n N)).1.continuous,
      ihf, ihg]
    rfl
  | smul a f hf ih =>
    rw [show a • f = fun y => a • f y from rfl, fourierProj_smul, ih]
    rfl

/-- `P_N` is idempotent. -/
theorem fourierProj_fourierProj (N : ℕ) (u : (Fin n → ℝ) → EuclideanSpace ℝ ι) :
    fourierProj N (fourierProj N u) = fourierProj N u :=
  fourierProj_eq_self (fourierProj_mem_trigPoly N u)

/-- `u - P_N u` is `L²(cell)`-orthogonal to the trigonometric polynomials of degree `≤ N`. -/
theorem cellIntegral_inner_sub_fourierProj {N : ℕ} {u w : (Fin n → ℝ) → EuclideanSpace ℝ ι}
    (hu : Continuous u) (hw : w ∈ trigPoly ι n N) :
    cellIntegral (fun y => ⟪u y - fourierProj N u y, w y⟫) = 0 := by
  have hwc := (contDiff_isPeriodic_of_mem_trigPoly hw).1.continuous
  have h := cellIntegral_inner_fourierProj_comm hu hwc N
  rw [fourierProj_eq_self hw] at h
  simp only [inner_sub_left, cellIntegral_def] at h ⊢
  rw [integral_sub (integrableOn_cell (by fun_prop)) (integrableOn_cell (by fun_prop)), h,
    sub_self]

/-- Components of the cosine coefficient are the coefficients of the components. -/
theorem cosCoeff_apply {u : (Fin n → ℝ) → EuclideanSpace ℝ ι} (hu : Continuous u)
    (k : Fin n → ℤ) (j : ι) : cosCoeff k u j = cosCoeff k (fun y => u y j) := by
  simpa using map_cosCoeff (EuclideanSpace.proj j) hu k

/-- Components of the sine coefficient are the coefficients of the components. -/
theorem sinCoeff_apply {u : (Fin n → ℝ) → EuclideanSpace ℝ ι} (hu : Continuous u)
    (k : Fin n → ℤ) (j : ι) : sinCoeff k u j = sinCoeff k (fun y => u y j) := by
  simpa using map_sinCoeff (EuclideanSpace.proj j) hu k

/-- Parseval's identity on the cell: `∑_{k ∈ ℤⁿ} (‖ĉₖ‖² + ‖ŝₖ‖²) = ∫_cell ‖u‖²`. -/
theorem hasSum_norm_sq_coeff {u : (Fin n → ℝ) → EuclideanSpace ℝ ι} (hu : Continuous u) :
    HasSum (fun k => ‖cosCoeff k u‖ ^ 2 + ‖sinCoeff k u‖ ^ 2)
      (cellIntegral fun y => ‖u y‖ ^ 2) := by
  have hj : ∀ j : ι, Continuous fun y => u y j := fun j =>
    (EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp hu
  have h := hasSum_sum (s := Finset.univ) fun j _ => hasSum_sq_cell (hj j)
  convert h using 1
  · funext k
    simp only [EuclideanSpace.real_norm_sq_eq]
    simp only [cosCoeff_apply hu, sinCoeff_apply hu]
    simp only [Finset.sum_add_distrib, cosCoeff, sinCoeff, smul_eq_mul]
  · simp only [EuclideanSpace.real_norm_sq_eq, cellIntegral_def]
    exact integral_finsetSum _ fun j _ => integrableOn_cell (by fun_prop)

/-- The squared `L²(cell)` distance from `u` to `P_N u` is the sum of `‖ĉₖ‖² + ‖ŝₖ‖²` over the
frequencies outside the box. -/
theorem hasSum_norm_sub_fourierProj_sq {u : (Fin n → ℝ) → EuclideanSpace ℝ ι}
    (hu : Continuous u) (N : ℕ) :
    HasSum (fun k => if k ∈ freqBox n N then 0 else ‖cosCoeff k u‖ ^ 2 + ‖sinCoeff k u‖ ^ 2)
      (cellIntegral fun y => ‖u y - fourierProj N u y‖ ^ 2) := by
  set a : (Fin n → ℤ) → ℝ := fun k => ‖cosCoeff k u‖ ^ 2 + ‖sinCoeff k u‖ ^ 2
  have hbox : HasSum (fun k => if k ∈ freqBox n N then a k else 0) (∑ k ∈ freqBox n N, a k) := by
    have : HasSum (fun k => if k ∈ freqBox n N then a k else 0)
        (∑ k ∈ freqBox n N, if k ∈ freqBox n N then a k else 0) :=
      hasSum_sum_of_ne_finset_zero fun k hk => by simp [hk]
    rwa [Finset.sum_congr rfl fun k (hk : k ∈ freqBox n N) => ite_eq_left hk] at this
  have hPu : Continuous (fourierProj N u) := continuous_fourierProj N u
  have h1 : cellIntegral (fun y => ⟪u y, fourierProj N u y⟫) = ∑ k ∈ freqBox n N, a k := by
    rw [← cellIntegral_inner_fourierProj_comm hu hu, cellIntegral_inner_fourierProj hu]
    simp only [real_inner_self_eq_norm_sq, a]
  have h2 : cellIntegral (fun y => ‖fourierProj N u y‖ ^ 2) = ∑ k ∈ freqBox n N, a k := by
    have := cellIntegral_inner_fourierProj_comm hu hPu N
    rw [fourierProj_fourierProj] at this
    simp only [real_inner_self_eq_norm_sq] at this
    rw [this, h1]
  have e : cellIntegral (fun y => ‖u y - fourierProj N u y‖ ^ 2) =
      cellIntegral (fun y => ‖u y‖ ^ 2) - ∑ k ∈ freqBox n N, a k := by
    simp only [norm_sub_sq_real]
    rw [cellIntegral_def, integral_add (integrableOn_cell (by fun_prop))
      (integrableOn_cell (by fun_prop)), integral_sub (integrableOn_cell (by fun_prop))
      (integrableOn_cell (by fun_prop)), integral_const_mul]
    simp only [cellIntegral_def] at h1 h2 ⊢
    rw [h1, h2]
    ring
  rw [e]
  convert (hasSum_norm_sq_coeff hu).sub hbox using 1
  funext k
  split_ifs <;> simp [a]

/-- `trigPoly ι n N` is monotone in `N`. -/
theorem trigPoly_mono {N M : ℕ} (h : N ≤ M) : trigPoly ι n N ≤ trigPoly ι n M := by
  rw [trigPoly_def, trigPoly_def]
  exact Submodule.span_mono fun _ ⟨k, hk, v, hv⟩ =>
    ⟨k, fun i => (hk i).trans (by exact_mod_cast h), v, hv⟩

/-- `P_M P_N = P_N` for `N ≤ M`. -/
theorem fourierProj_fourierProj_of_le {N M : ℕ} (h : N ≤ M)
    (u : (Fin n → ℝ) → EuclideanSpace ℝ ι) :
    fourierProj M (fourierProj N u) = fourierProj N u :=
  fourierProj_eq_self (trigPoly_mono h (fourierProj_mem_trigPoly N u))

/-- `P_N` commutes with differences of continuous functions. -/
theorem fourierProj_sub {u v : (Fin n → ℝ) → EuclideanSpace ℝ ι} (hu : Continuous u)
    (hv : Continuous v) (N : ℕ) :
    fourierProj N (fun y => u y - v y) = fourierProj N u - fourierProj N v := by
  have e : (fun y => u y - v y) = fun y => u y + (-1 : ℝ) • v y := by
    funext y; simp [sub_eq_add_neg]
  rw [e, fourierProj_add (v := fun y => (-1 : ℝ) • v y) hu (hv.const_smul (-1 : ℝ)),
    fourierProj_smul, neg_one_smul, sub_eq_add_neg]

/-- Bessel's inequality: `‖P_N u‖_{L²(cell)} ≤ ‖u‖_{L²(cell)}`. -/
theorem cellIntegral_norm_fourierProj_sq_le {u : (Fin n → ℝ) → EuclideanSpace ℝ ι}
    (hu : Continuous u) (N : ℕ) :
    cellIntegral (fun y => ‖fourierProj N u y‖ ^ 2) ≤ cellIntegral (fun y => ‖u y‖ ^ 2) := by
  have h := hasSum_norm_sub_fourierProj_sq hu N
  have h0 : 0 ≤ cellIntegral (fun y => ‖u y - fourierProj N u y‖ ^ 2) :=
    h.nonneg fun k => by split_ifs <;> positivity
  have hPu := continuous_fourierProj N u
  have h1 := cellIntegral_inner_fourierProj_comm hu hPu N
  rw [fourierProj_fourierProj] at h1
  simp only [norm_sub_sq_real, real_inner_self_eq_norm_sq] at h0 h1
  simp only [cellIntegral_def] at h0 h1 ⊢
  rw [integral_add (integrableOn_cell (by fun_prop)) (integrableOn_cell (by fun_prop)),
    integral_sub (integrableOn_cell (by fun_prop)) (integrableOn_cell (by fun_prop)),
    integral_const_mul] at h0
  linarith

/-- `‖P_M u - P_N u‖_{L²(cell)} ≤ ‖u - P_N u‖_{L²(cell)}` for `N ≤ M`. -/
theorem cellIntegral_norm_fourierProj_sub_sq_le {u : (Fin n → ℝ) → EuclideanSpace ℝ ι}
    (hu : Continuous u) {N M : ℕ} (h : N ≤ M) :
    cellIntegral (fun y => ‖fourierProj M u y - fourierProj N u y‖ ^ 2) ≤
      cellIntegral (fun y => ‖u y - fourierProj N u y‖ ^ 2) := by
  have e : (fun y => fourierProj M u y - fourierProj N u y) =
      fourierProj M (fun y => u y - fourierProj N u y) := by
    rw [fourierProj_sub hu (continuous_fourierProj N u), fourierProj_fourierProj_of_le h]
    rfl
  have := cellIntegral_norm_fourierProj_sq_le (u := fun y => u y - fourierProj N u y)
    (hu.sub (continuous_fourierProj N u)) M
  rwa [← e] at this

/-- The coefficients of `∂ᵢu`: `‖ĉₖ(∂ᵢu)‖² + ‖ŝₖ(∂ᵢu)‖² = (2πkᵢ)² (‖ĉₖu‖² + ‖ŝₖu‖²)`. -/
theorem norm_sq_coeff_fderiv {u : (Fin n → ℝ) → EuclideanSpace ℝ ι} (hu : ContDiff ℝ 1 u)
    (hp : IsPeriodic u) (k : Fin n → ℤ) (i : Fin n) :
    ‖cosCoeff k (fun y => fderiv ℝ u y (Pi.single i 1))‖ ^ 2 +
      ‖sinCoeff k (fun y => fderiv ℝ u y (Pi.single i 1))‖ ^ 2 =
        (2 * π * k i) ^ 2 * (‖cosCoeff k u‖ ^ 2 + ‖sinCoeff k u‖ ^ 2) := by
  rw [cosCoeff_fderiv hu hp, sinCoeff_fderiv hu hp, norm_smul, norm_smul, norm_neg, mul_pow,
    mul_pow, Real.norm_eq_abs, sq_abs]
  ring

/-- The tail bound `(2πN)² ‖u - P_N u‖²_{L²(cell)} ≤ ∑ᵢ ‖∂ᵢu‖²_{L²(cell)}` for periodic `C¹`
`u` (Parseval, and `|ĉₖ(∂ᵢu)|² + |ŝₖ(∂ᵢu)|² = (2πkᵢ)² (|ĉₖ u|² + |ŝₖ u|²)`). -/
theorem sq_mul_cellIntegral_sub_fourierProj_le {u : (Fin n → ℝ) → EuclideanSpace ℝ ι}
    (hu : ContDiff ℝ 1 u) (hp : IsPeriodic u) (N : ℕ) :
    (2 * π * N) ^ 2 * cellIntegral (fun y => ‖u y - fourierProj N u y‖ ^ 2) ≤
      ∑ i, cellIntegral (fun y => ‖fderiv ℝ u y (Pi.single i 1)‖ ^ 2) := by
  set a : (Fin n → ℤ) → ℝ := fun k => ‖cosCoeff k u‖ ^ 2 + ‖sinCoeff k u‖ ^ 2
  have ha : ∀ k, 0 ≤ a k := fun k => by positivity
  have h1 := (hasSum_norm_sub_fourierProj_sq hu.continuous N).mul_left ((2 * π * N) ^ 2)
  have h2 : HasSum (fun k => ∑ i, (2 * π * k i) ^ 2 * a k)
      (∑ i, cellIntegral (fun y => ‖fderiv ℝ u y (Pi.single i 1)‖ ^ 2)) :=
    hasSum_sum fun i _ => (hasSum_norm_sq_coeff ((hu.continuous_fderiv one_ne_zero).clm_apply
      continuous_const)).congr_fun fun k => (norm_sq_coeff_fderiv hu hp k i).symm
  refine hasSum_le (fun k => ?_) h1 h2
  split_ifs with hk
  · rw [mul_zero]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (ha k)
  · obtain ⟨i, hi⟩ : ∃ i, (N : ℤ) < |k i| := by simpa [mem_freqBox] using hk
    have hNi : (2 * π * N) ^ 2 ≤ (2 * π * k i) ^ 2 := by
      have : (N : ℝ) ≤ |(k i : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hi.le
      rw [sq_le_sq, abs_of_nonneg (by positivity), abs_mul, abs_of_pos (by positivity)]
      exact mul_le_mul_of_nonneg_left this (by positivity)
    calc (2 * π * N) ^ 2 * a k ≤ (2 * π * k i) ^ 2 * a k :=
          mul_le_mul_of_nonneg_right hNi (ha k)
      _ ≤ ∑ j, (2 * π * k j) ^ 2 * a k :=
          Finset.single_le_sum (f := fun j => (2 * π * k j) ^ 2 * a k)
            (fun j _ => mul_nonneg (sq_nonneg _) (ha k)) (Finset.mem_univ i)

/-- The tail bound in norms: `2πN ‖u - P_N u‖_{L²(cell)} ≤ ∑ᵢ ‖∂ᵢu‖_{L²(cell)}`. -/
theorem mul_cellNorm_sub_fourierProj_le {u : (Fin n → ℝ) → EuclideanSpace ℝ ι}
    (hu : ContDiff ℝ 1 u) (hp : IsPeriodic u) (N : ℕ) :
    2 * π * N * cellNorm (fun y => u y - fourierProj N u y) ≤
      ∑ i, cellNorm (fun y => fderiv ℝ u y (Pi.single i 1)) := by
  have h := sq_mul_cellIntegral_sub_fourierProj_le hu hp N
  have hx : ∀ i, 0 ≤ cellIntegral (fun y => ‖fderiv ℝ u y (Pi.single i 1)‖ ^ 2) := fun i => by
    rw [cellIntegral_def]
    exact integral_nonneg fun y => sq_nonneg _
  simp only [cellNorm]
  calc 2 * π * N * √(cellIntegral fun y => ‖u y - fourierProj N u y‖ ^ 2)
      = √((2 * π * N) ^ 2 * cellIntegral fun y => ‖u y - fourierProj N u y‖ ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
    _ ≤ √(∑ i, cellIntegral (fun y => ‖fderiv ℝ u y (Pi.single i 1)‖ ^ 2)) :=
        Real.sqrt_le_sqrt h
    _ ≤ √((∑ i, √(cellIntegral (fun y => ‖fderiv ℝ u y (Pi.single i 1)‖ ^ 2))) ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        calc ∑ i, cellIntegral (fun y => ‖fderiv ℝ u y (Pi.single i 1)‖ ^ 2)
            = ∑ i, √(cellIntegral (fun y => ‖fderiv ℝ u y (Pi.single i 1)‖ ^ 2)) ^ 2 :=
              Finset.sum_congr rfl fun i _ => (Real.sq_sqrt (hx i)).symm
          _ ≤ _ := Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => Real.sqrt_nonneg _
    _ = _ := Real.sqrt_sq (Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _)

/-- `P_N` of a smooth family is a smooth periodic family. -/
theorem isPeriodicSmooth_fourierProj {p : ℕ}
    {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι} (hV : ContDiff ℝ ∞ ↿V) (N : ℕ) :
    IsPeriodicSmooth (fun l t => fourierProj N (V l t)) where
  smooth := by
    have hV' : ContDiff ℝ ∞ fun x : ((Fin p → ℝ) × ℝ) × (Fin n → ℝ) => V x.1.1 x.1.2 x.2 :=
      hV.comp (f := fun x : ((Fin p → ℝ) × ℝ) × (Fin n → ℝ) => (x.1.1, x.1.2, x.2))
        (by fun_prop)
    have hcont : ∀ l t, Continuous (V l t) := fun l t =>
      (hV.comp (f := fun y : Fin n → ℝ => (l, t, y)) (by fun_prop)).continuous
    have hcoef : ∀ (g : ℝ → ℝ), ContDiff ℝ ∞ g → ∀ k : Fin n → ℤ, ContDiff ℝ ∞
        fun q : (Fin p → ℝ) × ℝ => cellIntegral fun z => g (phase k z) • V q.1 q.2 z := by
      intro g hg k
      refine (contDiff_piLp 2).2 fun j => ?_
      have e : (fun q : (Fin p → ℝ) × ℝ => (cellIntegral fun z => g (phase k z) • V q.1 q.2 z) j) =
          fun q => cellIntegral fun z => g (phase k z) * V q.1 q.2 z j := funext fun q => by
        have := map_cosCoeff (k := 0) (EuclideanSpace.proj (𝕜 := ℝ) j)
          (u := fun z => g (phase k z) • V q.1 q.2 z) (by fun_prop)
        simpa [cosCoeff] using this
      rw [e]
      exact contDiff_cellIntegral
        (f := fun (q : (Fin p → ℝ) × ℝ) z => g (phase k z) * V q.1 q.2 z j)
        ((hg.comp ((contDiff_phase k).comp contDiff_snd)).mul
          ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp hV'))
    exact ContDiff.sum fun k _ =>
      ((((contDiff_phase k).comp (contDiff_snd.comp contDiff_snd)).cos).smul
        ((hcoef Real.cos Real.contDiff_cos k).comp (contDiff_fst.prodMk
          (contDiff_fst.comp contDiff_snd)))).add
      ((((contDiff_phase k).comp (contDiff_snd.comp contDiff_snd)).sin).smul
        ((hcoef Real.sin Real.contDiff_sin k).comp (contDiff_fst.prodMk
          (contDiff_fst.comp contDiff_snd))))
  periodic l t := isPeriodic_fourierProj N (V l t)

end Euclidean

end

end LorentzianCalderon.PDE
