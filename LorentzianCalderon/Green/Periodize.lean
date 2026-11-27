module

public import LorentzianCalderon.PDE.Limit
public import LorentzianCalderon.Green.Lens
public import LorentzianCalderon.Green.NormalForm

public section

/-!
# Local-in-time solutions of the normal form from the periodic core

The normal form `∂₀²v = a^{ij} ∂ᵢ∂ⱼv + b^μ ∂_μv + S` on `ℝ^{1+n}` (coordinates `z = (t, y)`),
with coefficients depending smoothly on a parameter `l`, equal to `a = c(l) id`, `b = 0`, `S = 0`
for `|y| > R₀`, and `S = 0` for `t ≤ t₀`. For a cell size `L > 2R₀` the coefficients and the
source, evaluated at `cellPoint L t y = (t, L (y - round y))`, are smooth and `ℤⁿ`-periodic in
`y` (`contDiff_comp_cellPoint`), so the periodic core (`PDE.exists_periodic_solution`) solves the
periodized problem in the variables `(t, y / L)` (`exists_periodized_solution`). The periodic
solution vanishes near the boundary of the cell `|yᵢ| < L/2` up to time `T` if `L` is large for
`T`: there the equation is the flat wave equation of `diag(-c, 1, …, 1)`, and finite propagation
speed on tents (`eq_zero_of_bottom`) applies (`periodizedSolution_eq_zero_of_near`). Cut off
outside the cell, it solves the original problem for `t < T` (`exists_local_solution`).
-/

namespace LorentzianCalderon

noncomputable section
open Set Filter Function Matrix
open scoped ContDiff Topology

variable {n : ℕ}

/-! ### Rounding -/

/-- `round x = k` if `|x - k| < 1/2`. -/
theorem round_eq_of_abs_sub_lt {x : ℝ} {k : ℤ} (h : |x - k| < 1 / 2) : round x = k := by
  rw [round_eq, Int.floor_eq_iff]
  rw [abs_lt] at h
  constructor <;> linarith

/-- The distance to the nearest integer is `1`-Lipschitz. -/
theorem abs_sub_round_sub_le (x x' : ℝ) :
    |x - round x| - |x - x'| ≤ |x' - round x'| := by
  have h1 := round_le x (round x')
  have h2 : |x - round x'| ≤ |x - x'| + |x' - round x'| := by
    have := abs_sub_le x x' (round x' : ℝ)
    linarith
  linarith

/-- `1/2` has distance at least `1/2` from every integer. -/
theorem half_le_abs_half_sub_int (m : ℤ) : 1 / 2 ≤ |1 / 2 - (m : ℝ)| := by
  rcases le_or_gt m 0 with h | h
  · have : (m : ℝ) ≤ 0 := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have : (1 : ℝ) ≤ m := by exact_mod_cast h
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- A point `c = ±L/2` of a cell face has distance at least `L/2` from `Lℤ`. -/
theorem half_le_abs_face_sub {L c : ℝ} (hL : 0 ≤ L) (hc : |c| = L / 2) (m : ℤ) :
    L / 2 ≤ |c - L * m| := by
  rcases abs_eq (by linarith : 0 ≤ L / 2) |>.1 hc with rfl | rfl
  · have h := mul_le_mul_of_nonneg_left (half_le_abs_half_sub_int m) hL
    rw [← abs_of_nonneg hL, ← abs_mul, abs_of_nonneg hL] at h
    calc L / 2 = L * (1 / 2) := by ring
      _ ≤ |L * (1 / 2 - m)| := h
      _ = |L / 2 - L * m| := by ring_nf
  · have h := mul_le_mul_of_nonneg_left (half_le_abs_half_sub_int (-m)) hL
    rw [← abs_of_nonneg hL, ← abs_mul, abs_of_nonneg hL] at h
    calc L / 2 = L * (1 / 2) := by ring
      _ ≤ |L * (1 / 2 - ((-m : ℤ) : ℝ))| := h
      _ = |-(L / 2) - L * m| := by
        push_cast
        rw [← abs_neg]
        ring_nf

/-! ### Cell points -/

/-- The point `(t, L (y - round y))` of `ℝ^{1+n}`: `y` reduced to the cell `[-1/2, 1/2]ⁿ` and
scaled by `L`. -/
def cellPoint (L t : ℝ) (y : Fin n → ℝ) : E n :=
  WithLp.toLp 2 (Fin.cons t fun i => L * (y i - round (y i)))

/-- The time of a cell point. -/
@[simp] theorem cellPoint_zero (L t : ℝ) (y : Fin n → ℝ) : cellPoint L t y 0 = t := by rfl

/-- The space coordinates of a cell point. -/
@[simp] theorem cellPoint_succ (L t : ℝ) (y : Fin n → ℝ) (i : Fin n) :
    cellPoint L t y i.succ = L * (y i - round (y i)) := by rfl

/-- Cell points are `ℤⁿ`-periodic in `y`. -/
theorem cellPoint_add_single (L t : ℝ) (y : Fin n → ℝ) (i : Fin n) :
    cellPoint L t (y + Pi.single i 1) = cellPoint L t y := by
  ext j
  refine Fin.cases rfl (fun k => ?_) j
  simp only [cellPoint_succ, Pi.add_apply]
  by_cases hk : k = i
  · subst hk
    simp [round_add_one]
  · simp [hk]

/-- A space coordinate is bounded by the spatial norm. -/
theorem abs_apply_succ_le_norm_spatial (z : E n) (i : Fin n) : |z i.succ| ≤ ‖spatial z‖ := by
  have := PiLp.norm_apply_le (spatial z) i
  rwa [spatial_apply, Real.norm_eq_abs] at this

/-- A point `(f, g)` of `ℝ^{1+n}` with smooth coordinates depends smoothly on the parameter. -/
theorem contDiff_toLp_cons {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {f : P → ℝ}
    {g : P → Fin n → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ∀ i, ContDiff ℝ ∞ fun q => g q i) :
    ContDiff ℝ ∞ fun q => (WithLp.toLp 2 (Fin.cons (f q) (g q) : Fin (n + 1) → ℝ) : E n) := by
  refine (contDiff_piLp 2).2 fun j => ?_
  refine Fin.cases ?_ (fun i => ?_) j
  · simpa using hf
  · simpa using hg i

/-- A smooth function of `(l, z)` that is independent of `z` for `|y| > R₀` stays smooth when
evaluated at `cellPoint L t y`, for `L > 2 R₀`: where `y` is near a cell face, `cellPoint` is far
out; elsewhere `round y` is locally constant. -/
theorem contDiff_comp_cellPoint {P X : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X] {f : P × E n → X} (hf : ContDiff ℝ ∞ f)
    {R₀ L : ℝ} (hL0 : 0 < L) (hL : 2 * R₀ < L)
    (hfar : ∀ l z z', R₀ < ‖spatial z‖ → R₀ < ‖spatial z'‖ → f (l, z) = f (l, z')) :
    ContDiff ℝ ∞ fun q : P × ℝ × (Fin n → ℝ) => f (q.1, cellPoint L q.2.1 q.2.2) := by
  refine contDiff_iff_contDiffAt.2 fun ⟨l, t, y⟩ => ?_
  by_cases h : ∀ i, |y i - round (y i)| < 1 / 2
  · have hev : ∀ᶠ q : P × ℝ × (Fin n → ℝ) in 𝓝 (l, t, y), ∀ i,
        round (q.2.2 i) = round (y i) := by
      refine eventually_all.2 fun i => ?_
      have hc : Continuous fun q : P × ℝ × (Fin n → ℝ) => q.2.2 i := by fun_prop
      filter_upwards [hc.continuousAt.eventually
        ((isOpen_lt (continuous_abs.comp (continuous_sub_right _)) continuous_const).mem_nhds
          (h i))] with q hq
      exact round_eq_of_abs_sub_lt hq
    have hs : ContDiff ℝ ∞ fun q : P × ℝ × (Fin n → ℝ) =>
        f (q.1, (WithLp.toLp 2 (Fin.cons q.2.1 fun i => L * (q.2.2 i - round (y i))) : E n)) :=
      hf.comp (contDiff_fst.prodMk (contDiff_toLp_cons (by fun_prop) fun i => by fun_prop))
    refine hs.contDiffAt.congr_of_eventuallyEq ?_
    filter_upwards [hev] with q hq
    simp only [cellPoint, hq]
  · push Not at h
    obtain ⟨i, hi⟩ := h
    set δ := 1 / 2 - R₀ / L
    have hδ : 0 < δ := by
      have : R₀ / L < 1 / 2 := by rw [div_lt_iff₀ hL0]; linarith
      simp only [δ]
      linarith
    have hfar' : ∀ x : ℝ, 1 / 2 - δ < |x - round x| → ∀ (t' : ℝ) (y' : Fin n → ℝ),
        y' i = x → R₀ < ‖spatial (cellPoint L t' y')‖ := by
      intro x hx t' y' hy'
      refine lt_of_lt_of_le ?_ (abs_apply_succ_le_norm_spatial _ i)
      rw [cellPoint_succ, hy', abs_mul, abs_of_pos hL0]
      have : R₀ = L * (1 / 2 - δ) := by simp only [δ]; field_simp; ring
      rw [this]
      exact mul_lt_mul_of_pos_left hx hL0
    have hy : R₀ < ‖spatial (cellPoint L t y)‖ := hfar' (y i) (by linarith) t y rfl
    have hev : ∀ᶠ q : P × ℝ × (Fin n → ℝ) in 𝓝 (l, t, y), |y i - q.2.2 i| < δ := by
      have hc : Continuous fun q : P × ℝ × (Fin n → ℝ) => |y i - q.2.2 i| := by fun_prop
      exact hc.continuousAt.eventually (gt_mem_nhds (by simpa using hδ))
    have hs : ContDiff ℝ ∞ fun q : P × ℝ × (Fin n → ℝ) => f (q.1, cellPoint L t y) :=
      hf.comp (contDiff_fst.prodMk contDiff_const)
    refine hs.contDiffAt.congr_of_eventuallyEq ?_
    filter_upwards [hev] with q hq
    refine hfar q.1 _ _ (hfar' (q.2.2 i) ?_ q.2.1 q.2.2 rfl) hy
    have := abs_sub_round_sub_le (y i) (q.2.2 i)
    linarith

/-- Inside the open cell `|yᵢ| < L/2`, `cellPoint` undoes the scaling. -/
theorem cellPoint_of_mem_cell {L : ℝ} (hL : 0 < L) {z : E n}
    (hz : ∀ i : Fin n, |z i.succ| < L / 2) :
    cellPoint L (z 0) (fun i => L⁻¹ * z i.succ) = z := by
  ext j
  refine Fin.cases rfl (fun i => ?_) j
  have hr : round (L⁻¹ * z i.succ) = 0 := by
    refine round_eq_of_abs_sub_lt ?_
    rw [Int.cast_zero, sub_zero, abs_mul, abs_of_pos (inv_pos.2 hL), inv_mul_lt_iff₀ hL]
    linarith [hz i]
  rw [cellPoint_succ, hr, Int.cast_zero, sub_zero, mul_inv_cancel_left₀ hL.ne']

/-- Near a cell face, `cellPoint` is far out: if `|c| = L/2` then the `i`-th coordinate of the
cell point of `z` is at least `L/2 - |zᵢ - c|`. -/
theorem le_abs_cellPoint_succ {L : ℝ} (hL : 0 < L) (z : E n) (i : Fin n) {c : ℝ}
    (hc : |c| = L / 2) :
    L / 2 - |z i.succ - c| ≤ |cellPoint L (z 0) (fun j => L⁻¹ * z j.succ) i.succ| := by
  rw [cellPoint_succ, mul_sub, mul_inv_cancel_left₀ hL.ne']
  have h := half_le_abs_face_sub hL.le hc (round (L⁻¹ * z i.succ))
  have h3 := abs_sub_le c (z i.succ) (L * round (L⁻¹ * z i.succ))
  have h4 := abs_sub_comm c (z i.succ)
  linarith

/-! ### Lifting periodic families to `ℝ^{1+n}` -/

section Lift

open PDE

variable {p : ℕ}

/-- The function `z = (t, y) ↦ V(l, t, y / L)` (its only component) on `ℝ^{1+n}`. -/
def liftZ (L : ℝ) (V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ (Fin 1))
    (l : Fin p → ℝ) (z : E n) : ℝ :=
  V l (z 0) (fun i => L⁻¹ * z i.succ) 0

/-- The linear part `z ↦ (0, t, y / L)` of the map `z ↦ (l, t, y / L)`. -/
def liftCLM (p : ℕ) (L : ℝ) : E n →L[ℝ] (Fin p → ℝ) × ℝ × (Fin n → ℝ) :=
  (0 : E n →L[ℝ] (Fin p → ℝ)).prod ((EuclideanSpace.proj (0 : Fin (n + 1))).prod
    (ContinuousLinearMap.pi fun i : Fin n => L⁻¹ • EuclideanSpace.proj i.succ))

/-- The direction of `(t, y)`-space corresponding to the coordinate `k` of `ℝ^{1+n}`. -/
def zDir (k : Fin (n + 1)) : Dir n p := Fin.cases Dir.time Dir.space k

/-- The scaling factor of the coordinate `k`: `1` for time, `L⁻¹` for space. -/
def zScale (L : ℝ) (k : Fin (n + 1)) : ℝ := Fin.cases 1 (fun _ => L⁻¹) k

/-- `liftCLM` maps the coordinate vectors to the scaled coordinate directions. -/
theorem liftCLM_single (L : ℝ) (k : Fin (n + 1)) :
    liftCLM p L (EuclideanSpace.single k 1) = zScale L k • (zDir (p := p) k).vec := by
  refine Fin.cases ?_ (fun i => ?_) k
  · simp [liftCLM, zScale, zDir, Dir.vec_time]
    ext j
    simp
  · simp only [liftCLM, zScale, zDir, Fin.cases_succ, Dir.vec_space]
    ext j
    · simp
    · simp [Fin.succ_ne_zero]
    · simp [Pi.single_apply]

/-- The lift of a smooth family is smooth in `(l, z)`. -/
theorem contDiff_liftZ {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ (Fin 1)}
    (hV : ContDiff ℝ ∞ ↿V) (L : ℝ) :
    ContDiff ℝ ∞ fun q : (Fin p → ℝ) × E n => liftZ L V q.1 q.2 := by
  have h : ContDiff ℝ ∞ fun q : (Fin p → ℝ) × E n =>
      ((q.1, q.2 0, fun i => L⁻¹ * q.2 i.succ) : (Fin p → ℝ) × ℝ × (Fin n → ℝ)) := by
    refine contDiff_fst.prodMk (((contDiff_coordinate 0).comp contDiff_snd).prodMk
      (contDiff_pi.2 fun i => contDiff_const.mul ((contDiff_coordinate i.succ).comp contDiff_snd)))
  exact (contDiff_piLp_apply (p := 2)).comp (hV.comp h)

/-- The derivative of a lift, by the chain rule. -/
theorem hasFDerivAt_liftZ {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ (Fin 1)}
    (hV : Differentiable ℝ ↿V) (L : ℝ) (l : Fin p → ℝ) (z : E n) :
    HasFDerivAt (liftZ L V l)
      ((EuclideanSpace.proj (0 : Fin 1) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ).comp
        ((fderiv ℝ ↿V (l, z 0, fun i => L⁻¹ * z i.succ)).comp (liftCLM p L))) z := by
  have hι : HasFDerivAt (fun z : E n =>
      ((l, z 0, fun i => L⁻¹ * z i.succ) : (Fin p → ℝ) × ℝ × (Fin n → ℝ))) (liftCLM p L) z := by
    have : (fun z : E n => ((l, z 0, fun i => L⁻¹ * z i.succ) : (Fin p → ℝ) × ℝ × (Fin n → ℝ)))
        = fun z => (l, 0, 0) + liftCLM p L z := by
      funext z
      simp [liftCLM]
    rw [this]
    exact (liftCLM p L).hasFDerivAt.const_add _
  exact (EuclideanSpace.proj (0 : Fin 1)).hasFDerivAt.comp z ((hV _).hasFDerivAt.comp z hι)

/-- `∂ₖ` of a lifted family is the lift of the corresponding derivative, scaled. -/
theorem d_liftZ {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ (Fin 1)}
    (hV : Differentiable ℝ ↿V) (L : ℝ) (l : Fin p → ℝ) (z : E n) (k : Fin (n + 1)) :
    d (liftZ L V l) z k = zScale L k * liftZ L ((zDir k).d V) l z := by
  have hk : zDir (p := p) k ≠ Dir.self := by
    refine Fin.cases ?_ (fun i => ?_) k <;> simp [zDir]
  rw [d_def, (hasFDerivAt_liftZ hV L l z).fderiv]
  simp only [ContinuousLinearMap.comp_apply, liftCLM_single, map_smul]
  rw [liftZ, Dir.d_eq_fderiv hk hV]
  simp

/-- The lift of a differentiable family is differentiable. -/
theorem differentiable_liftZ {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ (Fin 1)}
    (hV : Differentiable ℝ ↿V) (L : ℝ) (l : Fin p → ℝ) : Differentiable ℝ (liftZ L V l) :=
  fun z => (hasFDerivAt_liftZ hV L l z).differentiableAt

/-- `∂ᵢ∂ⱼ` of a lifted family is the lift of the corresponding second derivative, scaled. -/
theorem d2_liftZ {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ (Fin 1)}
    (hV : ContDiff ℝ ∞ ↿V) (L : ℝ) (l : Fin p → ℝ) (z : E n) (i j : Fin (n + 1)) :
    d2 (liftZ L V l) z i j =
      zScale L j * (zScale L i * liftZ L ((zDir i).d ((zDir j).d V)) l z) := by
  have hd := hV.differentiable (by simp)
  have hdj : Differentiable ℝ ↿((zDir (p := p) j).d V) :=
    (Dir.contDiff_d hV _).differentiable (by simp)
  rw [d2_def]
  simp_rw [d_liftZ hd L l _ j]
  rw [d_const_mul (differentiable_liftZ hdj L l z), d_liftZ hdj]

end Lift

/-! ### The periodized problem -/

section Periodized

open PDE

variable {p : ℕ}

/-- Hypotheses on the normal form `∂₀²v = a^{ij} ∂ᵢ∂ⱼv + b^μ ∂_μv + S` with parameters `l`:
smooth coefficients, `a` symmetric and uniformly positive definite for `(l, t)` in compact sets,
`a = c(l) id` with `0 < c(l) ≤ 1`, `b = 0` and `S = 0` for `|y| > R₀`, and `S = 0` for
`t ≤ t₀`. -/
structure IsFlatNormalForm (A : Fin n → Fin n → (Fin p → ℝ) → E n → ℝ)
    (B : Fin (n + 1) → (Fin p → ℝ) → E n → ℝ) (S : (Fin p → ℝ) → E n → ℝ)
    (c : (Fin p → ℝ) → ℝ) (R₀ t₀ : ℝ) : Prop where
  smooth_A : ∀ i j, ContDiff ℝ ∞ fun q : (Fin p → ℝ) × E n => A i j q.1 q.2
  smooth_B : ∀ k, ContDiff ℝ ∞ fun q : (Fin p → ℝ) × E n => B k q.1 q.2
  smooth_S : ContDiff ℝ ∞ fun q : (Fin p → ℝ) × E n => S q.1 q.2
  symm : ∀ i j l z, A i j l z = A j i l z
  pos : ∀ K : Set ((Fin p → ℝ) × ℝ), IsCompact K → ∃ κ > 0, ∀ l z, (l, z 0) ∈ K →
    ∀ ξ : Fin n → ℝ, κ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, A i j l z * ξ i * ξ j
  c_pos : ∀ l, 0 < c l
  c_le_one : ∀ l, c l ≤ 1
  far_A : ∀ l z, R₀ < ‖spatial z‖ → ∀ i j, A i j l z = if i = j then c l else 0
  far_B : ∀ l z, R₀ < ‖spatial z‖ → ∀ k, B k l z = 0
  far_S : ∀ l z, R₀ < ‖spatial z‖ → S l z = 0
  past_S : ∀ l z, z 0 ≤ t₀ → S l z = 0

/-- The coefficients of the periodized problem in the variables `(t, y / L)`. -/
def periodCoeffs (A : Fin n → Fin n → (Fin p → ℝ) → E n → ℝ)
    (B : Fin (n + 1) → (Fin p → ℝ) → E n → ℝ) (L : ℝ) : HypCoeffs p n (Fin 1) where
  a i j l t y := A i j l (cellPoint L t y) / L ^ 2
  bt l t y := B 0 l (cellPoint L t y) • ContinuousLinearMap.id ℝ _
  b i l t y := (B i.succ l (cellPoint L t y) / L) • ContinuousLinearMap.id ℝ _
  c _ _ _ := 0

/-- The source of the periodized problem. -/
def periodSource (S : (Fin p → ℝ) → E n → ℝ) (L : ℝ) (l : Fin p → ℝ) (t : ℝ) (y : Fin n → ℝ) :
    EuclideanSpace ℝ (Fin 1) :=
  S l (cellPoint L t y) • EuclideanSpace.single 0 1

variable {A : Fin n → Fin n → (Fin p → ℝ) → E n → ℝ} {B : Fin (n + 1) → (Fin p → ℝ) → E n → ℝ}
  {S : (Fin p → ℝ) → E n → ℝ} {c : (Fin p → ℝ) → ℝ} {R₀ t₀ L : ℝ}

/-- Functions of cell points are periodic. -/
theorem isPeriodic_comp_cellPoint {X : Type*} (f : E n → X) (L t : ℝ) :
    IsPeriodic fun y => f (cellPoint L t y) := isPeriodic_iff.2 fun i y => by
  simp only [cellPoint_add_single]

/-- `contDiff_comp_cellPoint` for the coefficients of a flat normal form. -/
theorem IsFlatNormalForm.contDiff_comp {f : (Fin p → ℝ) × E n → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfar : ∀ l z, R₀ < ‖spatial z‖ → ∀ z', R₀ < ‖spatial z'‖ → f (l, z) = f (l, z'))
    (hL0 : 0 < L) (hL : 2 * R₀ < L) :
    ContDiff ℝ ∞ fun q : (Fin p → ℝ) × ℝ × (Fin n → ℝ) => f (q.1, cellPoint L q.2.1 q.2.2) :=
  contDiff_comp_cellPoint hf hL0 hL fun l z z' hz hz' => hfar l z hz z' hz'

/-- The periodized coefficients satisfy the hypotheses of the periodic core. -/
theorem IsFlatNormalForm.isGood (h : IsFlatNormalForm A B S c R₀ t₀) (hL0 : 0 < L)
    (hL : 2 * R₀ < L) : (periodCoeffs A B L).IsGood where
  smooth_a i j := (IsFlatNormalForm.contDiff_comp (h.smooth_A i j) (fun l z hz z' hz' => by
    rw [h.far_A l z hz, h.far_A l z' hz']) hL0 hL).div_const _
  smooth_bt := (IsFlatNormalForm.contDiff_comp (h.smooth_B 0) (fun l z hz z' hz' => by
    simp only [h.far_B l z hz, h.far_B l z' hz']) hL0 hL).smul contDiff_const
  smooth_b i := ((IsFlatNormalForm.contDiff_comp (h.smooth_B i.succ) (fun l z hz z' hz' => by
    simp only [h.far_B l z hz, h.far_B l z' hz']) hL0 hL).div_const _).smul contDiff_const
  smooth_c := contDiff_const
  periodic_a i j l t := isPeriodic_comp_cellPoint (fun z => A i j l z / L ^ 2) L t
  periodic_bt l t := isPeriodic_comp_cellPoint
    (fun z => B 0 l z • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))) L t
  periodic_b i l t := isPeriodic_comp_cellPoint
    (fun z => (B i.succ l z / L) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))) L t
  periodic_c l t := isPeriodic_iff.2 fun _ _ => rfl
  symm i j := by
    funext l t y
    simp only [periodCoeffs, h.symm i j]
  pos K hK := by
    obtain ⟨κ, hκ, hpos⟩ := h.pos K hK
    refine ⟨κ / L ^ 2, by positivity, fun l t hlt y ξ => ?_⟩
    have := hpos l (cellPoint L t y) (by simpa using hlt) ξ
    simp only [periodCoeffs]
    have hsum : ∑ i, ∑ j, A i j l (cellPoint L t y) / L ^ 2 * ξ i * ξ j =
        (∑ i, ∑ j, A i j l (cellPoint L t y) * ξ i * ξ j) / L ^ 2 := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hsum, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right this (by positivity)

/-- The periodized source is smooth and periodic. -/
theorem IsFlatNormalForm.isPeriodicSmooth_source (h : IsFlatNormalForm A B S c R₀ t₀)
    (hL0 : 0 < L) (hL : 2 * R₀ < L) : IsPeriodicSmooth (periodSource S L) where
  smooth := (IsFlatNormalForm.contDiff_comp h.smooth_S (fun l z hz z' hz' => by
    rw [h.far_S l z hz, h.far_S l z' hz']) hL0 hL).smul contDiff_const
  periodic l t := isPeriodic_comp_cellPoint (fun z => S l z • EuclideanSpace.single 0 1) L t

/-- The cell point of `z = (t, y)` at scale `L`: `(t, y)` reduced to the cell `|yᵢ| ≤ L/2`. -/
def zCell (L : ℝ) (z : E n) : E n := cellPoint L (z 0) (fun i => L⁻¹ * z i.succ)

/-- Coordinates of a finite sum. -/
theorem ofLp_sum_apply {ι : Type*} (s : Finset ι) (f : ι → EuclideanSpace ℝ (Fin 1))
    (j : Fin 1) : (∑ i ∈ s, f i) j = ∑ i ∈ s, f i j := by
  simp [WithLp.ofLp_sum]

/-- A solution of the periodized problem, lifted to `ℝ^{1+n}`, solves the normal form with the
coefficients evaluated at the cell point. -/
theorem liftZ_eq_of_periodic {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ (Fin 1)}
    (hV : ContDiff ℝ ∞ ↿V)
    (heq : ∀ l t y, dt (dt V) l t y = (periodCoeffs A B L).apply V l t y + periodSource S L l t y)
    (hL0 : 0 < L) (l : Fin p → ℝ) (z : E n) :
    d2 (liftZ L V l) z 0 0 =
      ∑ i, ∑ j, A i j l (zCell L z) * d2 (liftZ L V l) z i.succ j.succ +
        ∑ k, B k l (zCell L z) * d (liftZ L V l) z k + S l (zCell L z) := by
  have hd := hV.differentiable (by simp)
  simp only [d2_liftZ hV, d_liftZ hd]
  simp only [zScale, zDir, Fin.cases_zero, Fin.cases_succ, Dir.d_time, Dir.d_space, one_mul]
  have h := congrArg (fun v : EuclideanSpace ℝ (Fin 1) => v 0)
    (heq l (z 0) (fun i => L⁻¹ * z i.succ))
  simp only [HypCoeffs.apply_def, periodCoeffs, periodSource, PiLp.add_apply, ofLp_sum_apply,
    PiLp.smul_apply, smul_eq_mul, _root_.smul_apply, ContinuousLinearMap.id_apply,
    _root_.zero_apply, add_zero] at h
  rw [liftZ, h, Fin.sum_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ, one_mul, zCell, liftZ, Dir.d_time, Dir.d_space]
  simp only [PiLp.single_apply, ite_true, mul_one]
  have hL : L ≠ 0 := hL0.ne'
  have e1 : ∀ (x : Fin n → Fin n → ℝ) (w : Fin n → Fin n → ℝ),
      ∑ i, ∑ j, w i j / L ^ 2 * x i j = ∑ i, ∑ j, w i j * (L⁻¹ * (L⁻¹ * x i j)) :=
    fun x w => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      field_simp
  have e2 : ∀ (x : Fin n → ℝ) (w : Fin n → ℝ),
      ∑ i, w i / L * x i = ∑ i, w i * (L⁻¹ * x i) :=
    fun x w => Finset.sum_congr rfl fun i _ => by field_simp
  rw [e1 (fun i j => (dy i (dy j V) l (z 0) fun i => L⁻¹ * z i.succ) 0)
    (fun i j => A i j l (cellPoint L (z 0) fun i => L⁻¹ * z i.succ)),
    e2 (fun i => (dy i V l (z 0) fun i => L⁻¹ * z i.succ) 0)
    (fun i => B i.succ l (cellPoint L (z 0) fun i => L⁻¹ * z i.succ))]
  ring

/-- The periodized problem has a solution vanishing for `t ≤ t₀`
(`PDE.exists_periodic_solution`). -/
theorem IsFlatNormalForm.exists_periodized (h : IsFlatNormalForm A B S c R₀ t₀) (hL0 : 0 < L)
    (hL : 2 * R₀ < L) :
    ∃ V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ (Fin 1), IsPeriodicSmooth V ∧
      (∀ l t y, t ≤ t₀ → V l t y = 0) ∧
      ∀ l t y, dt (dt V) l t y = (periodCoeffs A B L).apply V l t y + periodSource S L l t y :=
  exists_periodic_solution (h.isGood hL0 hL) (h.isPeriodicSmooth_source hL0 hL)
    fun l t y ht => by
      rw [periodSource, h.past_S l (cellPoint L t y) (by simpa using ht), zero_smul]

end Periodized

/-! ### Finite propagation speed for the flat wave equation -/

section Tent

variable {c : ℝ}

/-- Second derivatives only depend on the germ. -/
theorem d2_congr {u v : E n → ℝ} {x : E n} (h : u =ᶠ[𝓝 x] v) (i j : Fin (n + 1)) :
    d2 u x i j = d2 v x i j := by
  have h' : (fun y => d u y j) =ᶠ[𝓝 x] fun y => d v y j :=
    h.eventually_nhds.mono fun y hy => by
      change d u y j = d v y j
      rw [d_congr hy]
  rw [d2_def, d2_def, d_congr h']

/-- The quadratic form of `diag(-c, 1, …, 1)` on coefficient vectors. -/
theorem sum_lapseDiag (c : ℝ) (ξ η : Fin (n + 1) → ℝ) :
    ∑ j, ∑ k, lapseDiag c j k * ξ j * η k = -c * ξ 0 * η 0 + ∑ i : Fin n, ξ i.succ * η i.succ := by
  have h : ∀ j, ∑ k, lapseDiag c j k * ξ j * η k = lapseDiag c j j * ξ j * η j := fun j => by
    rw [Finset.sum_eq_single j (fun k _ hk => by simp [lapseDiag_def, diagonal_apply_ne _ hk.symm])
      (by simp)]
  rw [Finset.sum_congr rfl fun j _ => h j, Fin.sum_univ_succ]
  simp [lapseDiag_def]

/-- The bilinear form of `diag(-c, 1, …, 1)`. -/
theorem form_lapseDiag (c : ℝ) (v w : E n) :
    form (lapseDiag c) v w = -c * v 0 * w 0 + ∑ i : Fin n, v i.succ * w i.succ := by
  rw [← sum_lapseDiag]
  simp only [form_def]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

/-- `diag(-c, 1, …, 1)` is Lorentzian for `c > 0`. -/
theorem isLorentzian_lapseDiag (hc : 0 < c) : IsLorentzian (lapseDiag (n := n) c) where
  symm := by simp [lapseDiag_def]
  det_neg := by
    rw [lapseDiag_def, det_diagonal, Fin.prod_univ_succ]
    simp [Fin.succ_ne_zero, hc]
  spacelike := by
    let ℓ : E n →ₗ[ℝ] ℝ := (EuclideanSpace.proj (0 : Fin (n + 1)) : E n →L[ℝ] ℝ)
    have hsurj : Function.Surjective ℓ := fun t =>
      ⟨EuclideanSpace.single 0 t, by simp [ℓ]⟩
    refine ⟨LinearMap.ker ℓ, ⟨?_, fun v hv hv0 => ?_⟩⟩
    · have h := LinearMap.finrank_range_add_finrank_ker ℓ
      rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_self,
        finrank_euclideanSpace_fin] at h
      omega
    · have h0 : v 0 = 0 := hv
      rw [form_lapseDiag, h0]
      obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
        by_contra hall
        push Not at hall
        exact hv0 (by ext j; simp [hall j])
      obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 (show j ≠ 0 from fun h => hj (by rw [h]; exact h0))
      have : v i.succ * v i.succ ≤ ∑ k : Fin n, v k.succ * v k.succ :=
        Finset.single_le_sum (f := fun k : Fin n => v k.succ * v k.succ)
          (fun k _ => mul_self_nonneg _) (Finset.mem_univ i)
      have hpos : 0 < v i.succ * v i.succ := mul_self_pos.2 hj
      linarith

/-- A function with `∂₀φ = 1` and `Σᵢ (∂ᵢφ)² < 1` is temporal for `diag(-c, 1, …, 1)`,
`0 < c ≤ 1`, with the orientation `∂₀`. -/
theorem isFutureTimelike_lapseDiag (hc : 0 < c) (hc1 : c ≤ 1) {φ : E n → ℝ} {x : E n}
    (h0 : d φ x 0 = 1) (hs : ∑ i : Fin n, d φ x i.succ ^ 2 < 1) :
    IsFutureTimelike (fun _ => lapseDiag (n := n) c) (fun _ => EuclideanSpace.single 0 1) x
      (-grad (fun _ => lapseDiag c) φ x) where
  timelike := by
    rw [form_neg_grad (g := fun _ => lapseDiag c) (isLorentzian_lapseDiag hc)]
    simp only [coform_def, inv_lapseDiag hc.ne', sum_lapseDiag, h0]
    have : 1 ≤ c⁻¹ := one_le_inv₀ hc |>.2 hc1
    have hs' : ∑ i : Fin n, d φ x i.succ * d φ x i.succ < 1 := by simpa [sq] using hs
    linarith
  future := by
    rw [form_neg_grad_left (g := fun _ => lapseDiag c) (isLorentzian_lapseDiag hc)]
    rw [← d_def]
    rw [h0]
    norm_num

/-- The partial derivatives of `tentTime`. -/
theorem d_tentTime (a : ℝ) (xc x : E n) (k : Fin (n + 1)) :
    d (tentTime a xc) x k = (if k = 0 then 1 else 0) +
      a * (2 * √(1 + ∑ i : Fin n, (x - xc) i.succ ^ 2))⁻¹ *
        ∑ i : Fin n, 2 * (x - xc) i.succ * (if k = i.succ then 1 else 0) := by
  rw [d_def, (hasFDerivAt_tentTime a xc x).fderiv]
  simp [PiLp.single_apply, eq_comm]

/-- `∂₀ tentTime = 1`. -/
theorem d_tentTime_zero (a : ℝ) (xc x : E n) : d (tentTime a xc) x 0 = 1 := by
  rw [d_tentTime]
  simp [(Fin.succ_ne_zero _).symm]

/-- The spatial gradient of `tentTime a` has norm at most `|a|`. -/
theorem sum_d_tentTime_sq_le (a : ℝ) (xc x : E n) :
    ∑ i : Fin n, d (tentTime a xc) x i.succ ^ 2 ≤ a ^ 2 := by
  have hd : ∀ j : Fin n, d (tentTime a xc) x j.succ =
      a * (x - xc) j.succ / √(1 + ∑ i : Fin n, (x - xc) i.succ ^ 2) := by
    intro j
    rw [d_tentTime]
    simp only [Fin.succ_ne_zero, ite_false, zero_add, Fin.succ_inj, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have : 0 < √(1 + ∑ i : Fin n, (x - xc) i.succ ^ 2) :=
      Real.sqrt_pos.2 (by positivity)
    field_simp
  set S := ∑ i : Fin n, (x - xc) i.succ ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  simp only [hd, div_pow, mul_pow]
  rw [← Finset.sum_div, ← Finset.mul_sum, Real.sq_sqrt (by linarith)]
  rw [div_le_iff₀ (by linarith)]
  nlinarith [sq_nonneg a]

/-- **Finite propagation speed** for `∂₀²u = c Δu` with `0 < c ≤ 1`: a smooth solution on the
tent `{t₀ - 1 ≤ t, t + ⟨y - y_c⟩/2 ≤ C}` that vanishes for `t ≤ t₀` vanishes inside the tent. -/
theorem eq_zero_of_flat_tent (hc : 0 < c) (hc1 : c ≤ 1) {u : E n → ℝ} (hu : ContDiff ℝ ∞ u)
    {t₀ C : ℝ} (xc : E n)
    (hflat : ∀ x, t₀ - 1 ≤ x 0 → tentTime (1 / 2) xc x ≤ C →
      d2 u x 0 0 = ∑ i : Fin n, ∑ j : Fin n, (if i = j then c else 0) * d2 u x i.succ j.succ)
    (hpast : ∀ x, x 0 ≤ t₀ → u x = 0) {x : E n} (hx : tentTime (1 / 2) xc x < C) : u x = 0 := by
  by_cases hx0 : x 0 ≤ t₀
  · exact hpast x hx0
  push Not at hx0
  have hL := isLorentzian_lapseDiag (n := n) hc
  have htemp : ∀ φ : E n → ℝ, (∀ y, d φ y 0 = 1) → (∀ y, ∑ i : Fin n, d φ y i.succ ^ 2 < 1) →
      ∀ y ∈ univ, IsFutureTimelike (fun _ => lapseDiag (n := n) c)
        (fun _ => EuclideanSpace.single 0 1) y (-grad (fun _ => lapseDiag c) φ y) :=
    fun φ h0 hs y _ => isFutureTimelike_lapseDiag hc hc1 (h0 y) (hs y)
  have hsmooth : ContDiff ℝ ∞ (tentTime (n := n) (1 / 2) xc) := by
    show ContDiff ℝ ∞ fun x => tentTime (n := n) (1 / 2) xc x
    simp only [tentTime_def]
    refine (contDiff_coordinate 0).add (contDiff_const.mul (ContDiff.sqrt (by fun_prop)
      fun y => ?_))
    have : 0 ≤ ∑ i : Fin n, (y - xc) i.succ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    linarith
  refine eq_zero_of_bottom (W := univ) (g := fun _ => lapseDiag c)
    (Y := fun _ => EuclideanSpace.single 0 1) (φ₁ := fun y => y 0) (φ₂ := tentTime (1 / 2) xc)
    (t₀ := t₀ - 1) (c := C) isOpen_univ (fun _ _ => contDiffOn_const) (fun _ _ => hL)
    continuousOn_const (fun _ _ => by simp [form_lapseDiag, hc])
    (contDiff_coordinate 0).contDiffOn hsmooth.contDiffOn
    (htemp _ (fun y => by rw [d_coord]; simp) (fun y => by simp [d_coord, Fin.succ_ne_zero]))
    (htemp _ (fun y => d_tentTime_zero _ _ _) (fun y => (sum_d_tentTime_sq_le _ _ _).trans_lt
      (by norm_num)))
    (by simpa using isCompact_tent (by norm_num : (0 : ℝ) < 1 / 2) xc (t₀ - 1) C)
    (U := univ) isOpen_univ (subset_univ _) (hu.of_le (by simp)).contDiffOn
    (fun y _ hy1 hy2 => ?_) (fun y _ _ hy => ?_) x (mem_univ x) (by linarith) hx
  · rw [box_eq_iff (G := fun _ => lapseDiag c) (fun _ _ => differentiableAt_const _)
      hL.det_neg.ne (HasZeroShift.lapseDiag c) (by simp [lapseDiag_def, hc.ne'])
      (hu.contDiffAt.of_le (by simp)), hflat y hy1 hy2]
    simp only [normalA_of_eq_lapseDiag (G := fun _ => lapseDiag (n := n) c) hc.ne' rfl,
      normalB_eq_zero (G := fun _ => lapseDiag (n := n) c) (z := y)
        (Eventually.of_forall fun _ => rfl),
      lapseSq_of_eq_lapseDiag (G := fun _ => lapseDiag (n := n) c) (z := y) rfl, zero_mul,
      Finset.sum_const_zero, mul_zero, add_zero]
  · have hev : u =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [(isOpen_lt (contDiff_coordinate 0).continuous continuous_const).mem_nhds
        (show y 0 < t₀ by simp only at hy; linarith)] with w hw
      exact hpast w (le_of_lt hw)
    exact ⟨hev.self_of_nhds, by rw [hev.fderiv_eq]; simp⟩

end Tent

/-! ### Cutting the periodic solution to the cell -/

section Cut

open PDE

variable {p : ℕ} {A : Fin n → Fin n → (Fin p → ℝ) → E n → ℝ}
  {B : Fin (n + 1) → (Fin p → ℝ) → E n → ℝ} {S : (Fin p → ℝ) → E n → ℝ} {c : (Fin p → ℝ) → ℝ}
  {R₀ t₀ L : ℝ}

/-- Up to time `T`, the lifted periodic solution vanishes within distance `1` of the cell faces
`|yᵢ| = L/2`, if `L/2 > R₀ + 2(T - t₀ + 2)`: tents of slope `1/2` reaching below `t₀` around such
points stay in the flat region. -/
theorem IsFlatNormalForm.liftZ_eq_zero_of_near (h : IsFlatNormalForm A B S c R₀ t₀)
    {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ (Fin 1)} (hV : IsPeriodicSmooth V)
    (hV0 : ∀ l t y, t ≤ t₀ → V l t y = 0)
    (heq : ∀ l t y, dt (dt V) l t y = (periodCoeffs A B L).apply V l t y + periodSource S L l t y)
    {T : ℝ} (hL0 : 0 < L) (hLT : 2 * (R₀ + 2 * (T - t₀ + 2)) < L) (l : Fin p → ℝ) {z : E n}
    (hzT : z 0 < T) {i : Fin n} (hzi : abs (L / 2 - |z i.succ|) < 1) : liftZ L V l z = 0 := by
  set ci : ℝ := if 0 ≤ z i.succ then L / 2 else -(L / 2)
  have hci : |ci| = L / 2 := by
    simp only [ci]
    split_ifs <;> simp only [abs_neg, abs_of_pos (half_pos hL0)]
  have hzci : |z i.succ - ci| < 1 := by
    simp only [ci]
    split_ifs with hz
    · rw [abs_of_nonneg hz] at hzi
      rw [abs_sub_comm]
      exact hzi
    · push Not at hz
      rw [abs_of_neg hz] at hzi
      rw [show z i.succ - -(L / 2) = L / 2 - -z i.succ by ring]
      exact hzi
  set xc : E n := z + (ci - z i.succ) • EuclideanSpace.single i.succ 1
  have hxc : ∀ j : Fin n, (z - xc) j.succ = if j = i then z i.succ - ci else 0 := by
    intro j
    simp only [xc, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply,
      Fin.succ_inj, smul_eq_mul]
    split_ifs <;> simp_all
  have hxci : xc i.succ = ci := by simp [xc]
  have hu := contDiff_liftZ hV.smooth L
  have hsl : ContDiff ℝ ∞ (liftZ L V l) := hu.comp (contDiff_const.prodMk contDiff_id)
  refine eq_zero_of_flat_tent (h.c_pos l) (h.c_le_one l) hsl (t₀ := t₀) (C := T + 1) xc
    (fun x hx1 hx2 => ?_) (fun x hx => by simp [liftZ, hV0 l _ _ hx]) ?_
  · have hfar : R₀ < ‖spatial (zCell L x)‖ := by
      have hsq : |x i.succ - ci| ≤ 2 * (T - t₀ + 2) := by
        have h1 : |(x - xc) i.succ| ≤ √(1 + ∑ j : Fin n, (x - xc) j.succ ^ 2) := by
          refine Real.abs_le_sqrt ?_
          have := Finset.single_le_sum (f := fun j : Fin n => (x - xc) j.succ ^ 2)
            (fun j _ => sq_nonneg _) (Finset.mem_univ i)
          linarith
        simp only [tentTime_def] at hx2
        rw [PiLp.sub_apply, hxci] at h1
        linarith
      have := le_abs_cellPoint_succ hL0 x i hci
      have h2 := abs_apply_succ_le_norm_spatial (zCell L x) i
      simp only [zCell] at h2 ⊢
      linarith
    rw [liftZ_eq_of_periodic hV.smooth heq hL0 l x]
    simp only [h.far_A l _ hfar, h.far_B l _ hfar, h.far_S l _ hfar, zero_mul,
      Finset.sum_const_zero, add_zero]
  · simp only [tentTime_def, hxc]
    simp only [ite_pow, Finset.sum_ite_eq', Finset.mem_univ, ite_true, zero_pow two_ne_zero,
      ]
    have hsq : (z i.succ - ci) ^ 2 < 1 := by
      have := sq_abs (z i.succ - ci)
      nlinarith [abs_nonneg (z i.succ - ci)]
    have : √(1 + (z i.succ - ci) ^ 2) < 2 := by
      rw [Real.sqrt_lt' (by norm_num)]
      linarith
    linarith

/-- The lifted periodic solution, cut off outside the open cell `|yᵢ| < L/2`. -/
def cutZ (L : ℝ) (u : (Fin p → ℝ) → E n → ℝ) (l : Fin p → ℝ) (z : E n) : ℝ :=
  if ∀ i : Fin n, |z i.succ| < L / 2 then u l z else 0

/-- **Local-in-time solutions.** Under `IsFlatNormalForm`, for every `T` the normal form has a
solution on `{t < T}` that is smooth in `(l, z)` there and vanishes for `t ≤ t₀`. -/
theorem IsFlatNormalForm.exists_local_solution (h : IsFlatNormalForm A B S c R₀ t₀) (T : ℝ) :
    ∃ v : (Fin p → ℝ) → E n → ℝ,
      (∀ l z, z 0 < T → ContDiffAt ℝ ∞ (fun q : (Fin p → ℝ) × E n => v q.1 q.2) (l, z)) ∧
      (∀ l z, z 0 ≤ t₀ → v l z = 0) ∧
      ∀ l z, z 0 < T → d2 (v l) z 0 0 = ∑ i, ∑ j, A i j l z * d2 (v l) z i.succ j.succ +
        ∑ k, B k l z * d (v l) z k + S l z := by
  set L : ℝ := 2 * (|R₀| + 2 * |T - t₀| + 5)
  have hL0 : 0 < L := by positivity
  have hLT : 2 * (R₀ + 2 * (T - t₀ + 2)) < L := by
    simp only [L]
    linarith [le_abs_self R₀, le_abs_self (T - t₀)]
  have hLR : 2 * R₀ < L := by
    simp only [L]
    linarith [le_abs_self R₀, abs_nonneg (T - t₀)]
  obtain ⟨V, hV, hV0, heq⟩ := h.exists_periodized hL0 hLR
  set u := liftZ L V
  have hu := contDiff_liftZ hV.smooth L
  have hu0 : ∀ l z, z 0 ≤ t₀ → u l z = 0 := fun l z hz => by simp [u, liftZ, hV0 l _ _ hz]
  have hcases : ∀ l z, z 0 < T →
      ((∀ i : Fin n, |z i.succ| < L / 2) ∧
        ∀ᶠ q : (Fin p → ℝ) × E n in 𝓝 (l, z), cutZ L u q.1 q.2 = u q.1 q.2) ∨
      (R₀ < ‖spatial z‖ ∧ ∀ᶠ q : (Fin p → ℝ) × E n in 𝓝 (l, z), cutZ L u q.1 q.2 = 0) := by
    intro l z hzT
    have hci : ∀ i : Fin n, Continuous fun q : (Fin p → ℝ) × E n => q.2 i.succ := fun i =>
      (contDiff_coordinate i.succ).continuous.comp continuous_snd
    by_cases hin : ∀ i : Fin n, |z i.succ| < L / 2
    · refine Or.inl ⟨hin, ?_⟩
      have hev : ∀ᶠ q : (Fin p → ℝ) × E n in 𝓝 (l, z), ∀ i : Fin n, |q.2 i.succ| < L / 2 :=
        eventually_all.2 fun i => ((hci i).abs.continuousAt).eventually (gt_mem_nhds (hin i))
      filter_upwards [hev] with q hq
      simp [cutZ, hq]
    · push Not at hin
      obtain ⟨i, hi⟩ := hin
      refine Or.inr ⟨by linarith [abs_apply_succ_le_norm_spatial z i], ?_⟩
      have hT : ∀ᶠ q : (Fin p → ℝ) × E n in 𝓝 (l, z), q.2 0 < T :=
        ((contDiff_coordinate 0).continuous.comp continuous_snd).continuousAt.eventually
          (gt_mem_nhds hzT)
      by_cases hnear : |z i.succ| < L / 2 + 1
      · have hev : ∀ᶠ q : (Fin p → ℝ) × E n in 𝓝 (l, z), abs (L / 2 - |q.2 i.succ|) < 1 := by
          refine (((continuous_const.sub (hci i).abs).abs).continuousAt).eventually
            (gt_mem_nhds ?_)
          show abs (L / 2 - |z i.succ|) < 1
          rw [abs_sub_comm, abs_of_nonneg (by linarith)]
          linarith
        filter_upwards [hev, hT] with q hq hqT
        have := h.liftZ_eq_zero_of_near hV hV0 heq hL0 hLT q.1 hqT hq
        simp [cutZ, u, this]
      · push Not at hnear
        have hev : ∀ᶠ q : (Fin p → ℝ) × E n in 𝓝 (l, z), L / 2 < |q.2 i.succ| :=
          ((hci i).abs.continuousAt).eventually (lt_mem_nhds (by linarith))
        filter_upwards [hev] with q hq
        simp only [cutZ, ite_eq_right_iff]
        exact fun hall => absurd (hall i) (not_lt.2 hq.le)
  refine ⟨cutZ L u, fun l z hzT => ?_, fun l z hz => ?_, fun l z hzT => ?_⟩
  · rcases hcases l z hzT with ⟨-, hev⟩ | ⟨-, hev⟩
    · exact hu.contDiffAt.congr_of_eventuallyEq hev
    · exact contDiffAt_const.congr_of_eventuallyEq hev
  · simp [cutZ, hu0 l z hz]
  · have hsl : Tendsto (fun w : E n => (l, w)) (𝓝 z) (𝓝 (l, z)) :=
      (continuous_const.prodMk continuous_id).tendsto z
    rcases hcases l z hzT with ⟨hin, hev⟩ | ⟨hfar, hev⟩
    · have hev' : cutZ L u l =ᶠ[𝓝 z] u l := hsl.eventually hev
      simp only [d2_congr hev', d_congr hev']
      rw [liftZ_eq_of_periodic hV.smooth heq hL0 l z, zCell, cellPoint_of_mem_cell hL0 hin]
    · have hev' : cutZ L u l =ᶠ[𝓝 z] fun _ => 0 := hsl.eventually hev
      have hd : ∀ x j, d (fun _ : E n => (0 : ℝ)) x j = 0 := fun x j => d_const 0 x j
      have hd2 : ∀ i j, d2 (fun _ : E n => (0 : ℝ)) z i j = 0 := fun i j => by
        simp [d2_def, hd]
      simp only [d2_congr hev', d_congr hev', hd, hd2, h.far_B l z hfar, h.far_S l z hfar,
        mul_zero, Finset.sum_const_zero, add_zero]

end Cut

end

end LorentzianCalderon
