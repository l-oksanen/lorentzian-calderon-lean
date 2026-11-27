module

public import LorentzianCalderon.Causal.Basic

public section

/-!
# Exterior points escape

With `R = √n`, the compact set
`W = {(t, x) : |x| ≤ R, -T - 2 (R - |x|) ≤ t ≤ T} ⊇ M₀` and its complement `O`. If `g` is the
Minkowski metric outside `M₀`, with `∂ₜ` future-directed there, every point of `O` is the initial
point of a future-inextendible timelike ray contained in `O` (blueprint, Lemma "Exterior points
escape").
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology InnerProductSpace
open Set Filter

variable {n : ℕ}

/-! ### Time and space -/

/-- The spatial part `(x 1, …, x n)` of a point of `ℝ^{1+n}`. -/
def spatial : E n →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 fun i => x i.succ
      map_add' := fun x y => by ext i; simp
      map_smul' := fun c x => by ext i; simp }

@[simp]
lemma spatial_apply (x : E n) (i : Fin n) : spatial x i = x i.succ := by rfl

/-- The point with time `t` and spatial part `u`. -/
def spacetimePoint (t : ℝ) (u : EuclideanSpace ℝ (Fin n)) : E n :=
  WithLp.toLp 2 (Fin.cons t fun i => u i)

@[simp]
lemma spacetimePoint_zero (t : ℝ) (u : EuclideanSpace ℝ (Fin n)) : spacetimePoint t u 0 = t :=
  by rfl

@[simp]
lemma spatial_spacetimePoint (t : ℝ) (u : EuclideanSpace ℝ (Fin n)) :
    spatial (spacetimePoint t u) = u := by
  ext i
  simp [spacetimePoint]

@[simp]
lemma single_zero_apply_zero : (EuclideanSpace.single 0 1 : E n) 0 = 1 := by
  simp

@[simp]
lemma spatial_single_zero : spatial (EuclideanSpace.single 0 1 : E n) = 0 := by
  ext i
  simp [Fin.succ_ne_zero]

lemma norm_sq_eq_time_sq_add (x : E n) : ‖x‖ ^ 2 = x 0 ^ 2 + ‖spatial x‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by positivity), Fin.sum_univ_succ]
  simp

lemma form_minkowski (v w : E n) :
    form (minkowski n) v w = -(v 0 * w 0) + ⟪spatial v, spatial w⟫_ℝ := by
  simp [form_def, minkowski_def, Matrix.diagonal_apply, Fin.sum_univ_succ, PiLp.inner_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma form_minkowski_self (v : E n) :
    form (minkowski n) v v = -(v 0 ^ 2) + ‖spatial v‖ ^ 2 := by
  rw [form_minkowski, real_inner_self_eq_norm_sq]
  ring

lemma form_minkowski_single_zero (w : E n) :
    form (minkowski n) (EuclideanSpace.single 0 1) w = -w 0 := by
  simp [form_minkowski]

/-- A future-pointing (positive time component) causal vector and a future-pointing timelike
vector have negative Minkowski product. -/
lemma form_minkowski_neg {v w : E n} (hv : form (minkowski n) v v ≤ 0) (hv0 : 0 < v 0)
    (hw : form (minkowski n) w w < 0) (hw0 : 0 < w 0) : form (minkowski n) v w < 0 := by
  rw [form_minkowski_self] at hv hw
  rw [form_minkowski]
  have hi := real_inner_le_norm (spatial v) (spatial w)
  have ha := norm_nonneg (spatial v)
  have hb := norm_nonneg (spatial w)
  have hav : ‖spatial v‖ ≤ v 0 := by nlinarith
  have hbw : ‖spatial w‖ < w 0 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hav hb, mul_lt_mul_of_pos_left hbw hv0]

lemma eq_zero_of_form_minkowski_self_nonpos {v : E n} (hv : form (minkowski n) v v ≤ 0)
    (hv0 : v 0 = 0) : v = 0 := by
  rw [form_minkowski_self, hv0] at hv
  have h := norm_sq_eq_time_sq_add v
  rw [hv0] at h
  have : ‖v‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖spatial v‖]
  simpa using this

lemma ne_zero_time_of_form_minkowski {a : E n} (ha : form (minkowski n) a a ≤ 0) (ha0 : a ≠ 0) :
    a 0 ≠ 0 :=
  fun h => ha0 (eq_zero_of_form_minkowski_self_nonpos ha h)

/-! ### Exterior of `M₀` -/

section Exterior

variable {T : ℝ} {g : MatrixField n} {Y : E n → E n} {x v : E n}

/-- At a point where `g` is Minkowskian and `∂ₜ` is future-directed, the future-directed timelike
vectors are the Minkowski-timelike vectors with positive time component. -/
lemma isFutureTimelike_iff_of_minkowski (hgx : g x = minkowski n)
    (hY : form (g x) (Y x) (Y x) < 0)
    (hfut : form (g x) (EuclideanSpace.single 0 1) (Y x) < 0) :
    IsFutureTimelike g Y x v ↔ form (minkowski n) v v < 0 ∧ 0 < v 0 := by
  rw [show IsFutureTimelike g Y x v ↔ form (g x) v v < 0 ∧ form (g x) v (Y x) < 0 from
    ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩]
  rw [hgx] at hY hfut ⊢
  rw [form_minkowski_single_zero] at hfut
  have hY0 : 0 < Y x 0 := by linarith
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rcases lt_trichotomy (v 0) 0 with h | h | h
    · have := form_minkowski_neg (v := -v) (by simpa using h1.le) (by simpa using h) hY hY0
      simp at this
      linarith
    · exact absurd (eq_zero_of_form_minkowski_self_nonpos h1.le h) (by
        rintro rfl
        simp at h1)
    · exact h
  · rintro ⟨h1, h2⟩
    exact ⟨h1, form_minkowski_neg h1.le h2 hY hY0⟩

/-- At a point where `g` is Minkowskian and `∂ₜ` is future-directed, the future-directed causal
vectors are the nonzero Minkowski-causal vectors with positive time component. -/
lemma isFutureCausal_iff_of_minkowski (hgx : g x = minkowski n)
    (hY : form (g x) (Y x) (Y x) < 0)
    (hfut : form (g x) (EuclideanSpace.single 0 1) (Y x) < 0) :
    IsFutureCausal g Y x v ↔ form (minkowski n) v v ≤ 0 ∧ 0 < v 0 := by
  rw [show IsFutureCausal g Y x v ↔ v ≠ 0 ∧ form (g x) v v ≤ 0 ∧ form (g x) v (Y x) < 0 from
    ⟨fun h => ⟨h.1, h.2, h.3⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩]
  rw [hgx] at hY hfut ⊢
  rw [form_minkowski_single_zero] at hfut
  have hY0 : 0 < Y x 0 := by linarith
  constructor
  · rintro ⟨h0, h1, h2⟩
    refine ⟨h1, ?_⟩
    rcases lt_trichotomy (v 0) 0 with h | h | h
    · have := form_minkowski_neg (v := -v) (by simpa using h1) (by simpa using h) hY hY0
      simp at this
      linarith
    · exact absurd (eq_zero_of_form_minkowski_self_nonpos h1 h) h0
    · exact h
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1, form_minkowski_neg h1 h2 hY hY0⟩
    rintro rfl
    simp at h2

end Exterior

/-! ### The sets `W` and `O` -/

/-- `W = {(t, x) : |x| ≤ R, -T - 2 (R - |x|) ≤ t ≤ T}` with `R = √n`. -/
def W (n : ℕ) (T : ℝ) : Set (E n) :=
  { x | ‖spatial x‖ ≤ √n ∧ -T - 2 * (√n - ‖spatial x‖) ≤ x 0 ∧ x 0 ≤ T }

theorem mem_W {n : ℕ} {T : ℝ} {x} :
    x ∈ W n T ↔ ‖spatial x‖ ≤ √n ∧ -T - 2 * (√n - ‖spatial x‖) ≤ x 0 ∧ x 0 ≤ T := Iff.rfl

/-- The complement `O` of `W`. -/
def O (n : ℕ) (T : ℝ) : Set (E n) := (W n T)ᶜ

theorem mem_O {n : ℕ} {T : ℝ} {x : E n} : x ∈ O n T ↔ x ∉ W n T := Iff.rfl

variable {T : ℝ}

lemma isClosed_W : IsClosed (W n T) := by
  have h0 : Continuous fun x : E n => x 0 := by fun_prop
  have hs : Continuous fun x : E n => ‖spatial x‖ := spatial.continuous.norm
  exact (isClosed_le hs continuous_const).inter
    ((isClosed_le (by fun_prop) h0).inter (isClosed_le h0 continuous_const))

lemma isOpen_O : IsOpen (O n T) := isClosed_W.isOpen_compl

lemma isCompact_W : IsCompact (W n T) := by
  refine Metric.isCompact_of_isClosed_isBounded isClosed_W
    ((Metric.isBounded_closedBall (x := 0) (r := |T| + 3 * √n)).subset fun x hx => ?_)
  obtain ⟨h1, h2, h3⟩ := hx
  rw [Metric.mem_closedBall, dist_zero_right]
  have hsq := norm_sq_eq_time_sq_add x
  have hn := Real.sqrt_nonneg n
  have hsn := norm_nonneg (spatial x)
  have hx0 : |x 0| ≤ |T| + 2 * √n := by
    rw [abs_le]
    constructor <;> cases abs_cases T <;> linarith
  have hxn := norm_nonneg x
  nlinarith [sq_abs (x 0), abs_nonneg (x 0)]

lemma norm_spatial_le_of_mem_M0 {x : E n} (hx : x ∈ M0 n T) : ‖spatial x‖ ≤ √n := by
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i, ‖spatial x i‖ ^ 2 ≤ ∑ _i : Fin n, (1 : ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        simpa [sq_le_one_iff_abs_le_one] using (mem_M0.1 hx).2 i
    _ = n := by simp

lemma M0_subset_W : M0 n T ⊆ W n T := by
  intro x hx
  have h := norm_spatial_le_of_mem_M0 hx
  have ht := abs_le.1 (mem_M0.1 hx).1
  exact ⟨h, by linarith, ht.2⟩

lemma not_mem_M0_of_mem_O {x : E n} (hx : x ∈ O n T) : x ∉ M0 n T :=
  fun h => hx (M0_subset_W h)

/-! ### Escape -/

/-- A straight ray with positive time component of the velocity is inextendible. -/
lemma isInextendibleRay_line {P : E n → E n → Prop} {x v : E n} (hv : 0 < v 0)
    (hP : ∀ s : ℝ, 0 ≤ s → P (x + s • v) v) : IsInextendibleRay P (fun s => x + s • v) := by
  refine ⟨fun a ha => isPathOn_line ha fun t ht => hP t ht.1, fun p hp => ?_⟩
  have h0 : Continuous fun x : E n => x 0 := by fun_prop
  have hlim := (h0.tendsto p).comp hp
  have htop : Tendsto (fun s : ℝ => x 0 + s * v 0) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_id.atTop_mul_const hv)
  exact not_tendsto_nhds_of_tendsto_atTop htop _ (by simpa [Function.comp_def] using hlim)

/-- A straight ray with nonzero velocity leaves every compact set. -/
lemma tendsto_cocompact_line {x v : E n} (hv : v ≠ 0) :
    Tendsto (fun s : ℝ => x + s • v) atTop (cocompact (E n)) := by
  rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
  have hv' : 0 < ‖v‖ := norm_pos_iff.2 hv
  refine tendsto_atTop_mono' _ ?_
    (tendsto_atTop_add_const_right _ (-‖x‖) (tendsto_id.atTop_mul_const hv'))
  filter_upwards [eventually_ge_atTop 0] with s hs
  have h := norm_sub_le (x + s • v) x
  rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs] at h
  simp only [id]
  linarith

lemma exists_unit_smul_eq (hn : 0 < n) (u : EuclideanSpace ℝ (Fin n)) :
    ∃ e : EuclideanSpace ℝ (Fin n), ‖e‖ = 1 ∧ u = ‖u‖ • e := by
  by_cases hu : u = 0
  · exact ⟨EuclideanSpace.single ⟨0, hn⟩ 1, by simp, by simp [hu]⟩
  · refine ⟨‖u‖⁻¹ • u, norm_smul_inv_norm hu, ?_⟩
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hu), one_smul]

/-- Every point of `O` moves inside `O` along a straight line with Minkowski-timelike velocity
of time component `1`. -/
theorem exists_escape_direction (hn : 0 < n) {x : E n} (hx : x ∈ O n T) :
    ∃ v : E n, v 0 = 1 ∧ form (minkowski n) v v < 0 ∧ ∀ s : ℝ, 0 ≤ s → x + s • v ∈ O n T := by
  by_cases h : √n < ‖spatial x‖ ∨ T < x 0
  · refine ⟨EuclideanSpace.single 0 1, by simp, by simp [form_minkowski_self],
      fun s hs hW => ?_⟩
    obtain ⟨h1, -, h3⟩ := hW
    simp only [map_add, map_smul, spatial_single_zero, smul_zero, add_zero, PiLp.add_apply,
      PiLp.smul_apply, single_zero_apply_zero, smul_eq_mul, mul_one] at h1 h3
    rcases h with h | h <;> linarith
  · push Not at h
    have hx' : x 0 < -T - 2 * (√n - ‖spatial x‖) := by
      by_contra hc
      exact hx ⟨h.1, not_lt.1 hc, h.2⟩
    obtain ⟨e, he, hxe⟩ := exists_unit_smul_eq hn (spatial x)
    refine ⟨spacetimePoint 1 ((1 / 2 : ℝ) • e), rfl, ?_, fun s hs hW => ?_⟩
    · rw [form_minkowski_self]
      simp [norm_smul, he]
      norm_num
    · have hsp : spatial (x + s • spacetimePoint 1 ((1 / 2 : ℝ) • e)) =
          (‖spatial x‖ + s / 2) • e := by
        rw [map_add, map_smul, spatial_spacetimePoint, smul_smul, add_smul, ← hxe]
        ring_nf
      have hnorm : ‖spatial (x + s • spacetimePoint 1 ((1 / 2 : ℝ) • e))‖ =
          ‖spatial x‖ + s / 2 := by
        rw [hsp, norm_smul, he, mul_one, Real.norm_of_nonneg (by positivity)]
      obtain ⟨h1, h2, -⟩ := hW
      rw [hnorm] at h1 h2
      simp only [PiLp.add_apply, PiLp.smul_apply, spacetimePoint_zero, smul_eq_mul,
        mul_one] at h2
      linarith

/-- **Exterior points escape.** If `g` is the Minkowski metric outside `M₀` and `∂ₜ` is
future-directed there, every point of `O` is the initial point of a future-inextendible timelike
ray contained in `O` and leaving every compact set. -/
theorem exists_isInextendibleRay_subset_O (hn : 0 < n) {g : MatrixField n} {Y : E n → E n}
    (hY : IsTimeOrientation g Y) (hg : ∀ x ∉ M0 n T, g x = minkowski n)
    (hfut : ∀ x ∉ M0 n T, form (g x) (EuclideanSpace.single 0 1) (Y x) < 0)
    {x : E n} (hx : x ∈ O n T) :
    ∃ c : ℝ → E n, c 0 = x ∧ IsInextendibleRay (IsFutureTimelike g Y) c ∧
      (∀ t : ℝ, 0 ≤ t → c t ∈ O n T) ∧ Tendsto c atTop (cocompact (E n)) := by
  obtain ⟨v, hv0, hvv, hO⟩ := exists_escape_direction hn hx
  have hv : v ≠ 0 := fun h => by simp [h] at hv0
  refine ⟨fun s => x + s • v, by simp, isInextendibleRay_line (by rw [hv0]; exact one_pos)
    fun s hs => ?_, hO, tendsto_cocompact_line hv⟩
  have hM := not_mem_M0_of_mem_O (hO s hs)
  exact (isFutureTimelike_iff_of_minkowski (hg _ hM) (hY.timelike _) (hfut _ hM)).2
    ⟨hvv, by rw [hv0]; exact one_pos⟩

end

end LorentzianCalderon
