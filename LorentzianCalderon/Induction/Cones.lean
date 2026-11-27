module

public import LorentzianCalderon.Setting.Escape
public import LorentzianCalderon.Geometry.Span

public section

/-!
# Time cones of a Lorentzian scalar product

For a Lorentzian matrix `G`, two causal vectors in the future of the same timelike vector `Y`
have negative product. The proofs write `G = Pᵀ η P`
(`IsLorentzian.exists_eq_transpose_mul_minkowski_mul`) and compare time components in Minkowski
space.
-/

namespace LorentzianCalderon

noncomputable section
open scoped Matrix
open Matrix

variable {n : ℕ}

/-! ### Minkowski space -/

/-- In Minkowski space, a nonzero causal vector `a` and a timelike vector `b` have negative
product exactly when their time components have the same sign. -/
lemma form_minkowski_neg_iff {a b : E n} (ha : form (minkowski n) a a ≤ 0) (ha0 : a ≠ 0)
    (hb : form (minkowski n) b b < 0) :
    form (minkowski n) a b < 0 ↔ 0 < a 0 * b 0 := by
  have ha' := ne_zero_time_of_form_minkowski ha ha0
  have hb' := ne_zero_time_of_form_minkowski hb.le (by rintro rfl; simp at hb)
  have hna : form (minkowski n) (-a) (-a) ≤ 0 := by simpa using ha
  have hnb : form (minkowski n) (-b) (-b) < 0 := by simpa using hb
  rcases ha'.lt_or_gt with h1 | h1 <;> rcases hb'.lt_or_gt with h2 | h2
  · have := form_minkowski_neg hna (by simpa using h1) hnb (by simpa using h2)
    simp only [form_neg_left, form_neg_right, neg_neg] at this
    exact ⟨fun _ => mul_pos_of_neg_of_neg h1 h2, fun _ => this⟩
  · have := form_minkowski_neg hna (by simpa using h1) hb h2
    simp only [form_neg_left] at this
    exact ⟨fun h => by linarith, fun h => by nlinarith⟩
  · have := form_minkowski_neg ha h1 hnb (by simpa using h2)
    simp only [form_neg_right] at this
    exact ⟨fun h => by linarith, fun h => by nlinarith⟩
  · exact ⟨fun _ => mul_pos h1 h2, fun _ => form_minkowski_neg ha h1 hb h2⟩

/-! ### Lorentzian scalar products -/

section Lorentzian

variable {G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}

/-- The vector `P v` for a matrix `P`. -/
private def mapVec (P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (v : E n) : E n :=
  WithLp.toLp 2 (P *ᵥ v.ofLp)

private lemma form_congr_minkowski {P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hP : G = Pᵀ * minkowski n * P) (v w : E n) :
    form G v w = form (minkowski n) (mapVec P v) (mapVec P w) := by
  rw [form_eq_dotProduct, form_eq_dotProduct, hP, mapVec, mapVec, ← mulVec_mulVec,
    ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

private lemma mapVec_ne_zero {P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hP : P.det ≠ 0)
    {v : E n} (hv : v ≠ 0) : mapVec P v ≠ 0 := by
  intro h
  apply hv
  have : P *ᵥ v.ofLp = 0 := by
    have := congrArg WithLp.ofLp h
    simpa [mapVec] using this
  have := eq_zero_of_mulVec_eq_zero hP this
  ext i
  simpa using congrFun this i

private lemma exists_minkowski (hG : IsLorentzian G) :
    ∃ P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ, P.det ≠ 0 ∧ G = Pᵀ * minkowski n * P := by
  obtain ⟨P, hP⟩ := hG.exists_eq_transpose_mul_minkowski_mul
  refine ⟨P, fun h => ?_, hP⟩
  have := hG.det_neg
  rw [hP, det_mul, det_mul, h, mul_zero] at this
  exact lt_irrefl 0 this

/-- Two causal vectors in the future of a timelike vector `Y`, one of them timelike, have
negative product. -/
theorem IsLorentzian.form_neg_of_future (hG : IsLorentzian G) {Y u v : E n}
    (hY : form G Y Y < 0) (hu : form G u u < 0) (huY : form G u Y < 0)
    (hv : form G v v ≤ 0) (hv0 : v ≠ 0) (hvY : form G v Y < 0) : form G u v < 0 := by
  obtain ⟨P, hP0, hP⟩ := exists_minkowski hG
  rw [form_congr_minkowski hP] at hY hu huY hv hvY ⊢
  have hu0 : u ≠ 0 := by rintro rfl; simp [mapVec] at hu
  have h1 := (form_minkowski_neg_iff hu.le (mapVec_ne_zero hP0 hu0) hY).1 huY
  have h2 := (form_minkowski_neg_iff hv (mapVec_ne_zero hP0 hv0) hY).1 hvY
  have h3 : 0 < mapVec P v 0 * mapVec P u 0 := by
    have hY0 : mapVec P Y 0 ≠ 0 :=
      ne_zero_time_of_form_minkowski hY.le (by rintro h; rw [h] at hY; simp at hY)
    have := mul_pos h1 h2
    have hsq : 0 < mapVec P Y 0 ^ 2 := by positivity
    nlinarith
  rw [form_comm (by simp [minkowski_def])]
  exact (form_minkowski_neg_iff hv (mapVec_ne_zero hP0 hv0) hu).2 h3

/-- A nonzero causal vector with negative product with a vector `b` in the future of `Y` is
in the future of `Y`. -/
theorem IsLorentzian.form_neg_of_form_neg (hG : IsLorentzian G) {Y a b : E n}
    (hY : form G Y Y < 0) (ha : form G a a ≤ 0) (ha0 : a ≠ 0) (hb : form G b b < 0)
    (hbY : form G b Y < 0) (hab : form G a b < 0) : form G a Y < 0 := by
  rcases (hG.form_ne_zero ha ha0 hY).lt_or_gt with h | h
  · exact h
  · have := hG.form_neg_of_future hY hb hbY (by simpa using ha) (neg_ne_zero.2 ha0)
      (by simpa using h)
    rw [form_neg_right, form_comm hG.symm] at this
    linarith

end Lorentzian

/-! ### Time-oriented metrics -/

section Field

variable {g : MatrixField n} {Y : E n → E n} {x u v : E n}

/-- The future cone of `Y` is that of any of its future-directed timelike vectors. -/
theorem IsFutureTimelike.of_form_neg (hg : IsLorentzian (g x)) (hY : form (g x) (Y x) (Y x) < 0)
    (hu : IsFutureTimelike g Y x u) (hv : form (g x) v v < 0) (huv : form (g x) v u < 0) :
    IsFutureTimelike g Y x v :=
  ⟨hv, hg.form_neg_of_form_neg hY hv.le (by rintro rfl; simp at hv) hu.timelike hu.future huv⟩

end Field

end

end LorentzianCalderon
