module

public import LorentzianCalderon.Facts.Vocabulary

public section

/-!
# The bilinear form

Algebra of `form A v w = Σ Aᵢⱼ vⁱ wʲ`: bilinearity, symmetry for symmetric `A`, and the
expression as a dot product. For Lorentzian `A`, a nonzero causal vector is not orthogonal to a
timelike one (`IsLorentzian.form_ne_zero`), and future-directed timelike and causal vectors have
negative product (`IsFutureTimelike.form_neg`).
-/

namespace LorentzianCalderon

noncomputable section
open scoped Matrix

variable {n : ℕ}

section Form

variable (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (u v w : E n) (c : ℝ)

@[simp]
lemma form_smul_left : form A (c • v) w = c * form A v w := by
  simp only [form_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [PiLp.smul_apply, smul_eq_mul]
  ring

@[simp]
lemma form_smul_right : form A v (c • w) = c * form A v w := by
  simp only [form_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [PiLp.smul_apply, smul_eq_mul]
  ring

@[simp]
lemma form_neg_left : form A (-v) w = -form A v w := by
  simpa using form_smul_left A v w (-1)

@[simp]
lemma form_neg_right : form A v (-w) = -form A v w := by
  simpa using form_smul_right A v w (-1)

@[simp]
lemma form_zero_left : form A 0 w = 0 := by
  simpa using form_smul_left A 0 w 0

@[simp]
lemma form_zero_right : form A v 0 = 0 := by
  simpa using form_smul_right A v 0 0

lemma form_add_left : form A (u + v) w = form A u w + form A v w := by
  simp only [form_def, PiLp.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma form_add_right : form A u (v + w) = form A u v + form A u w := by
  simp only [form_def, PiLp.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma form_sub_left : form A (u - v) w = form A u w - form A v w := by
  rw [sub_eq_add_neg, form_add_left, form_neg_left, sub_eq_add_neg]

lemma form_sub_right : form A u (v - w) = form A u v - form A u w := by
  rw [sub_eq_add_neg, form_add_right, form_neg_right, sub_eq_add_neg]

lemma form_eq_dotProduct : form A v w = v.ofLp ⬝ᵥ (A *ᵥ w.ofLp) := by
  simp only [form_def, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

end Form

lemma form_comm {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hA : Aᵀ = A) (v w : E n) :
    form A v w = form A w v := by
  simp only [form_def]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have := congr_fun (congr_fun hA i) j
  rw [Matrix.transpose_apply] at this
  rw [this]
  ring

/-! ### Lorentzian scalar products -/

/-- A nonzero causal vector and a timelike vector are not orthogonal. -/
theorem IsLorentzian.form_ne_zero {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : IsLorentzian A) {v N : E n} (hv : form A v v ≤ 0) (hv0 : v ≠ 0)
    (hN : form A N N < 0) : form A v N ≠ 0 := by
  intro hsymm
  have h0 : form A N v = 0 := by rw [form_comm hA.symm]; exact hsymm
  have hq : ∀ a b : ℝ, form A (a • N + b • v) (a • N + b • v) =
      a ^ 2 * form A N N + b ^ 2 * form A v v := by
    intro a b
    simp only [form_add_left, form_add_right, form_smul_left, form_smul_right, h0, hsymm]
    ring
  by_cases hli : LinearIndependent ℝ ![N, v]
  · obtain ⟨V, hV⟩ := hA.spacelike
    set U := Submodule.span ℝ (Set.range ![N, v])
    have hU : Module.finrank ℝ U = 2 := by simpa using finrank_span_eq_card hli
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq U V
    have h2 := Submodule.finrank_le (U ⊔ V)
    rw [finrank_euclideanSpace_fin] at h2
    rw [hU, hV.finrank_eq] at h1
    have hne : U ⊓ V ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at h1
      omega
    obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 (Submodule.mem_inf.1 hz).1
    have hpos := hV.pos z (Submodule.mem_inf.1 hz).2 hz0
    rw [← hc, Fin.sum_univ_two] at hpos
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hpos
    rw [hq] at hpos
    nlinarith [sq_nonneg (c 0), sq_nonneg (c 1)]
  · rw [LinearIndependent.pair_iff] at hli
    push Not at hli
    obtain ⟨s, t, hst, hne⟩ := hli
    have hN0 : N ≠ 0 := by
      rintro rfl
      simp at hN
    by_cases ht : t = 0
    · subst ht
      have hs : s ≠ 0 := fun hs => hne hs rfl
      simp only [zero_smul, add_zero, smul_eq_zero, hs, false_or] at hst
      exact hN0 hst
    · have htv : t • v = -(s • N) := eq_neg_of_add_eq_zero_right hst
      have hv' : v = (-(s / t)) • N := by
        calc v = t⁻¹ • (t • v) := (inv_smul_smul₀ ht v).symm
          _ = (-(s / t)) • N := by rw [htv, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
      rw [hv', form_smul_right] at h0
      rcases mul_eq_zero.1 h0 with h | h
      · have : s = 0 := by
          rw [neg_eq_zero, div_eq_zero_iff] at h
          exact h.resolve_right ht
        rw [this, zero_smul, zero_add, smul_eq_zero] at hst
        exact hv0 (hst.resolve_left ht)
      · linarith

/-- **Reverse sign lemma.** A future-directed timelike and a future-directed causal vector have
negative scalar product. -/
theorem IsFutureTimelike.form_neg {g : MatrixField n} {Y : E n → E n} {x N v : E n}
    (hL : IsLorentzian (g x)) (hY : form (g x) (Y x) (Y x) < 0) (hN : IsFutureTimelike g Y x N)
    (hv : IsFutureCausal g Y x v) : form (g x) N v < 0 := by
  set a := form (g x) N v
  set b := form (g x) (Y x) v
  have hb : b < 0 := by
    simp only [b]
    rw [form_comm hL.symm _ _]
    exact hv.future
  have ha : a ≠ 0 := fun h => hL.form_ne_zero hv.causal hv.ne_zero hN.timelike
    ((form_comm hL.symm v N).trans h)
  by_contra hcon
  have ha' : 0 < a := lt_of_le_of_ne (not_lt.1 hcon) (Ne.symm ha)
  set t := a / (a - b)
  have hab : 0 < a - b := by linarith
  have ht0 : 0 < t := div_pos ha' hab
  have ht1 : t < 1 := (div_lt_one hab).2 (by linarith)
  set M := (1 - t) • N + t • Y x
  have hNY : form (g x) N (Y x) < 0 := hN.future
  have hYN : form (g x) (Y x) N = form (g x) N (Y x) := form_comm hL.symm _ _
  have hM : form (g x) M M < 0 := by
    simp only [M, form_add_left, form_add_right, form_smul_left, form_smul_right, hYN]
    have h1 : 0 < 1 - t := by linarith
    nlinarith [mul_pos h1 h1, mul_pos ht0 ht0, mul_pos h1 ht0, hN.timelike]
  have hMv : form (g x) M v = 0 := by
    simp only [M, form_add_left, form_smul_left]
    change (1 - a / (a - b)) * a + a / (a - b) * b = 0
    field_simp
    ring
  exact hL.form_ne_zero hv.causal hv.ne_zero hM ((form_comm hL.symm v M).trans hMv)

theorem continuous_form {g : MatrixField n} {Y : E n → E n} (hg : IsSpacetime g Y) :
    Continuous fun q : E n × E n × E n => form (g q.1) q.2.1 q.2.2 := by
  simp only [form_def]
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  have hij : Continuous fun q : E n × E n × E n => g q.1 i j :=
    (hg.smooth i j).continuous.comp continuous_fst
  have h1 : Continuous fun q : E n × E n × E n => q.2.1 i :=
    (EuclideanSpace.proj i : E n →L[ℝ] ℝ).continuous.comp (continuous_fst.comp continuous_snd)
  have h2 : Continuous fun q : E n × E n × E n => q.2.2 j :=
    (EuclideanSpace.proj j : E n →L[ℝ] ℝ).continuous.comp (continuous_snd.comp continuous_snd)
  exact (h1.mul hij).mul h2

end

end LorentzianCalderon
