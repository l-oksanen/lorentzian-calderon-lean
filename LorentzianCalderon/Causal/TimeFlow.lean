module

public import LorentzianCalderon.Causal.Steep
public import LorentzianCalderon.ODE.Global
public import LorentzianCalderon.Local.Energy.Coform
public import LorentzianCalderon.Local.MatrixCalculus

public section

/-!
# The flow of a standard time function

For a standard time function `ψ`, the field `N = grad ψ / g(dψ, dψ)` is smooth, future timelike,
with `dψ(N) = 1`, and bounded by `1/κ` for the steepness constant `κ`. So its flow `Φ` is global
and smooth, and moves the level sets of `ψ` into each other: `ψ(Φ_t x) = ψ x + t`. This gives
`Facts.exists_cauchyTemporal`, which was a cited fact, from `Facts.exists_temporal`.
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Topology
open Set Filter

variable {n : ℕ} {g : MatrixField n} {Y : E n → E n} {ψ : E n → ℝ}

theorem contDiffOn_grad {g : MatrixField n} (hg : ∀ i j, ContDiff ℝ ∞ fun x => g x i j)
    (hdet : ∀ x, (g x).det ≠ 0) {T : Set (E n)} (hT : IsOpen T) {φ : E n → ℝ}
    (hφ : ContDiffOn ℝ ∞ φ T) : ContDiffOn ℝ ∞ (grad g φ) T := by
  have : ContDiffOn ℝ ∞ (fun x => fun j => ∑ k, (g x)⁻¹ j k * d φ x k) T :=
    contDiffOn_pi.2 fun j => ContDiffOn.sum fun k _ =>
      (contDiff_inv_apply hg hdet j k).contDiffOn.mul (contDiffOn_d hT hφ k)
  rw [show grad g φ = _ from funext (grad_def g φ)]
  exact (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm.contDiff.comp_contDiffOn this

theorem contDiff_coform_d (hg : ∀ i j, ContDiff ℝ ∞ fun x => g x i j)
    (hdet : ∀ x, (g x).det ≠ 0) {u v : E n → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ fun x => coform g x (d u x) (d v x) := by
  simp only [coform_def]
  exact ContDiff.sum fun j _ => ContDiff.sum fun k _ =>
    ((contDiff_inv_apply hg hdet j k).mul (contDiff_d hu j)).mul (contDiff_d hv k)

/-- The field `N = grad ψ / g(dψ, dψ)`, normalized by `dψ(N) = 1`. -/
def timeField (g : MatrixField n) (ψ : E n → ℝ) (x : E n) : E n :=
  (coform g x (d ψ x) (d ψ x))⁻¹ • grad g ψ x

theorem timeField_def (g : MatrixField n) (ψ : E n → ℝ) (x : E n) :
    timeField g ψ x =
      (coform g x (d ψ x) (d ψ x))⁻¹ • grad g ψ x := by rfl

section Field

variable (hg : IsSpacetime g Y) (hψ : ∀ x, IsFutureTimelike g Y x (-grad g ψ x))
include hg hψ

theorem coform_d_self_neg (x : E n) : coform g x (d ψ x) (d ψ x) < 0 :=
  coform_self_neg_of_future (hg.lorentzian x) (hψ x)

theorem fderiv_timeField (x : E n) : fderiv ℝ ψ x (timeField g ψ x) = 1 := by
  rw [timeField, map_smul, fderiv_eq_form_grad (hg.lorentzian x), smul_eq_mul]
  have h := form_neg_grad (hg.lorentzian x) ψ ψ
  rw [form_neg_left, form_neg_right, neg_neg] at h
  rw [h]
  exact inv_mul_cancel₀ (coform_d_self_neg hg hψ x).ne

theorem isFutureTimelike_timeField (x : E n) : IsFutureTimelike g Y x (timeField g ψ x) := by
  rw [timeField, show ∀ c : ℝ, c⁻¹ • grad g ψ x = (-c⁻¹) • (-grad g ψ x) by
    intro c; rw [smul_neg, neg_smul, neg_neg]]
  exact (hψ x).smul (neg_pos.2 (inv_lt_zero.2 (coform_d_self_neg hg hψ x)))

theorem contDiff_timeField (hψs : ContDiff ℝ ∞ ψ) : ContDiff ℝ ∞ (timeField g ψ) :=
  ((contDiff_coform_d hg.smooth hg.det_ne_zero hψs hψs).inv fun x =>
    (coform_d_self_neg hg hψ x).ne).smul
    (contDiffOn_univ.1 (contDiffOn_grad hg.smooth hg.det_ne_zero isOpen_univ hψs.contDiffOn))

end Field

/-- The flow of `N = grad ψ / g(dψ, dψ)` for a standard time function `ψ`: global, smooth, and
moving the level sets of `ψ` into each other. -/
theorem IsStandardTime.exists_flow (hg : IsSpacetime g Y) (hψ : IsStandardTime g Y ψ) :
    ∃ Φ : ℝ → E n → E n, ContDiff ℝ ∞ (fun p : ℝ × E n => Φ p.1 p.2) ∧
      (∀ x, Φ 0 x = x) ∧
      (∀ t x, HasDerivAt (fun r => Φ r x) ((coform g (Φ t x) (d ψ (Φ t x)) (d ψ (Φ t x)))⁻¹ •
        grad g ψ (Φ t x)) t) ∧
      ∀ t x, ψ (Φ t x) = ψ x + t := by
  obtain ⟨κ, hκ, hsteep⟩ := hψ.exists_steep hg
  set N := timeField g ψ
  have hN : ContDiff ℝ ∞ N := contDiff_timeField hg hψ.past_gradient hψ.smooth
  have hN1 : ContDiff ℝ 1 N := hN.of_le (by simp)
  have hNb : ∀ x, ‖N x‖ ≤ κ⁻¹ := fun x => by
    have := hsteep x _ (isFutureTimelike_timeField hg hψ.past_gradient x).isFutureCausal
    rw [fderiv_timeField hg hψ.past_gradient] at this
    rw [le_inv_comm₀ (norm_pos_iff.2 (isFutureTimelike_timeField hg hψ.past_gradient x).ne_zero)
      hκ, ← one_div, le_div_iff₀ (norm_pos_iff.2
        (isFutureTimelike_timeField hg hψ.past_gradient x).ne_zero)]
    linarith
  have hdom := ODEFlow.dom_eq_univ hN1 hNb
  have hFL := ODEFlow.locallyLipschitzOn_of_contDiffOn isOpen_univ hN1.contDiffOn
  have hΦd := ODEFlow.hasDerivAt_flow hN1 hdom
  refine ⟨fun t x => ODEFlow.flow N univ (t, x), ?_, fun x => ODEFlow.flow_zero hFL (mem_univ x),
    hΦd, fun t x => ?_⟩
  · have := (ODEFlow.contDiffOn_flow isOpen_univ hN.contDiffOn).2
    rw [hdom] at this
    exact contDiffOn_univ.1 this
  have hψd : Differentiable ℝ ψ := hψ.smooth.differentiable (by simp)
  have hder : ∀ r, HasDerivAt (fun r => ψ (ODEFlow.flow N univ (r, x)) - r) 0 r := fun r => by
    have := ((hψd _).hasFDerivAt.comp_hasDerivAt r (hΦd r x)).sub (hasDerivAt_id r)
    rwa [fderiv_timeField hg hψ.past_gradient, sub_self] at this
  have := is_const_of_deriv_eq_zero (fun r => (hder r).differentiableAt)
    (fun r => (hder r).deriv) t 0
  simp only [ODEFlow.flow_zero hFL (mem_univ x), sub_zero] at this
  linarith

/-- A standard time function exists, it is Cauchy, and the flow of `grad ψ / g(dψ, dψ)` is
global, smooth, and moves the level sets of `ψ` into each other. -/
theorem exists_standardTime_flow (hg : IsSpacetime g Y) :
    ∃ (ψ : E n → ℝ) (Φ : ℝ → E n → E n), IsStandardTime g Y ψ ∧ IsCauchyTemporal g Y ψ ∧
      ContDiff ℝ ∞ (fun p : ℝ × E n => Φ p.1 p.2) ∧
      (∀ x, Φ 0 x = x) ∧
      (∀ t x, HasDerivAt (fun r => Φ r x) ((coform g (Φ t x) (d ψ (Φ t x)) (d ψ (Φ t x)))⁻¹ •
        grad g ψ (Φ t x)) t) ∧
      ∀ t x, ψ (Φ t x) = ψ x + t := by
  obtain ⟨ψ, hψ⟩ := exists_standardTime hg
  obtain ⟨Φ, hΦ⟩ := hψ.exists_flow hg
  exact ⟨ψ, Φ, hψ, hψ.isCauchyTemporal hg, hΦ⟩

/-- A Cauchy temporal function exists, and the flow of `N_ψ = grad ψ / g(dψ, dψ)` is complete,
smooth, and moves the level sets of `ψ` into each other. Formerly a fact citing
Bernal–Sánchez, Comm. Math. Phys. 257 (2005), Theorem 1.1; now derived from
`Facts.exists_temporal` through a standard time function (`exists_standardTime_flow`). -/
theorem Facts.exists_cauchyTemporal (hg : IsSpacetime g Y) :
    ∃ (ψ : E n → ℝ) (Φ : ℝ → E n → E n), IsCauchyTemporal g Y ψ ∧
      ContDiff ℝ ∞ (fun p : ℝ × E n => Φ p.1 p.2) ∧
      (∀ x, Φ 0 x = x) ∧
      (∀ t x, HasDerivAt (fun r => Φ r x) ((coform g (Φ t x) (d ψ (Φ t x)) (d ψ (Φ t x)))⁻¹ •
        grad g ψ (Φ t x)) t) ∧
      ∀ t x, ψ (Φ t x) = ψ x + t := by
  obtain ⟨ψ, Φ, -, h⟩ := exists_standardTime_flow hg
  exact ⟨ψ, Φ, h⟩

end

end LorentzianCalderon
