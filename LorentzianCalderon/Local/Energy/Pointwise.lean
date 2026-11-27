module

public import LorentzianCalderon.Local.Energy.Current
public import LorentzianCalderon.Local.Energy.Compactness

public section

/-!
# The pointwise inequality for the divergence of the current (Step 1)

On the lens `L`, for `σ ≥ σ₀` and the mass term `λ = ε₀² σ²`,
`∂ⱼPʲ ≤ e^{2σψ} (-a σ (|dw|² + σ² w²) + (b / σ) |□w|²)`.
The constants come from compactness of `L`: the coercivity of `T(X, X)`, and bounds for `Xw` and
for the remainder of the divergence identity, all homogeneous of degree two in `(dw, √λ w)`.
-/

namespace LorentzianCalderon

noncomputable section
open Set Matrix
open scoped ContDiff

variable {n : ℕ}

/-- The space of pairs `(ξ, s)` of a covector and a scalar. -/
abbrev Jet (n : ℕ) := (Fin (n + 1) → ℝ) × ℝ

/-- `T(β, β)` for the differential `v.1` and `λ w² = v.2²`. -/
def txxForm (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (β : Fin (n + 1) → ℝ) (v : Jet n) : ℝ :=
  emTensor (bil A) 1 v.2 v.1 β β

theorem txxForm_def (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (β : Fin (n + 1) → ℝ) (v : Jet n) :
    txxForm A β v =
      emTensor (bil A) 1 v.2 v.1 β β := by rfl

/-- The linear form `Σₖ aₖ ξₖ`. -/
def lin (a ξ : Fin (n + 1) → ℝ) : ℝ := ∑ k, a k * ξ k

theorem lin_def (a ξ : Fin (n + 1) → ℝ) :
    lin a ξ =
      ∑ k, a k * ξ k := by rfl

/-- The quadratic form `Σ_{c,e} a_{ce} ξ_c ξ_e`. -/
def quad (a : Fin (n + 1) → Fin (n + 1) → ℝ) (ξ : Fin (n + 1) → ℝ) : ℝ :=
  ∑ c, ∑ e, a c e * ξ c * ξ e

theorem quad_def (a : Fin (n + 1) → Fin (n + 1) → ℝ) (ξ : Fin (n + 1) → ℝ) :
    quad a ξ =
      ∑ c, ∑ e, a c e * ξ c * ξ e := by rfl

theorem lin_smul (a ξ : Fin (n + 1) → ℝ) (t : ℝ) : lin a (t • ξ) = t * lin a ξ := by
  simp only [lin, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem quad_smul (a : Fin (n + 1) → Fin (n + 1) → ℝ) (ξ : Fin (n + 1) → ℝ) (t : ℝ) :
    quad a (t • ξ) = t ^ 2 * quad a ξ := by
  simp only [quad, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => by ring

/-- The remainder of the divergence identity in terms of the values of its coefficients. -/
def remForm (ρ₀ : ℝ) (A : Fin (n + 1) → Fin (n + 1) → ℝ)
    (dX : Fin (n + 1) → Fin (n + 1) → ℝ) (D : ℝ) (X : Fin (n + 1) → ℝ)
    (dG : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → ℝ) (v : Jet n) : ℝ :=
  ∑ j, (ρ₀ * lin (A j) v.1) * lin (fun b => dX b j) v.1 -
    1 / 2 * D * (quad A v.1 + v.2 ^ 2) -
    1 / 2 * ∑ j, (ρ₀ * X j) * quad (fun c e => dG c e j) v.1

theorem remForm_def (ρ₀ : ℝ) (A : Fin (n + 1) → Fin (n + 1) → ℝ)
    (dX : Fin (n + 1) → Fin (n + 1) → ℝ) (D : ℝ) (X : Fin (n + 1) → ℝ)
    (dG : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → ℝ) (v : Jet n) :
    remForm ρ₀ A dX D X dG v =
      ∑ j, (ρ₀ * lin (A j) v.1) * lin (fun b => dX b j) v.1 -
        1 / 2 * D * (quad A v.1 + v.2 ^ 2) -
        1 / 2 * ∑ j, (ρ₀ * X j) * quad (fun c e => dG c e j) v.1 := by rfl

theorem continuous_txxForm :
    Continuous fun q : (Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ × (Fin (n + 1) → ℝ)) × Jet n =>
      txxForm q.1.1 q.1.2 q.2 := by
  simp only [txxForm, emTensor_def, bil, Matrix.toLinearMap₂'_apply, smul_eq_mul]
  fun_prop

theorem continuous_remForm :
    Continuous fun q : (ℝ × (Fin (n + 1) → Fin (n + 1) → ℝ) ×
        (Fin (n + 1) → Fin (n + 1) → ℝ) × ℝ × (Fin (n + 1) → ℝ) ×
        (Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → ℝ)) × Jet n =>
      remForm q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2.1 q.1.2.2.2.2.1 q.1.2.2.2.2.2 q.2 := by
  simp only [remForm, lin, quad]
  fun_prop

theorem txxForm_smul (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (β : Fin (n + 1) → ℝ) (t : ℝ)
    (v : Jet n) : txxForm A β (t • v) = t ^ 2 * txxForm A β v := by
  simp only [txxForm, emTensor_def, Prod.smul_fst, Prod.smul_snd, map_smul, LinearMap.smul_apply,
    smul_eq_mul]
  ring

theorem remForm_smul (ρ₀ : ℝ) (A : Fin (n + 1) → Fin (n + 1) → ℝ)
    (dX : Fin (n + 1) → Fin (n + 1) → ℝ) (D : ℝ) (X : Fin (n + 1) → ℝ)
    (dG : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → ℝ) (t : ℝ) (v : Jet n) :
    remForm ρ₀ A dX D X dG (t • v) = t ^ 2 * remForm ρ₀ A dX D X dG v := by
  simp only [remForm, Prod.smul_fst, Prod.smul_snd, lin_smul, quad_smul, smul_eq_mul]
  have e1 : ∑ j, (ρ₀ * (t * lin (A j) v.1)) * (t * lin (fun b => dX b j) v.1) =
      t ^ 2 * ∑ j, (ρ₀ * lin (A j) v.1) * lin (fun b => dX b j) v.1 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  have e2 : ∑ j, (ρ₀ * X j) * (t ^ 2 * quad (fun c e => dG c e j) v.1) =
      t ^ 2 * ∑ j, (ρ₀ * X j) * quad (fun c e => dG c e j) v.1 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [e1, e2]
  ring

theorem txxForm_pos {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hA : IsLorentzForm (bil A))
    {β : Fin (n + 1) → ℝ} (hβ : bil A β β < 0) {v : Jet n} (hv : v ≠ 0) :
    0 < txxForm A β v := by
  have e : txxForm A β v = emTensor (bil A) 0 0 v.1 β β + -(1 / 2) * bil A β β * v.2 ^ 2 := by
    simp only [txxForm, emTensor_def]; ring
  rw [e]
  rcases eq_or_ne v.1 0 with h1 | h1
  · have h2 : v.2 ≠ 0 := fun h2 => hv (Prod.ext h1 h2)
    rw [h1]
    simp only [emTensor_def, map_zero, zero_mul, mul_zero, sub_zero, zero_add]
    have : 0 < v.2 ^ 2 := by positivity
    nlinarith
  · have := hA.emTensor_self_pos hβ h1
    have : 0 ≤ -(1 / 2) * bil A β β * v.2 ^ 2 := by
      have : 0 ≤ v.2 ^ 2 := sq_nonneg _
      nlinarith
    linarith

theorem norm_jet_sq_le (v : Jet n) : ‖v‖ ^ 2 ≤ ‖v.1‖ ^ 2 + v.2 ^ 2 := by
  rw [Prod.norm_def, Real.norm_eq_abs]
  rcases le_total ‖v.1‖ |v.2| with h | h
  · rw [max_eq_right h, sq_abs]; nlinarith [sq_nonneg ‖v.1‖]
  · rw [max_eq_left h]; nlinarith [sq_nonneg v.2]

theorem norm_jet_sq_ge (v : Jet n) : ‖v.1‖ ^ 2 + v.2 ^ 2 ≤ 2 * ‖v‖ ^ 2 := by
  rw [Prod.norm_def, Real.norm_eq_abs]
  have h1 : ‖v.1‖ ≤ max ‖v.1‖ |v.2| := le_max_left _ _
  have h2 : |v.2| ≤ max ‖v.1‖ |v.2| := le_max_right _ _
  have h3 : v.2 ^ 2 = |v.2| ^ 2 := (sq_abs _).symm
  nlinarith [norm_nonneg v.1, abs_nonneg v.2]

end

end LorentzianCalderon
