module

public import LorentzianCalderon.Local.BoxCalculus

public section

/-!
# Algebra of the comparison

For a map `Ψ`, a function `κ` and metrics `g`, `g'`, the coefficients
`ḡ^{αβ} = g(dΨ^α, dΨ^β) - κ g'^{αβ} ∘ Ψ` and `θ̄^k = -□_g Ψ^k + κ (□_{g'} x^k) ∘ Ψ`
express `-□_g (v ∘ Ψ) + κ (□_{g'} v) ∘ Ψ` and `g(d(v₁ ∘ Ψ), d(v₂ ∘ Ψ)) - κ g'(dv₁, dv₂) ∘ Ψ`
in terms of the derivatives of `v`, `v₁`, `v₂` at `Ψ x`.
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Finset

variable {n : ℕ}

/-- `ḡ^{αβ} = g(dΨ^α, dΨ^β) - κ g'^{αβ} ∘ Ψ`. -/
def gbar (g g' : MatrixField n) (Ψ : E n → E n) (κ : E n → ℝ) (x : E n)
    (α β : Fin (n + 1)) : ℝ :=
  ∑ j, ∑ k, (g x)⁻¹ j k * d (fun y => Ψ y α) x j * d (fun y => Ψ y β) x k -
    κ x * (g' (Ψ x))⁻¹ α β

theorem gbar_def (g g' : MatrixField n) (Ψ : E n → E n) (κ : E n → ℝ) (x : E n)
    (α β : Fin (n + 1)) :
    gbar g g' Ψ κ x α β =
      ∑ j, ∑ k, (g x)⁻¹ j k * d (fun y => Ψ y α) x j * d (fun y => Ψ y β) x k -
        κ x * (g' (Ψ x))⁻¹ α β := by rfl

/-- `θ̄^k = -□_g Ψ^k + κ (□_{g'} x^k) ∘ Ψ`. -/
def θbar (g g' : MatrixField n) (Ψ : E n → E n) (κ : E n → ℝ) (x : E n)
    (k : Fin (n + 1)) : ℝ :=
  -box g (fun y => Ψ y k) x + κ x * box g' (fun z => z k) (Ψ x)

theorem θbar_def (g g' : MatrixField n) (Ψ : E n → E n) (κ : E n → ℝ) (x : E n) (k : Fin (n + 1)) :
    θbar g g' Ψ κ x k =
      -box g (fun y => Ψ y k) x + κ x * box g' (fun z => z k) (Ψ x) := by rfl

variable {g g' : MatrixField n} {Ψ : E n → E n} {x : E n}

/-- The comparison of the wave operators, equation `eq_alg1` of the blueprint. -/
theorem box_comparison (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hdet : (g x).det ≠ 0) (hg' : ∀ i j, DifferentiableAt ℝ (fun z => g' z i j) (Ψ x))
    (hdet' : (g' (Ψ x)).det ≠ 0) (hΨ : ContDiffAt ℝ 2 Ψ x) {v : E n → ℝ}
    (hv : ContDiffAt ℝ 2 v (Ψ x)) (κ : E n → ℝ) :
    -box g (v ∘ Ψ) x + κ x * box g' v (Ψ x) =
      ∑ α, ∑ β, gbar g g' Ψ κ x α β * d2 v (Ψ x) α β +
        ∑ k, θbar g g' Ψ κ x k * d v (Ψ x) k := by
  rw [box_comp hg hdet hv hΨ, box_eq hg' hdet' hv]
  simp only [gbar, θbar, Finset.mul_sum, sub_mul, add_mul, neg_mul, mul_neg, mul_add,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib, mul_assoc]
  ring

/-- The comparison of the inner products of differentials, equation `eq_alg2` of the
blueprint. -/
theorem cometric_comparison (hΨ : DifferentiableAt ℝ Ψ x) {v₁ v₂ : E n → ℝ}
    (hv₁ : DifferentiableAt ℝ v₁ (Ψ x)) (hv₂ : DifferentiableAt ℝ v₂ (Ψ x)) (κ : E n → ℝ) :
    ∑ j, ∑ k, (g x)⁻¹ j k * d (v₁ ∘ Ψ) x j * d (v₂ ∘ Ψ) x k -
        κ x * ∑ α, ∑ β, (g' (Ψ x))⁻¹ α β * d v₁ (Ψ x) α * d v₂ (Ψ x) β =
      ∑ α, ∑ β, gbar g g' Ψ κ x α β * d v₁ (Ψ x) α * d v₂ (Ψ x) β := by
  have h₁ : ∀ j, d (v₁ ∘ Ψ) x j = ∑ α, d v₁ (Ψ x) α * d (fun y => Ψ y α) x j :=
    d_comp hv₁ hΨ
  have h₂ : ∀ k, d (v₂ ∘ Ψ) x k = ∑ β, d v₂ (Ψ x) β * d (fun y => Ψ y β) x k :=
    d_comp hv₂ hΨ
  have e : ∑ j, ∑ k, (g x)⁻¹ j k * d (v₁ ∘ Ψ) x j * d (v₂ ∘ Ψ) x k =
      ∑ α, ∑ β, (∑ j, ∑ k, (g x)⁻¹ j k * d (fun y => Ψ y α) x j *
        d (fun y => Ψ y β) x k) * d v₁ (Ψ x) α * d v₂ (Ψ x) β := by
    simp only [h₁, h₂, Finset.mul_sum, Finset.sum_mul]
    rw [sum_comm₄]
    refine Finset.sum_comm.trans ?_
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [e]
  simp only [gbar, Finset.mul_sum, sub_mul, Finset.sum_sub_distrib, mul_assoc]

end

end LorentzianCalderon
