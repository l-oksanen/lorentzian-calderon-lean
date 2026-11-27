module

public import LorentzianCalderon.Local.Differential
public import LorentzianCalderon.Local.MatrixCalculus

public section

/-!
# The Piola identity

The columns of the adjugate of a Jacobian matrix are divergence free:
`∑ⱼ ∂ⱼ (adj DΨ)ʲₐ = 0`.
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Matrix Finset

variable {n : ℕ} {Ψ : E n → E n} {x : E n}

theorem contDiffAt_D {m : ℕ∞ω} (hΨ : ContDiffAt ℝ (m + 1) Ψ x) (i j : Fin (n + 1)) :
    ContDiffAt ℝ m (fun y => D Ψ y i j) x := by
  simp only [D_def]
  exact contDiffAt_coord (Ψ := fun y => fderiv ℝ Ψ y (EuclideanSpace.single j 1))
    ((hΨ.fderiv_right le_rfl).clm_apply contDiffAt_const) i

theorem differentiableAt_D (hΨ : ContDiffAt ℝ 2 Ψ x) (i j : Fin (n + 1)) :
    DifferentiableAt ℝ (fun y => D Ψ y i j) x :=
  (contDiffAt_D (m := 1) hΨ i j).differentiableAt one_ne_zero

/-- The derivatives of the Jacobian matrix are the second derivatives of the components. -/
theorem d_D (hΨ : ContDiffAt ℝ 2 Ψ x) (i j k : Fin (n + 1)) :
    d (fun y => D Ψ y i j) x k = d2 (fun y => Ψ y i) x k j := by
  rw [d2_def]
  refine congrFun (d_congr ?_) k
  filter_upwards [hΨ.eventually (by simp)] with y hy
  exact (d_coord_comp (hy.differentiableAt (by simp)) i j).symm

theorem d_D_comm (hΨ : ContDiffAt ℝ 2 Ψ x) (i j k : Fin (n + 1)) :
    d (fun y => D Ψ y i j) x k = d (fun y => D Ψ y i k) x j := by
  rw [d_D hΨ, d_D hΨ, d2_comm (contDiffAt_coord hΨ i)]

theorem sum_sum_eq_zero_of_antisymm {ι : Type*} [Fintype ι] (T : ι → ι → ℝ)
    (hT : ∀ j l, T j l = -T l j) : ∑ j, ∑ l, T j l = 0 := by
  have h : ∑ j, ∑ l, T j l = -∑ j, ∑ l, T j l := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => hT j l
  linarith

/-- The Piola identity: `∑ⱼ ∂ⱼ (adj DΨ)ʲₐ = 0`. -/
theorem sum_d_adjugate_D (hΨ : ContDiffAt ℝ 2 Ψ x) (a : Fin (n + 1)) :
    ∑ j, d (fun y => (D Ψ y).adjugate j a) x j = 0 := by
  have hD := differentiableAt_D hΨ
  let T : Fin (n + 1) → Fin (n + 1) → ℝ := fun j l =>
    (((D Ψ x).updateCol j (Pi.single a 1)).updateCol l
      fun k => if l = j then 0 else d (fun y => D Ψ y k l) x j).det
  have step : ∀ j, d (fun y => (D Ψ y).adjugate j a) x j = ∑ l, T j l := by
    intro j
    simp_rw [adjugate_apply_eq_det_updateCol]
    have hA : ∀ k l, DifferentiableAt ℝ
        (fun y => ((D Ψ y).updateCol j (Pi.single a 1)) k l) x := by
      intro k l
      simp only [updateCol_apply]
      split_ifs
      · exact differentiableAt_const _
      · exact hD k l
    rw [d_def, fderiv_det_apply hA]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [T]
    congr 2
    ext k
    by_cases hl : l = j
    · simp [hl]
    · simp only [updateCol_apply, hl, ite_false, d_def]
  rw [Finset.sum_congr rfl fun j _ => step j]
  refine sum_sum_eq_zero_of_antisymm T fun j l => ?_
  by_cases hjl : j = l
  · subst hjl
    have : T j j = 0 :=
      det_eq_zero_of_column_eq_zero j fun i => by simp
    rw [this, neg_zero]
  · simp only [T, Ne.symm hjl, hjl, ite_false]
    rw [det_updateCol_updateCol_swap _ hjl]
    congr 3
    ext k
    exact d_D_comm hΨ k l j

end

end LorentzianCalderon
