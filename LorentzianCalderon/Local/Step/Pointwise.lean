module

public import LorentzianCalderon.Local.Step.Lens

public section

/-!
# The local continuation step: pointwise identities

At a point `x ∈ V` and a level `s ∈ J`, for a label `a`:
* `box_wb`: `□_g w̄_{a,s} = (φ_a - s) A_{a,s} - κ (φ'_a ∘ Ψ - s) A'_{a,s} ∘ Ψ
  + ḡ^{αβ} (∂_α∂_β u'_{a,s}) ∘ Ψ + θ̄^k (∂_k u'_{a,s}) ∘ Ψ` (Steps 1 and 2 on `D_{a,s}`);
* `transport_wb`: the identity behind Steps 1 and 2 on `Γ_{a,s}`, expressing
  `u_{a,s} (θ̄^k (∂_k φ'_a) ∘ Ψ - □_g φ̄_a)` by `Z_a w̄_{a,s}`, `w̄_{a,s}`, `ḡ`, `dφ̄_a` and the
  conormal coefficients;
* `gb_null`: `ḡ(dφ'_a, dφ'_a) ∘ Ψ = g(dφ_a - dφ̄_a, dφ_a - dφ̄_a)` (Step 3).
-/

namespace LorentzianCalderon

noncomputable section
open Set Matrix Filter
open scoped ContDiff Topology

variable {n : ℕ} {ι : Type*}

section Coform

variable (g : MatrixField n) (x : E n)

theorem coform_sub_left (ξ ξ' η : Fin (n + 1) → ℝ) :
    coform g x (ξ - ξ') η = coform g x ξ η - coform g x ξ' η := by
  simp only [coform_def, Pi.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]

theorem coform_sub_right (ξ η η' : Fin (n + 1) → ℝ) :
    coform g x ξ (η - η') = coform g x ξ η - coform g x ξ η' := by
  simp only [coform_def, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem coform_symm {g : MatrixField n} {x : E n} (hL : IsLorentzian (g x))
    (ξ η : Fin (n + 1) → ℝ) : coform g x ξ η = coform g x η ξ := by
  rw [coform_eq_bil, coform_eq_bil, bil_symm hL.inv_symm]

end Coform

namespace StepData

variable {S : StepData n ι} (hS : S.Hyp)
include hS

theorem Hyp.contDiffOn_u (a : ι) {s : ℝ} (hs : s ∈ S.J) : ContDiffOn ℝ ∞ (S.u a s) S.V :=
  contDiffOn_slice (hS.smooth_u a) hs

theorem Hyp.contDiffOn_u' (a : ι) {s : ℝ} (hs : s ∈ S.J) : ContDiffOn ℝ ∞ (S.u' a s) S.V' :=
  contDiffOn_slice (hS.smooth_u' a) hs

theorem Hyp.contDiffOn_u'Ψ_slice (a : ι) {s : ℝ} (hs : s ∈ S.J) :
    ContDiffOn ℝ ∞ (fun y => S.u' a s (S.Ψ y)) S.V :=
  (hS.contDiffOn_u' a hs).comp hS.smooth_Ψ hS.mapsTo_Ψ

theorem Hyp.contDiffAt_of_V {f : E n → ℝ} (hf : ContDiffOn ℝ ∞ f S.V) {x : E n}
    (hx : x ∈ S.V) : ContDiffAt ℝ ∞ f x := hf.contDiffAt (hS.isOpen_V.mem_nhds hx)

theorem Hyp.contDiffAt_of_V' {f : E n → ℝ} (hf : ContDiffOn ℝ ∞ f S.V') {z : E n}
    (hz : z ∈ S.V') : ContDiffAt ℝ ∞ f z := hf.contDiffAt (hS.isOpen_V'.mem_nhds hz)

theorem Hyp.box_sub {u v : E n → ℝ} (hu : ContDiffOn ℝ ∞ u S.V) (hv : ContDiffOn ℝ ∞ v S.V)
    {x : E n} (hx : x ∈ S.V) : box S.g (fun y => u y - v y) x = box S.g u x - box S.g v x :=
  box_sub_of_contDiffOn hS.smooth_g hS.det_ne_zero hS.isOpen_V hu hv hx

theorem Hyp.d_sub {u v : E n → ℝ} (hu : ContDiffOn ℝ ∞ u S.V) (hv : ContDiffOn ℝ ∞ v S.V)
    {x : E n} (hx : x ∈ S.V) : d (fun y => u y - v y) x = d u x - d v x := by
  ext k
  simp only [d_def, Pi.sub_apply]
  rw [fderiv_fun_sub ((hS.contDiffAt_of_V hu hx).differentiableAt (by simp))
    ((hS.contDiffAt_of_V hv hx).differentiableAt (by simp))]
  rfl

theorem Hyp.box_comparison_at {v : E n → ℝ} (hv : ContDiffOn ℝ ∞ v S.V') {x : E n}
    (hx : x ∈ S.V) :
    -box S.g (fun y => v (S.Ψ y)) x + S.κ x * box S.g' v (S.Ψ x) =
      ∑ α, ∑ β, S.gb x α β * d2 v (S.Ψ x) α β + ∑ k, S.θb x k * d v (S.Ψ x) k := by
  simp only [gb_def, θb_def]
  exact box_comparison (fun i j => ((hS.smooth_g i j).differentiable (by simp)) x)
      (hS.det_ne_zero x) (fun i j => ((hS.smooth_g' i j).differentiable (by simp)) _)
      (hS.det_ne_zero' _) ((hS.smooth_Ψ.contDiffAt (hS.isOpen_V.mem_nhds hx)).of_le (by simp))
      ((hS.contDiffAt_of_V' hv (hS.mapsTo_Ψ hx)).of_le (by simp)) S.κ

theorem Hyp.cometric_comparison_at {v₁ v₂ : E n → ℝ} (hv₁ : ContDiffOn ℝ ∞ v₁ S.V')
    (hv₂ : ContDiffOn ℝ ∞ v₂ S.V') {x : E n} (hx : x ∈ S.V) :
    coform S.g x (d (fun y => v₁ (S.Ψ y)) x) (d (fun y => v₂ (S.Ψ y)) x) -
        S.κ x * coform S.g' (S.Ψ x) (d v₁ (S.Ψ x)) (d v₂ (S.Ψ x)) =
      ∑ α, ∑ β, S.gb x α β * d v₁ (S.Ψ x) α * d v₂ (S.Ψ x) β := by
  simp only [gb_def, coform_def]
  exact cometric_comparison (hS.differentiableAt_Ψ hx)
      ((hS.contDiffAt_of_V' hv₁ (hS.mapsTo_Ψ hx)).differentiableAt (by simp))
      ((hS.contDiffAt_of_V' hv₂ (hS.mapsTo_Ψ hx)).differentiableAt (by simp)) S.κ

/-- `□_g w̄_{a,s}` in terms of the comparison coefficients. -/
theorem box_wb (a : ι) {s : ℝ} (hs : s ∈ S.J) {x : E n} (hx : x ∈ S.V) :
    box S.g (S.wb a s) x = (S.φ a x - s) * S.A a s x -
      S.κ x * ((S.φ' a (S.Ψ x) - s) * S.A' a s (S.Ψ x)) +
      (∑ α, ∑ β, S.gb x α β * d2 (S.u' a s) (S.Ψ x) α β +
        ∑ k, S.θb x k * d (S.u' a s) (S.Ψ x) k) := by
  have h1 : box S.g (S.wb a s) x = box S.g (S.u a s) x - box S.g (fun y => S.u' a s (S.Ψ y)) x := by
    simpa only [wb_eq] using
      hS.box_sub (hS.contDiffOn_u a hs) (hS.contDiffOn_u'Ψ_slice a hs) hx
  have h2 := hS.box_comparison_at (hS.contDiffOn_u' a hs) hx
  rw [hS.wave' a s hs _ (hS.mapsTo_Ψ hx)] at h2
  rw [h1, hS.wave a s hs x hx]
  linarith

/-- The identity behind Steps 1 and 2 on the front `{φ_a = s}`. -/
theorem transport_wb (a : ι) {s : ℝ} (hs : s ∈ S.J) {x : E n} (hx : x ∈ S.V) :
    S.u a s x * (∑ k, S.θb x k * d (S.φ' a) (S.Ψ x) k - box S.g (S.φb a) x) =
      2 * -coform S.g x (d (S.φ a) x) (d (S.wb a s) x) +
        S.κ x * S.wb a s x * box S.g' (S.φ' a) (S.Ψ x) -
        S.u a s x * ∑ α, ∑ β, S.gb x α β * d2 (S.φ' a) (S.Ψ x) α β -
        2 * ∑ α, ∑ β, S.gb x α β * d (S.φ' a) (S.Ψ x) α * d (S.u' a s) (S.Ψ x) β -
        2 * coform S.g x (d (S.φb a) x) (d (fun y => S.u' a s (S.Ψ y)) x) -
        (S.φ a x - s) * S.B a s x + S.κ x * ((S.φ' a (S.Ψ x) - s) * S.B' a s (S.Ψ x)) := by
  have hφ := (hS.eikonal a).smooth
  have hφ'Ψ := hS.contDiffOn_φ'Ψ a
  have hu := hS.contDiffOn_u a hs
  have hu'Ψ := hS.contDiffOn_u'Ψ_slice a hs
  have hT := hS.transport a s hs x hx
  have hT' := hS.transport' a s hs _ (hS.mapsTo_Ψ hx)
  have hC := hS.cometric_comparison_at (hS.eikonal' a).smooth (hS.contDiffOn_u' a hs) hx
  have hB := hS.box_comparison_at (hS.eikonal' a).smooth hx
  have hbox : box S.g (S.φb a) x = box S.g (S.φ a) x - box S.g (fun y => S.φ' a (S.Ψ y)) x := by
    simpa only [φb_eq] using
      hS.box_sub hφ hφ'Ψ hx
  have hdw : d (S.wb a s) x = d (S.u a s) x - d (fun y => S.u' a s (S.Ψ y)) x := by
    simpa only [wb_eq] using
      hS.d_sub hu hu'Ψ hx
  have hdφ : d (S.φb a) x = d (S.φ a) x - d (fun y => S.φ' a (S.Ψ y)) x := by
    simpa only [φb_eq] using
      hS.d_sub hφ hφ'Ψ hx
  have hc1 : coform S.g x (d (S.φ a) x) (d (S.wb a s) x) =
      coform S.g x (d (S.φ a) x) (d (S.u a s) x) -
        coform S.g x (d (S.φb a) x) (d (fun y => S.u' a s (S.Ψ y)) x) -
        coform S.g x (d (fun y => S.φ' a (S.Ψ y)) x) (d (fun y => S.u' a s (S.Ψ y)) x) := by
    rw [hdw, coform_sub_right, hdφ, coform_sub_left]; ring
  rw [hc1, hbox]
  simp only [StepData.wb_def]
  linear_combination -hT + S.κ x * hT' - 2 * hC - S.u a s x * hB

/-- Step 3: `ḡ(dφ'_a, dφ'_a) ∘ Ψ = g(dφ_a - dφ̄_a, dφ_a - dφ̄_a)`. -/
theorem gb_null (a : ι) {x : E n} (hx : x ∈ S.V) :
    ∑ α, ∑ β, S.gb x α β * d (S.φ' a) (S.Ψ x) α * d (S.φ' a) (S.Ψ x) β =
      coform S.g x (d (S.φ a) x - d (S.φb a) x) (d (S.φ a) x - d (S.φb a) x) := by
  have hC := hS.cometric_comparison_at (hS.eikonal' a).smooth (hS.eikonal' a).smooth hx
  rw [(hS.eikonal' a).null _ (hS.mapsTo_Ψ hx), mul_zero, sub_zero] at hC
  have hdφ : d (S.φb a) x = d (S.φ a) x - d (fun y => S.φ' a (S.Ψ y)) x := by
    simpa only [φb_eq] using
      hS.d_sub (hS.eikonal a).smooth (hS.contDiffOn_φ'Ψ a) hx
  rw [← hC, hdφ, sub_sub_cancel]

end StepData

end

end LorentzianCalderon
