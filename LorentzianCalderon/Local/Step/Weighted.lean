module

public import LorentzianCalderon.Local.Step.Bounds
public import LorentzianCalderon.Local.Step.Absorb

public section

/-!
# The local continuation step: weighted integrals on the lens

`N σ f = ∫_L e^{2σψ} f` on the lens `L = L_{R/2}`, its elementary properties for functions
continuous on `V`, and the vanishing on `V° ∩ {ψ < τ}` of a nonnegative continuous function with
`N σ f = 0`. Also the vanishing of `w̄_{a,s}` and `φ̄_a` with their differentials on the top.
-/

namespace LorentzianCalderon

noncomputable section
open Set Matrix Filter MeasureTheory Metric
open scoped ContDiff Topology

variable {n : ℕ} {ι : Type*}

namespace StepData

/-- The weighted integral `∫_L e^{2σψ} f` over the lens `L_{R/2}`. -/
def N (S : StepData n ι) (R σ : ℝ) (f : E n → ℝ) : ℝ :=
  ∫ x in S.L R (R / 2), Real.exp (2 * σ * S.ψ x) * f x

theorem N_def (S : StepData n ι) (R σ : ℝ) (f : E n → ℝ) :
    N S R σ f =
      ∫ x in S.L R (R / 2), Real.exp (2 * σ * S.ψ x) * f x := by rfl

variable {S : StepData n ι} (hS : S.Hyp)
include hS

/-- `w̄_{a,s}` vanishes with its differential on `{ψ = τ} ∩ {φ_a ≥ s}`. -/
theorem Hyp.wb_top (a : ι) {s : ℝ} (hs : s ∈ S.J) {x : E n} (hx : x ∈ S.V) (hψ : S.ψ x = S.τ)
    (hsx : s ≤ S.φ a x) : S.wb a s x = 0 ∧ fderiv ℝ (S.wb a s) x = 0 := by
  set O := S.V ∩ S.ψ ⁻¹' Ioi S.τ ∩ S.φ a ⁻¹' Ioi s
  have hO : IsOpen O := by
    have h1 := hS.smooth_ψ.continuousOn.isOpen_inter_preimage hS.isOpen_V
      (isOpen_Ioi (a := S.τ))
    exact (hS.continuousOn_φ a).mono (inter_subset_left (s := S.V)) |>.isOpen_inter_preimage
      h1 (isOpen_Ioi (a := s))
  have h0 : ∀ y ∈ O, S.wb a s y = 0 := fun y hy => by
    simp only [wb_def, hS.amplitude_top a s hs y hy.1.1 hy.1.2 (le_of_lt hy.2), sub_self]
  have hxc : x ∈ closure O := by
    refine closure_mono (fun y hy => ?_) (hS.mem_closure_top hx (f := S.φ a)
      (hS.differentiableAt_of_contDiffOn (hS.eikonal a).smooth hx) (hS.coform_φ_ψ_neg a hx)
      (hS.isOpen_V.mem_nhds hx))
    exact ⟨⟨hy.1, (hψ ▸ hy.2.1 : S.τ < S.ψ y)⟩, (lt_of_le_of_lt hsx hy.2.2 : s < S.φ a y)⟩
  rw [wb_eq] at h0 ⊢
  exact eq_zero_and_fderiv_of_mem_closure hS.isOpen_V
    ((hS.contDiffOn_u a hs).sub (hS.contDiffOn_u'Ψ_slice a hs) |>.of_le (by simp)) hO h0 hx hxc

/-- `φ̄_a` vanishes with its differential on the top `{ψ = τ}`. -/
theorem Hyp.φb_top (a : ι) {x : E n} (hx : x ∈ S.V) (hψ : S.ψ x = S.τ) :
    S.φb a x = 0 ∧ fderiv ℝ (S.φb a) x = 0 := by
  set O := {y | y ∈ S.V ∧ S.τ < S.ψ y}
  have hO : IsOpen O := hS.smooth_ψ.continuousOn.isOpen_inter_preimage hS.isOpen_V
    (isOpen_Ioi (a := S.τ))
  have h0 : ∀ y ∈ O, S.φb a y = 0 := fun y hy => by
    simp only [φb_def, hS.phase_top a y hy.1 hy.2, sub_self]
  have hxc : x ∈ closure O := by
    refine closure_mono (fun y hy => ?_) (hS.mem_closure_top hx (f := S.ψ)
      (hS.differentiableAt_of_contDiffOn hS.smooth_ψ hx) (hS.coform_ψ_neg hx)
      (hS.isOpen_V.mem_nhds hx))
    exact ⟨hy.1, hψ ▸ hy.2.1⟩
  exact eq_zero_and_fderiv_of_mem_closure hS.isOpen_V ((hS.contDiffOn_φb a).of_le (by simp))
    hO h0 hx hxc

namespace Ball

variable {R : ℝ} (hB : S.Ball R)
include hB

omit hS in
theorem L_subset_V : S.L R (R / 2) ⊆ S.V := fun _ hx => hB.subset (mem_L.1 hx).1

theorem isCompact_L' : IsCompact (S.L R (R / 2)) :=
  isCompact_L hS hB (half_pos hB).le (half_lt hB)

theorem measurableSet_L : MeasurableSet (S.L R (R / 2)) := (isCompact_L' hS hB).measurableSet

omit hS in
theorem q₀_mem_L : S.q₀ ∈ S.L R (R / 2) := by
  refine mem_L.2 ⟨mem_ball_self hB.pos, (by rw [τ_def]), ?_⟩
  simp only [ψt_def, τ_def, sub_self, norm_zero]
  have := half_pos hB
  nlinarith

omit hB in
theorem continuousOn_exp (σ : ℝ) : ContinuousOn (fun x => Real.exp (2 * σ * S.ψ x)) S.V :=
  Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hS.smooth_ψ.continuousOn)

theorem integrableOn {f : E n → ℝ} (hf : ContinuousOn f S.V) (σ : ℝ) :
    IntegrableOn (fun x => Real.exp (2 * σ * S.ψ x) * f x) (S.L R (R / 2)) :=
  (((continuousOn_exp hS σ).mul hf).mono (L_subset_V hB)).integrableOn_compact
    (isCompact_L' hS hB)

theorem N_mono {f h : E n → ℝ} (hf : ContinuousOn f S.V) (hh : ContinuousOn h S.V) (σ : ℝ)
    (hfh : ∀ x ∈ S.L R (R / 2), f x ≤ h x) : S.N R σ f ≤ S.N R σ h :=
  setIntegral_mono_on (integrableOn hS hB hf σ) (integrableOn hS hB hh σ)
    (measurableSet_L hS hB) fun x hx =>
      mul_le_mul_of_nonneg_left (hfh x hx) (Real.exp_pos _).le

theorem N_add {f h : E n → ℝ} (hf : ContinuousOn f S.V) (hh : ContinuousOn h S.V) (σ : ℝ) :
    S.N R σ (fun x => f x + h x) = S.N R σ f + S.N R σ h := by
  simp only [N, mul_add]
  exact integral_add (integrableOn hS hB hf σ) (integrableOn hS hB hh σ)

omit hS hB in
theorem N_const_mul (c σ : ℝ) (f : E n → ℝ) :
    S.N R σ (fun x => c * f x) = c * S.N R σ f := by
  simp only [N]
  rw [← integral_const_mul]
  congr 1; funext x; ring

theorem N_sum {κ : Type*} (s : Finset κ) {f : κ → E n → ℝ}
    (hf : ∀ a, ContinuousOn (f a) S.V) (σ : ℝ) :
    S.N R σ (fun x => ∑ a ∈ s, f a x) = ∑ a ∈ s, S.N R σ (f a) := by
  simp only [N, Finset.mul_sum]
  exact integral_finsetSum _ fun a _ => integrableOn hS hB (hf a) σ

theorem N_nonneg {f : E n → ℝ} (σ : ℝ) (hf : ∀ x ∈ S.L R (R / 2), 0 ≤ f x) :
    0 ≤ S.N R σ f :=
  setIntegral_nonneg (measurableSet_L hS hB) fun x hx =>
    mul_nonneg (Real.exp_pos _).le (hf x hx)

theorem N_eq_zero {f : E n → ℝ} (σ : ℝ) (hf : ∀ x ∈ S.L R (R / 2), f x = 0) :
    S.N R σ f = 0 := by
  simp only [N]
  rw [setIntegral_congr_fun (measurableSet_L hS hB) (g := fun _ => 0) fun x hx => by
    simp [hf x hx]]
  simp

/-- A nonnegative continuous function with `N σ f = 0` vanishes on `V° ∩ {ψ < τ}`. -/
theorem eq_zero_of_N_eq_zero {f : E n → ℝ} (hf : ContinuousOn f S.V) (σ : ℝ)
    (hf0 : ∀ x ∈ S.L R (R / 2), 0 ≤ f x) (hN : S.N R σ f = 0) : ∀ x ∈ S.Vlow R, f x = 0 := by
  have hae := (setIntegral_eq_zero_iff_of_nonneg_ae
    ((ae_restrict_iff' (measurableSet_L hS hB)).2 (Eventually.of_forall fun x hx =>
      mul_nonneg (Real.exp_pos _).le (hf0 x hx))) (integrableOn hS hB hf σ)).1 hN
  have hVL := Vlow_subset_L hB
  have hae' := ae_restrict_of_ae_restrict_of_subset hVL hae
  have hcont : ContinuousOn (fun x => Real.exp (2 * σ * S.ψ x) * f x) (S.Vlow R) :=
    ((continuousOn_exp hS σ).mul hf).mono (hVL.trans (L_subset_V hB))
  have heq := Measure.eqOn_open_of_ae_eq hae' (isOpen_Vlow hS hB) hcont continuousOn_const
  intro x hx
  have := heq hx
  simp only [Pi.zero_apply] at this
  exact (mul_eq_zero.1 this).resolve_left (Real.exp_pos _).ne'

end Ball

end StepData

end

end LorentzianCalderon
