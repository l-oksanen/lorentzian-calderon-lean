module

public import LorentzianCalderon.Local.Step.Conformal

public section

/-!
# The local continuation step

Blueprint, Proposition `prop_local_step`, with (L1) in the pointwise form of
`lem_conormal`(b) (see `LorentzianCalderon.Local.Step.Hyp`). Step 6 (the amplitudes) is
`StepData.Ball.amplitude_Vo`; Steps 0–5 are in the files `Local/Step/*.lean`.

The energy inequalities enter through `LorentzianCalderon.Local.Step.EnergyInterface`, which
restates those of `LorentzianCalderon.Local.Energy` for the local step.
-/

namespace LorentzianCalderon

noncomputable section
open Set Matrix Filter MeasureTheory Metric
open scoped ContDiff Topology

variable {n : ℕ} {ι : Type*}

namespace StepData

variable {S : StepData n ι} (hS : S.Hyp)
include hS

namespace Ball

variable {R : ℝ} (hB : S.Ball R)
include hB

/-- Below the top, `□_g w̄_{a,s} = 0` on `{φ_a > s}`. -/
theorem box_wb_eq_zero [Fintype ι] (a : ι) {s : ℝ} (hs : s ∈ S.J) {x : E n}
    (hx : x ∈ S.Vlow R) (hsx : s < S.φ a x) : box S.g (S.wb a s) x = 0 := by
  have hxV := hB.subset (Vo_subset hB (mem_Vlow.1 hx).1)
  obtain ⟨hgb, hθb, hφb⟩ := steps123 hS hB x hx
  have hφ' : S.φ' a (S.Ψ x) = S.φ a x := by
    have := hφb a; simp only [φb_def] at this; linarith
  rw [box_wb hS a hs hxV, hS.wave_zero a s hs x hxV hsx,
    hS.wave_zero' a s hs _ (hS.mapsTo_Ψ hxV) (hφ' ▸ hsx)]
  simp [hgb, hθb]

/-- **Step 6**: `u_{a,s} = u'_{a,s} ∘ Ψ` on `V° ∩ {φ_a ≥ s}`. -/
theorem amplitude_Vo [Fintype ι] (a : ι) {s : ℝ} (hs : s ∈ S.J) {x : E n} (hx : x ∈ S.Vo R)
    (hsx : s ≤ S.φ a x) : S.u a s x = S.u' a s (S.Ψ x) := by
  have hxV := hB.subset (Vo_subset hB hx)
  suffices h : S.wb a s x = 0 by simp only [wb_def] at h; linarith
  rcases lt_trichotomy (S.ψ x) S.τ with hlt | heq | hgt
  swap
  · exact (hS.wb_top a hs hxV heq hsx).1
  swap
  · simp only [wb_def, hS.amplitude_top a s hs x hxV hgt hsx, sub_self]
  have hLV := L_subset_V (S := S) hB
  have hLc := isCompact_L' hS hB
  have hLm := measurableSet_L hS hB
  have hw : ContDiffOn ℝ ∞ (S.wb a s) S.V := by
    rw [wb_eq]
    exact (hS.contDiffOn_u a hs).sub (hS.contDiffOn_u'Ψ_slice a hs)
  obtain ⟨C, σ₀, H⟩ := (setting' hS hB).energy_superlevel (eikonal hS hB a)
  set σ := max σ₀ 1
  have hσ1 : 1 ≤ σ := le_max_right _ _
  have h := H σ (le_max_left _ _) s S.V (S.wb a s) hS.isOpen_V (by rwa [L_def] at hLV)
    (hw.of_le (by simp))
    fun y hy hψ hsy => by
      obtain ⟨h1, h2⟩ := hS.wb_top a hs (hLV (mem_L.2 hy)) hψ hsy
      exact ⟨h1, d_eq_zero_of_fderiv h2⟩
  rw [← L_def] at h
  have hm := measurableSet_L_superlevel hS hB a s
  have hz : ∫ y in S.L R (R / 2) ∩ {y | s < S.φ a y},
      Real.exp (2 * σ * S.ψ y) * box S.g (S.wb a s) y ^ 2 = 0 := by
    refine integral_eq_zero_of_ae ?_
    have hae := ae_restrict_of_ae_restrict_of_subset (inter_subset_left (t := {y | s < S.φ a y}))
      (ae_mem_Vlow hS hB)
    filter_upwards [hae, ae_restrict_mem hm] with y hy hy'
    simp [box_wb_eq_zero hS hB a hs hy hy'.2]
  rw [hz, mul_zero] at h
  have hf : ContinuousOn (fun y => Real.exp (2 * σ * S.ψ y) *
      (‖d (S.wb a s) y‖ ^ 2 + σ ^ 2 * S.wb a s y ^ 2)) S.V :=
    (continuousOn_exp hS σ).mul (((hS.continuousOn_norm_d hw).pow 2).add
      (continuousOn_const.mul (hw.continuousOn.pow 2)))
  have hf0 : ∀ y, 0 ≤ Real.exp (2 * σ * S.ψ y) *
      (‖d (S.wb a s) y‖ ^ 2 + σ ^ 2 * S.wb a s y ^ 2) := fun y => by positivity
  have hI0 : ∫ y in S.L R (R / 2) ∩ {y | s < S.φ a y}, Real.exp (2 * σ * S.ψ y) *
      (‖d (S.wb a s) y‖ ^ 2 + σ ^ 2 * S.wb a s y ^ 2) = 0 := by
    have hnn := setIntegral_nonneg (μ := volume) hm fun y _ => hf0 y
    have : 0 < σ ^ 2 := by positivity
    nlinarith
  have hae := (setIntegral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall hf0)
    (((hf.mono hLV).integrableOn_compact hLc).mono_set inter_subset_left)).1 hI0
  set O := S.Vlow R ∩ (S.V ∩ S.φ a ⁻¹' Ioi s)
  have hOopen : IsOpen O :=
    (isOpen_Vlow hS hB).inter ((hS.continuousOn_φ a).isOpen_inter_preimage hS.isOpen_V isOpen_Ioi)
  have hOsub : O ⊆ S.L R (R / 2) ∩ {y | s < S.φ a y} := fun y hy =>
    ⟨Vlow_subset_L hB hy.1, hy.2.2⟩
  have heq := Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset hOsub hae) hOopen
    (hf.mono fun y hy => hy.2.1) continuousOn_const
  have hO0 : ∀ y ∈ O, S.wb a s y = 0 := fun y hy => by
    have := heq hy
    simp only [Pi.zero_apply] at this
    have h2 := (mul_eq_zero.1 this).resolve_left (Real.exp_pos _).ne'
    have h3 : σ ^ 2 * S.wb a s y ^ 2 = 0 := by
      have := sq_nonneg ‖d (S.wb a s) y‖
      have := mul_nonneg (sq_nonneg σ) (sq_nonneg (S.wb a s y))
      linarith
    have hσ0 : σ ^ 2 ≠ 0 := by positivity
    exact pow_eq_zero_iff two_ne_zero |>.1 ((mul_eq_zero.1 h3).resolve_left hσ0)
  have hxl : x ∈ S.Vlow R := mem_Vlow.2 ⟨hx, hlt⟩
  have hxc : x ∈ closure O := by
    refine closure_mono (fun y (hy : y ∈ {y | y ∈ S.Vlow R ∧ S.φ a x < S.φ a y ∧
        S.φ a x < S.φ a y}) => (⟨hy.1, hB.subset (Vo_subset hB (mem_Vlow.1 hy.1).1),
          (lt_of_le_of_lt hsx hy.2.1 : s < S.φ a y)⟩ : y ∈ O))
      (mem_closure_of_fderiv_pos (v := -grad S.g S.ψ x)
        (hS.differentiableAt_of_contDiffOn (hS.eikonal a).smooth hxV)
        (hS.differentiableAt_of_contDiffOn (hS.eikonal a).smooth hxV)
        (by rw [fderiv_neg_grad]; linarith [hS.coform_φ_ψ_neg a hxV])
        (by rw [fderiv_neg_grad]; linarith [hS.coform_φ_ψ_neg a hxV])
        ((isOpen_Vlow hS hB).mem_nhds hxl))
  exact eq_zero_of_mem_closure (hw.continuousOn.continuousAt (hS.isOpen_V.mem_nhds hxV))
    hO0 hxc

/-- `φ'_a ∘ Ψ = φ_a` on `V°`. -/
theorem phase_Vo [Fintype ι] (a : ι) {x : E n} (hx : x ∈ S.Vo R) :
    S.φ' a (S.Ψ x) = S.φ a x := by
  have hxV := hB.subset (Vo_subset hB hx)
  rcases lt_trichotomy (S.ψ x) S.τ with hlt | heq | hgt
  · have := (steps123 hS hB x (mem_Vlow.2 ⟨hx, hlt⟩)).2.2 a
    simp only [φb_def] at this; linarith
  · have := (hS.φb_top a hxV heq).1
    simp only [φb_def] at this; linarith
  · exact hS.phase_top a x hxV hgt

end Ball

/-- **Local continuation step** (blueprint `prop_local_step`): there is an open neighbourhood
`V° ⊆ V` of `q₀` on which `Ψ` has invertible differential (so, being smooth, is a local
diffeomorphism), `Ψ^* g' = g`, `φ'_a ∘ Ψ = φ_a` and `u_{a,s} = u'_{a,s} ∘ Ψ` on `{φ_a ≥ s}`;
moreover every smooth solution of `□_g w = 0` on `V°` vanishing on `V° ∩ {ψ > τ}` vanishes. -/
theorem prop_local_step [Fintype ι] :
    ∃ Vo : Set (E n), IsOpen Vo ∧ S.q₀ ∈ Vo ∧ Vo ⊆ S.V ∧
      (∀ x ∈ Vo, (D S.Ψ x).det ≠ 0) ∧
      (∀ x ∈ Vo, S.g x = (D S.Ψ x)ᵀ * S.g' (S.Ψ x) * D S.Ψ x) ∧
      (∀ a, ∀ x ∈ Vo, S.φ' a (S.Ψ x) = S.φ a x) ∧
      (∀ a, ∀ s ∈ S.J, ∀ x ∈ Vo, s ≤ S.φ a x → S.u a s x = S.u' a s (S.Ψ x)) ∧
      ∀ w : E n → ℝ, ContDiffOn ℝ ∞ w Vo → (∀ x ∈ Vo, box S.g w x = 0) →
        (∀ x ∈ Vo, S.τ < S.ψ x → w x = 0) → ∀ x ∈ Vo, w x = 0 := by
  obtain ⟨R, hB⟩ := hS.exists_ball
  refine ⟨S.Vo R, Ball.isOpen_Vo hS hB, Ball.mem_Vo hB,
    fun x hx => hB.subset (Ball.Vo_subset hB hx), fun x hx => hB.det x (Ball.Vo_subset hB hx),
    fun x hx => (Ball.pullback_Vo hS hB x hx).2, fun a x hx => Ball.phase_Vo hS hB a hx,
    fun a s hs x hx hsx => Ball.amplitude_Vo hS hB a hs hx hsx,
    fun w hw hbox htop => Ball.unique_continuation hS hB hw hbox htop⟩

end StepData

end

end LorentzianCalderon
