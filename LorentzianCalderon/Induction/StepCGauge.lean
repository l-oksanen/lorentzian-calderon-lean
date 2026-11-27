module

public import LorentzianCalderon.Induction.Lift
public import LorentzianCalderon.Local.Differential

public section

/-!
# The local gauge

Blueprint, Lemma `lem_ind_local_extension`, Step C2: `n + 1` phases `fᵢ` with linearly independent
differentials on an open set `U` form a map `(fᵢ)ᵢ` with a smooth local inverse near each point
of `U`.
-/

namespace LorentzianCalderon

noncomputable section
open Set Filter Matrix
open scoped ContDiff Topology

variable {n : ℕ}

/-- The components `d f y i = ∂ᵢ f(y)` of the differential of a smooth function are continuous. -/
theorem continuousAt_d {f : E n → ℝ} {U : Set (E n)} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    {z : E n} (hz : z ∈ U) (i : Fin (n + 1)) : ContinuousAt (fun y => d f y i) z := by
  simp only [d_def]
  exact ((hf.continuousOn_fderiv_of_isOpen hU (by simp)).continuousAt (hU.mem_nhds hz)).clm_apply
    continuousAt_const

/-- The map `(fᵢ)ᵢ` of `n + 1` functions. -/
def phaseMap (f : Fin (n + 1) → E n → ℝ) (z : E n) : E n := WithLp.toLp 2 fun i => f i z

theorem phaseMap_def (f : Fin (n + 1) → E n → ℝ) (z : E n) :
    phaseMap f z =
      WithLp.toLp 2 fun i => f i z := by rfl

@[simp]
lemma phaseMap_apply (f : Fin (n + 1) → E n → ℝ) (z : E n) (i : Fin (n + 1)) :
    phaseMap f z i = f i z := by rfl

theorem contDiffOn_phaseMap {f : Fin (n + 1) → E n → ℝ} {U : Set (E n)}
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) U) : ContDiffOn ℝ ∞ (phaseMap f) U :=
  (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm.contDiff.comp_contDiffOn (contDiffOn_pi.2 hf)

theorem fderiv_phaseMap {f : Fin (n + 1) → E n → ℝ} {z : E n}
    (hf : ∀ i, DifferentiableAt ℝ (f i) z) (v : E n) (i : Fin (n + 1)) :
    fderiv ℝ (phaseMap f) z v i = fderiv ℝ (f i) z v := by
  have h : phaseMap f = (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm ∘ fun z i => f i z := by rfl
  rw [h, ContinuousLinearEquiv.comp_fderiv, fderiv_pi hf]
  rfl

/-- **The local gauge**: phases with linearly independent differentials on `U` form a map with a
smooth local inverse near each point of `U`. -/
theorem exists_localInverse_phaseMap {f : Fin (n + 1) → E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hf : ∀ i, ContDiffOn ℝ ∞ (f i) U)
    (hli : ∀ z ∈ U, LinearIndependent ℝ fun i => d (f i) z) {p : E n} (hp : p ∈ U) :
    ∃ h : OpenPartialHomeomorph (E n) (E n), ⇑h = phaseMap f ∧ p ∈ h.source ∧ h.source ⊆ U ∧
      ContDiffOn ℝ ∞ h.symm h.target := by
  have hinj : ∀ z ∈ U, Function.Injective (fderiv ℝ (phaseMap f) z) := by
    intro z hz
    have hd : ∀ i, DifferentiableAt ℝ (f i) z := fun i =>
      ((hf i).contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
    set M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := Matrix.of fun i k => d (f i) z k
    have hM : IsUnit M := linearIndependent_rows_iff_isUnit.1 (hli z hz)
    rw [injective_iff_map_eq_zero]
    intro v hv
    have hMv : M *ᵥ v.ofLp = M *ᵥ 0 := by
      ext i
      have := congr_arg (fun w : E n => w i) hv
      simp only [fderiv_phaseMap hd, PiLp.zero_apply] at this
      rw [fderiv_apply_eq_sum_d] at this
      simp only [mulVec, dotProduct, M, Matrix.of_apply, Pi.zero_apply, mul_zero,
        Finset.sum_const_zero]
      rw [← this]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    have := mulVec_injective_iff_isUnit.2 hM hMv
    ext i
    exact congr_fun this i
  obtain ⟨h, hh, hph, hsub, hsm, -⟩ := exists_localInverse hU (contDiffOn_phaseMap hf) hinj hp
  exact ⟨h, hh, hph, hsub, hsm⟩

end

end LorentzianCalderon
