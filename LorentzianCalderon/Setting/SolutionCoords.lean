module

public import LorentzianCalderon.Setting.BoxGreen
public import LorentzianCalderon.Green.Prescribed

public section

/-!
# Solution coordinates

Finitely many solutions of `□_g v = 0` whose differentials span the covectors on a
neighbourhood of a given compact set (blueprint, Lemma `lem_solution_coords`).
-/

namespace LorentzianCalderon

noncomputable section
open Set
open scoped ContDiff Matrix Topology

variable {n : ℕ} {g : MatrixField n} {Y : E n → E n}

theorem fderiv_apply_unitNormal_ne_zero (hg : IsSpacetime g Y) {ψ : E n → ℝ}
    (hψ : IsCauchyTemporal g Y ψ) (x : E n) :
    fderiv ℝ ψ x (unitNormal g ψ x) ≠ 0 := by
  set G := grad g ψ x
  have hG : ∀ j, G j = ∑ k, (g x)⁻¹ j k * d ψ x k := fun j => by simp [G, grad_def]
  have hunit : IsUnit (g x).det := isUnit_iff_ne_zero.2 (hg.lorentzian x).det_neg.ne
  have hgG : ∀ i, ∑ j, g x i j * G j = d ψ x i := by
    intro i
    have := congr_fun (congrArg (fun M => M *ᵥ d ψ x) (Matrix.mul_nonsing_inv (g x) hunit)) i
    simp only [← Matrix.mulVec_mulVec, Matrix.one_mulVec] at this
    simpa [Matrix.mulVec, dotProduct, ← hG] using this
  set s := ∑ i, G i * d ψ x i
  have hform : form (g x) (-G) (-G) = s := by
    simp only [form_def, PiLp.neg_apply, s, ← hgG, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hco : coform g x (d ψ x) (d ψ x) = s := by
    simp only [coform_def, s, hG, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hs : s < 0 := hform ▸ (hψ.past_gradient x).timelike
  have hdψ : fderiv ℝ ψ x G = s := by
    rw [apply_eq_sum_d]
    exact Finset.sum_congr rfl fun i _ => by rw [d_def, mul_comm]
  rw [unitNormal_def, hco, map_smul, map_neg, hdψ, smul_eq_mul]
  have : 0 < √(-s) := Real.sqrt_pos.2 (by linarith)
  exact mul_ne_zero (inv_ne_zero this.ne') (by linarith)

/-- Near every point there are `n + 1` solutions of `□_g v = 0` whose differentials are
linearly independent. -/
theorem exists_local_solution_coords (hg : IsSpacetime g Y) (p : E n) :
    ∃ (v : Fin (n + 1) → E n → ℝ) (U : Set (E n)), (∀ i, ContDiff ℝ ∞ (v i)) ∧
      (∀ i x, box g (v i) x = 0) ∧ IsOpen U ∧ p ∈ U ∧
      ∀ x ∈ U, ∀ w, (∀ i, fderiv ℝ (v i) x w = 0) → w = 0 := by
  choose v hv hbox hvp using fun i : Fin (n + 1) =>
    Facts.exists_solution_fderiv_eq hg p (EuclideanSpace.proj i)
  set M : E n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun x => Matrix.of fun i j => d (v i) x j
  have hM : Continuous fun x => (M x).det :=
    Continuous.matrix_det (continuous_pi fun i => continuous_pi fun j =>
      (contDiff_d (hv i) j).continuous)
  refine ⟨v, {x | (M x).det ≠ 0}, hv, hbox, hM.isOpen_preimage _ isOpen_compl_singleton, ?_,
    fun x hx w hw => ?_⟩
  · have : M p = 1 := by
      ext i j
      simp [M, d_def, hvp, Matrix.one_apply, PiLp.single_apply]
    simp [this]
  · have h : M x *ᵥ (fun j => w j) = 0 := by
      ext i
      rw [Pi.zero_apply, ← hw i, apply_eq_sum_d]
      simp [M, Matrix.mulVec, dotProduct, d_def]
    have := Matrix.eq_zero_of_mulVec_eq_zero hx h
    ext j
    exact congr_fun this j

/-- Finitely many continuous linear functionals whose joint map is injective span the dual
space. -/
theorem span_range_eq_top_of_injective {ι : Type*} [Fintype ι] (ℓ : ι → E n →L[ℝ] ℝ)
    (h : Function.Injective (ContinuousLinearMap.pi ℓ)) :
    Submodule.span ℝ (range ℓ) = ⊤ := by
  classical
  obtain ⟨S, hS⟩ := LinearMap.exists_leftInverse_of_injective
    (ContinuousLinearMap.pi ℓ : E n →ₗ[ℝ] ι → ℝ) (LinearMap.ker_eq_bot.2 h)
  refine Submodule.eq_top_iff'.2 fun ζ => ?_
  have hζ : ζ = ∑ i, ζ (S (Pi.single i 1)) • ℓ i := by
    ext w
    have hw : w = S (fun i => ℓ i w) := (DFunLike.congr_fun hS w).symm
    conv_lhs => rw [hw]
    have : (fun i => ℓ i w) = ∑ i, ℓ i w • (Pi.single i 1 : ι → ℝ) := by
      ext j
      simp [Pi.single_apply]
    rw [this]
    simp [map_sum, mul_comm]
  rw [hζ]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- Solution coordinates (blueprint, Lemma `lem_solution_coords`): finitely many solutions of
`□_g v = 0` that form an immersion `(v₁, …, vₘ)` on an open neighbourhood of a compact set. -/
theorem exists_solution_coords (hg : IsSpacetime g Y) {K : Set (E n)} (hK : IsCompact K) :
    ∃ (m : ℕ) (v : Fin m → E n → ℝ), (∀ i, ContDiff ℝ ∞ (v i)) ∧ (∀ i x, box g (v i) x = 0) ∧
      ∃ N, IsOpen N ∧ K ⊆ N ∧ ∀ x ∈ N, Function.Injective (fderiv ℝ (fun y i => v i y) x) := by
  choose V U hV hbox hU hpU hinj using exists_local_solution_coords hg
  obtain ⟨t, -, hKt⟩ := hK.elim_nhds_subcover U fun p _ => (hU p).mem_nhds (hpU p)
  let e := Fintype.equivFin (t × Fin (n + 1))
  refine ⟨_, fun k => V (e.symm k).1 (e.symm k).2, fun k => hV _ _, fun k => hbox _ _,
    ⋃ p ∈ t, U p, isOpen_biUnion fun p _ => hU p, hKt, fun x hx => ?_⟩
  obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.1 hx
  rw [fderiv_pi fun k => (hV _ _).differentiable (by simp) x, injective_iff_map_eq_zero]
  intro w hw
  refine hinj p x hxp w fun i => ?_
  simpa using congr_fun hw (e (⟨p, hp⟩, i))

/-- Solution coordinates, with the differentials spanning the covectors on `N`. -/
theorem exists_solution_coords_span (hg : IsSpacetime g Y) {K : Set (E n)} (hK : IsCompact K) :
    ∃ (m : ℕ) (v : Fin m → E n → ℝ), (∀ i, ContDiff ℝ ∞ (v i)) ∧ (∀ i x, box g (v i) x = 0) ∧
      ∃ N, IsOpen N ∧ K ⊆ N ∧
        ∀ x ∈ N, Submodule.span ℝ (range fun i => fderiv ℝ (v i) x) = ⊤ := by
  obtain ⟨m, v, hv, hbox, N, hN, hKN, hinj⟩ := exists_solution_coords hg hK
  refine ⟨m, v, hv, hbox, N, hN, hKN, fun x hx => span_range_eq_top_of_injective _ ?_⟩
  rw [← fderiv_pi fun i => (hv i).differentiable (by simp) x]
  exact hinj x hx

end

end LorentzianCalderon
