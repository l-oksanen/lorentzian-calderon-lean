module

public import LorentzianCalderon.Geometry.FirstArrival
public import LorentzianCalderon.Geometry.Span

public section

/-!
# The induction, Step C1: directions

Blueprint, Lemma `lem_ind_local_extension`, Step C1: from one admissible direction at `p₀`, a
finite family of admissible directions `ζ = g(p₀)⁻¹ ξ` whose covectors `ξ = g(ζ, ·)` contain a
basis and whose outer products `ξ ξᵀ`, together with `g(p₀)`, span the symmetric matrices
(`lem_open_directions` and `lem_span`).
-/

namespace LorentzianCalderon

noncomputable section
open Set Filter Matrix
open scoped Topology

variable {n : ℕ} {g : MatrixField n} {Y : E n → E n}

/-- **Step C1** of `lem_ind_local_extension`: a finite family of admissible directions at `p₀` whose
covectors contain a basis and span the symmetric matrices with `g(p₀)`. -/
theorem IsAdmissibleDirection.exists_finset_span (hg : IsSpacetime g Y) {O : Set (E n)}
    (hO : IsOpen O) {p₀ ζ₀ : E n} (h₀ : IsAdmissibleDirection g Y O p₀ ζ₀) :
    ∃ (s : Finset (Fin (n + 1) → ℝ)) (b : Fin (n + 1) → Fin (n + 1) → ℝ),
      (∀ ξ ∈ s, ξ ≠ 0 ∧ IsAdmissibleDirection g Y O p₀ (WithLp.toLp 2 ((g p₀)⁻¹ *ᵥ ξ))) ∧
      (∀ i, b i ∈ s) ∧ LinearIndependent ℝ b ∧
      ∀ M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ, Mᵀ = M →
        M ∈ Submodule.span ℝ (insert (g p₀) ((fun ξ => vecMulVec ξ ξ) '' (s : Set _))) := by
  set A := g p₀
  have hA : IsLorentzian A := hg.lorentzian p₀
  have hunit : IsUnit A.det := hA.det_neg.ne.isUnit
  have hAinv : ∀ v, A⁻¹ *ᵥ (A *ᵥ v) = v := fun v => by
    rw [mulVec_mulVec, nonsing_inv_mul _ hunit, one_mulVec]
  have hinvA : ∀ v, A *ᵥ (A⁻¹ *ᵥ v) = v := fun v => by
    rw [mulVec_mulVec, mul_nonsing_inv _ hunit, one_mulVec]
  have hev₁ := h₀.eventually hg hO
  have hc : Continuous fun ζ : E n => form A ζ (Y p₀) := by
    simp only [form_def]
    fun_prop
  have hev₂ : ∀ᶠ ζ in 𝓝 ζ₀, form A ζ (Y p₀) < 0 :=
    hc.continuousAt.eventually (gt_mem_nhds (isAdmissibleDirection_iff.1 h₀).1.future)
  obtain ⟨N, hNp, hNo, hζ₀N⟩ := eventually_nhds_iff.1 (hev₁.and hev₂)
  set U : Set (Fin (n + 1) → ℝ) := (fun ξ => WithLp.toLp 2 (A⁻¹ *ᵥ ξ)) ⁻¹' N
  have hUo : IsOpen U := hNo.preimage (by fun_prop)
  have hne : ∃ ξ ∈ U, ξ ≠ 0 ∧ ξ ⬝ᵥ (A⁻¹ *ᵥ ξ) = 0 := by
    refine ⟨A *ᵥ ζ₀.ofLp, ?_, fun h => (isAdmissibleDirection_iff.1 h₀).1.ne_zero ?_, ?_⟩
    · show WithLp.toLp 2 (A⁻¹ *ᵥ (A *ᵥ ζ₀.ofLp)) ∈ N
      rw [hAinv]
      exact hζ₀N
    · have := hAinv ζ₀.ofLp
      rw [h, mulVec_zero] at this
      ext i
      exact (congr_fun this i).symm
    · rw [hAinv, dotProduct_comm, ← form_eq_dotProduct]
      exact (isAdmissibleDirection_iff.1 h₀).2.1
  obtain ⟨s, b, hs, hbs, hb, hspan⟩ := hA.exists_finset_null_span hg.two_le hUo hne
  refine ⟨s, b, fun ξ hξ => ⟨(hs ξ hξ).2.1, ?_⟩, hbs, hb, hspan⟩
  obtain ⟨hξU, hξ0, hξn⟩ := hs ξ hξ
  obtain ⟨hp, hfut⟩ := hNp _ hξU
  have hnull : form A (WithLp.toLp 2 (A⁻¹ *ᵥ ξ)) (WithLp.toLp 2 (A⁻¹ *ᵥ ξ)) = 0 := by
    rw [form_eq_dotProduct]
    rw [hinvA, dotProduct_comm]
    exact hξn
  refine hp ⟨fun h => hξ0 ?_, hnull.le, hfut⟩ hnull
  have := hinvA ξ
  have h' : A⁻¹ *ᵥ ξ = 0 := by
    have := congr_arg WithLp.ofLp h
    simpa using this
  rw [h', mulVec_zero] at this
  exact this.symm

end

end LorentzianCalderon
