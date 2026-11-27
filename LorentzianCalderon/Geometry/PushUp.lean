module

public import LorentzianCalderon.Geometry.LocalCausality

public section

/-!
# Push-up

Push-up (O'Neill, Corollary 14.1): `p ≤ q ≪ r` or `p ≪ q ≤ r` implies `p ≪ r`, from local
push-up in totally normal sets along a causal curve.
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Set Filter

variable {n : ℕ} {g : MatrixField n} {Y : E n → E n}

/-- Push-up along a causal curve: `γ(1) ≪ z` implies `γ(0) ≪ z`. -/
theorem IsPathOn.chronLT_of_chronLT (hg : IsSpacetime g Y) {γ : ℝ → E n}
    (hγ : IsPathOn (IsFutureCausal g Y) 0 1 γ) {z : E n} (hz : ChronLT g Y (γ 1) z) :
    ChronLT g Y (γ 0) z := by
  set S := {t ∈ Icc (0 : ℝ) 1 | ChronLT g Y (γ t) z}
  have hS1 : (1 : ℝ) ∈ S := ⟨⟨zero_le_one, le_rfl⟩, hz⟩
  have hSb : BddBelow S := ⟨0, fun t ht => ht.1.1⟩
  set t₀ := sInf S
  have ht₀ : t₀ ∈ Icc (0 : ℝ) 1 := ⟨le_csInf ⟨1, hS1⟩ fun t ht => ht.1.1, csInf_le hSb hS1⟩
  obtain ⟨W, ρ, L, hW0, hW⟩ := exists_isTotallyNormal hg (γ t₀)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hW.isOpen _ hW0
  obtain ⟨η, hη, hηc⟩ := Metric.continuousWithinAt_iff.1 (hγ.continuousOn t₀ ht₀) ε hε
  have hγW : ∀ t ∈ Icc (0 : ℝ) 1, |t - t₀| < η → γ t ∈ W := fun t ht h =>
    hball (hηc ht (by rwa [Real.dist_eq]))
  obtain ⟨t', ht'S, ht'⟩ := exists_lt_of_csInf_lt ⟨1, hS1⟩ (lt_add_of_pos_right t₀ hη)
  have ht₀t' : t₀ ≤ t' := csInf_le hSb ht'S
  set α := max 0 (t₀ - η / 2)
  have hα : α ∈ S := by
    have hαt' : α ≤ t' := max_le ht'S.1.1 (by linarith)
    rcases hαt'.lt_or_eq with hlt | heq
    · refine ⟨⟨le_max_left _ _, hαt'.trans ht'S.1.2⟩, ?_⟩
      refine hW.chronLT_of_isPathOn_of_chronLT hg
        (hγ.restrict (le_max_left _ _) hlt ht'S.1.2) (fun t ht => hγW t
          ⟨(le_max_left _ _).trans ht.1, ht.2.trans ht'S.1.2⟩ ?_) ht'S.2
      rw [abs_lt]
      constructor <;> linarith [ht.1, ht.2, le_max_right 0 (t₀ - η / 2)]
    · rw [heq]
      exact ht'S
  have ht₀α : t₀ ≤ α := csInf_le hSb hα
  have ht₀0 : t₀ = 0 := by
    by_contra h
    have : 0 < t₀ := lt_of_le_of_ne ht₀.1 (Ne.symm h)
    exact absurd ht₀α (not_le.2 (max_lt this (by linarith)))
  have hα0 : α = 0 := by
    show max 0 (t₀ - η / 2) = 0
    rw [ht₀0]
    exact max_eq_left (by linarith)
  simpa [hα0] using hα.2

/-- Push-up (O'Neill, Semi-Riemannian geometry, Corollary 14.1, p. 402): `p ≤ q ≪ r` implies
`p ≪ r`. -/
theorem CausalLE.trans_chronLT (hg : IsSpacetime g Y) {p q r : E n} (hpq : CausalLE g Y p q)
    (hqr : ChronLT g Y q r) : ChronLT g Y p r := by
  by_cases hne : p = q
  · rwa [hne]
  obtain ⟨γ, hγ, rfl, rfl⟩ := CausalLE.exists_isPathOn hpq hne zero_lt_one
  exact hγ.chronLT_of_chronLT hg hqr

/-- Push-up: `p ≪ q ≤ r` implies `p ≪ r`. -/
theorem ChronLT.trans_causalLE (hg : IsSpacetime g Y) {p q r : E n} (hpq : ChronLT g Y p q)
    (hqr : CausalLE g Y q r) : ChronLT g Y p r :=
  chronLT_neg_iff.1 (CausalLE.trans_chronLT hg.neg (causalLE_neg_iff.2 hqr)
    (chronLT_neg_iff.2 hpq))

end

end LorentzianCalderon
