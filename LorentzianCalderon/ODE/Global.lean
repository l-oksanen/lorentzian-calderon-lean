module

public import LorentzianCalderon.ODE.Smooth

public section

/-!
# Global flows of bounded fields

The flow of a `C¹` field `F` on a finite-dimensional space with `‖F‖ ≤ B` is defined for all
times: a trajectory stays within distance `B t` of its start, a uniform existence time on that
compact ball (tube lemma) continues it past any finite time. The global flow is differentiable
in time at every time.
-/

namespace LorentzianCalderon.ODEFlow

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {F : V → V} {B : ℝ}

/-- A trajectory of a field bounded by `B` moves at most at speed `B`. -/
theorem norm_flow_sub_le (hF : LocallyLipschitzOn univ F) (hB : ∀ x, ‖F x‖ ≤ B) {t : ℝ}
    (ht : 0 ≤ t) {z : V} (h : (t, z) ∈ dom F univ) : ‖flow F univ (t, z) - z‖ ≤ B * t := by
  have hs := isSol_flow hF h
  rw [uIcc_of_le ht] at hs
  have := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun s => flow F univ (s, z))
    (fun s hs' => hs.deriv s hs') (fun s _ => hB _) t ⟨ht, le_rfl⟩
  simpa [flow_zero hF (mem_univ z)] using this

variable [FiniteDimensional ℝ V]

theorem mem_dom_of_nonneg (hF : ContDiff ℝ 1 F) (hB : ∀ x, ‖F x‖ ≤ B) (z : V) {t : ℝ}
    (ht : 0 ≤ t) : (t, z) ∈ dom F univ := by
  have hFL := locallyLipschitzOn_of_contDiffOn isOpen_univ hF.contDiffOn
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB z)
  by_contra hcon
  set S := {s : ℝ | 0 ≤ s ∧ (s, z) ∉ dom F univ}
  have hSne : S.Nonempty := ⟨t, ht, hcon⟩
  have hSb : BddBelow S := ⟨0, fun s hs => hs.1⟩
  set T₀ := sInf S
  have hT₀ : 0 ≤ T₀ := le_csInf hSne fun s hs => hs.1
  have hbelow : ∀ s, 0 ≤ s → s < T₀ → (s, z) ∈ dom F univ := fun s hs hsT => by
    by_contra h
    exact (csInf_le hSb ⟨hs, h⟩).not_gt hsT
  obtain ⟨u, w, hu, -, hu0, hKw, huw⟩ := generalized_tube_lemma
    (isCompact_singleton (x := (0 : ℝ))) (isCompact_closedBall z (B * T₀))
    (isOpen_dom isOpen_univ hF.contDiffOn).1 (by
      rintro ⟨s, y⟩ ⟨hs, -⟩
      rw [show s = 0 from hs]
      exact mem_dom_zero (mem_univ y))
  obtain ⟨ε, hε, hεu⟩ := Metric.isOpen_iff.1 hu 0 (hu0 rfl)
  have hδ : ∀ y ∈ closedBall z (B * T₀), (ε / 2, y) ∈ dom F univ := fun y hy =>
    huw ⟨hεu (by rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith),
      hKw hy⟩
  set s₀ := max 0 (T₀ - ε / 4)
  have hs₀T : s₀ ≤ T₀ := max_le hT₀ (by linarith)
  have hs₀ : (s₀, z) ∈ dom F univ := by
    rcases hs₀T.lt_or_eq with h | h
    · exact hbelow s₀ (le_max_left _ _) h
    · have : s₀ = 0 := by
        rcases max_choice 0 (T₀ - ε / 4) with h' | h'
        · exact h'
        · simp only [s₀] at h; linarith
      rw [this]
      exact mem_dom_zero (mem_univ z)
  have hK : flow F univ (s₀, z) ∈ closedBall z (B * T₀) := by
    rw [mem_closedBall, dist_eq_norm]
    exact (norm_flow_sub_le hFL hB (le_max_left _ _) hs₀).trans
      (mul_le_mul_of_nonneg_left hs₀T hB0)
  have hdom := (flow_add hFL hs₀ (hδ _ hK)).1
  obtain ⟨a, haS, hlt⟩ := exists_lt_of_csInf_lt hSne
    (show T₀ < s₀ + ε / 2 by linarith [le_max_right 0 (T₀ - ε / 4)])
  exact haS.2 (mem_dom_of_mem_uIcc hdom (by
    rw [uIcc_of_le (by linarith [le_max_left 0 (T₀ - ε / 4)])]
    exact ⟨haS.1, hlt.le⟩))

/-- The flow of a bounded `C¹` field is global. -/
theorem dom_eq_univ (hF : ContDiff ℝ 1 F) (hB : ∀ x, ‖F x‖ ≤ B) : dom F univ = univ := by
  refine eq_univ_of_forall fun ⟨t, z⟩ => ?_
  rcases le_total 0 t with ht | ht
  · exact mem_dom_of_nonneg hF hB z ht
  · have := mem_dom_of_nonneg (F := -F) hF.neg (fun x => by simpa using hB x) z
      (neg_nonneg.2 ht)
    simpa using mem_dom_neg_iff.1 this

/-- A global flow solves the equation at every time. -/
theorem hasDerivAt_flow (hF : ContDiff ℝ 1 F) (hdom : dom F univ = univ) (t : ℝ) (z : V) :
    HasDerivAt (fun s => flow F univ (s, z)) (F (flow F univ (t, z))) t := by
  have hFL := locallyLipschitzOn_of_contDiffOn isOpen_univ hF.contDiffOn
  set y := flow F univ (t, z)
  obtain ⟨a, ha, ε, hε, r, hr, K, -, -, -, hsol, -⟩ :=
    exists_box isOpen_univ hF.contDiffOn (mem_univ y)
  have h0 : HasDerivAt (fun s => flow F univ (s, y)) (F y) (t - t) := by
    have := (hsol y (mem_closedBall_self hr.le)).deriv 0 ⟨by linarith, by linarith⟩
    rw [flow_zero hFL (mem_univ y)] at this
    rw [sub_self]
    exact this.hasDerivAt (Icc_mem_nhds (by linarith) hε)
  have heq : (fun s => flow F univ (s, z)) = fun s => flow F univ (s - t, y) := by
    funext s
    have := (flow_add hFL (s := t) (t := s - t) (z := z) (hdom ▸ mem_univ _)
      (hdom ▸ mem_univ _)).2
    rwa [add_sub_cancel] at this
  rw [heq]
  simpa [Function.comp_def] using
    h0.scomp (h := fun s => s - t) t ((hasDerivAt_id t).sub_const t)

end

end LorentzianCalderon.ODEFlow
