module

public import LorentzianCalderon.Geometry.Reach
public import LorentzianCalderon.Induction.Setup
public import LorentzianCalderon.Green.Basic

public section

/-!
# Small lenses above a point

For a Cauchy temporal function `ψ`, the part of the causal future of a small ball `K` around
`q₀` below a level `c` close to `ψ(q₀)` is compact and lies in any given neighbourhood of `q₀`
(`IsCauchyTemporal.exists_causalFutureSet_inter_le_subset`, blueprint `lem_ind_small_lens`).
-/

namespace LorentzianCalderon

noncomputable section
open Set Filter Function Metric
open scoped ContDiff Topology

variable {n : ℕ} {g : MatrixField n} {Y : E n → E n} {ψ : E n → ℝ}

/-- The causal future of a small ball around `q₀`, below a level slightly above `ψ(q₀)`, is a
compact subset of a given neighbourhood of `q₀`. -/
theorem IsCauchyTemporal.exists_causalFutureSet_inter_le_subset (hg : IsSpacetime g Y)
    (hψ : IsCauchyTemporal g Y ψ) {q₀ : E n} {O : Set (E n)} (hO : O ∈ 𝓝 q₀) :
    ∃ r > 0, ∃ c > ψ q₀, causalFutureSet g Y (closedBall q₀ r) ∩ {x | ψ x ≤ c} ⊆ O ∧
      IsCompact (causalFutureSet g Y (closedBall q₀ r) ∩ {x | ψ x ≤ c}) := by
  obtain ⟨ρ₀, hρ₀, hρ₀O⟩ := Metric.mem_nhds_iff.1 hO
  set ρ := ρ₀ / 2
  have hρ : 0 < ρ := half_pos hρ₀
  have hψc := hψ.smooth.continuous
  have hclosed : ∀ r c, IsClosed (causalFutureSet g Y (closedBall q₀ r) ∩ {x | ψ x ≤ c}) :=
    fun r c => (isClosed_causalFutureSet hg (isCompact_closedBall _ _)).inter
      (isClosed_le hψc continuous_const)
  suffices h : ∃ r > 0, ∃ c > ψ q₀,
      causalFutureSet g Y (closedBall q₀ r) ∩ {x | ψ x ≤ c} ⊆ ball q₀ ρ by
    obtain ⟨r, hr, c, hc, hsub⟩ := h
    refine ⟨r, hr, c, hc, fun x hx => hρ₀O (ball_subset_ball (half_le_self hρ₀.le) (hsub hx)), ?_⟩
    exact (isCompact_closedBall q₀ ρ).of_isClosed_subset (hclosed r c)
      (hsub.trans ball_subset_closedBall)
  by_contra hcon
  push Not at hcon
  set r : ℕ → ℝ := fun m => ρ / ((m : ℝ) + 2)
  have hr : ∀ m, 0 < r m := fun m => by positivity
  have hrρ : ∀ m, r m < ρ := fun m => by
    simp only [r]
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  set S : ℕ → Set (E n) := fun m => causalFutureSet g Y (closedBall q₀ (r m)) ∩
    {x | ψ x ≤ ψ q₀ + r m} ∩ sphere q₀ ρ
  have hSc : ∀ m, IsClosed (S m) := fun m => (hclosed _ _).inter isClosed_sphere
  have hS0 : IsCompact (S 0) := (isCompact_sphere q₀ ρ).of_isClosed_subset (hSc 0)
    inter_subset_right
  have hmono : ∀ m, S (m + 1) ⊆ S m := by
    intro m x ⟨⟨h1, h2⟩, h3⟩
    have hle : r (m + 1) ≤ r m :=
      div_le_div_of_nonneg_left hρ.le (by positivity) (by push_cast; linarith)
    exact ⟨⟨causalFutureSet_mono (closedBall_subset_closedBall hle) h1,
      show ψ x ≤ ψ q₀ + r m from le_trans h2 (by linarith)⟩, h3⟩
  have hne : ∀ m, (S m).Nonempty := fun m => by
    obtain ⟨x, ⟨hxJ, hxψ⟩, hxB⟩ := not_subset.1 (hcon (r m) (hr m) (ψ q₀ + r m)
      (by linarith [hr m]))
    obtain ⟨b, hb, hbx⟩ := mem_causalFutureSet.1 hxJ
    have hbρ : dist b q₀ < ρ := (mem_closedBall.1 hb).trans_lt (hrρ m)
    have hxρ : ρ ≤ dist x q₀ := not_lt.1 hxB
    have hbx' : b ≠ x := fun h => by rw [h] at hbρ; linarith
    obtain ⟨γ, hγ, hγ0, hγ1⟩ := CausalLE.exists_isPathOn (mem_causalFuture.1 hbx) hbx' zero_lt_one
    have hdc : ContinuousOn (fun t => dist (γ t) q₀) (Icc 0 1) :=
      (continuous_id.dist continuous_const).comp_continuousOn hγ.continuousOn
    obtain ⟨t, ht, hty⟩ := intermediate_value_Icc zero_le_one hdc
      (show ρ ∈ Icc (dist (γ 0) q₀) (dist (γ 1) q₀) by
        rw [hγ0, hγ1]; exact ⟨hbρ.le, hxρ⟩)
    simp only at hty
    have ht0 : 0 < t := lt_of_le_of_ne ht.1 fun h => by
      rw [← h, hγ0] at hty; linarith
    have hby : CausalLE g Y b (γ t) := by
      simpa [hγ0] using causalLE_of_isPathOn (hγ.restrict le_rfl ht0 ht.2)
    have hyx : CausalLE g Y (γ t) x := by
      rcases ht.2.lt_or_eq with ht1 | ht1
      · simpa [hγ1] using causalLE_of_isPathOn (hγ.restrict ht.1 ht1 le_rfl)
      · rw [ht1, hγ1]
    exact ⟨γ t, ⟨mem_causalFutureSet.2 ⟨b, hb, mem_causalFuture.2 hby⟩,
      (hψ.le_of_causalLE hg hyx).trans hxψ⟩,
      mem_sphere.2 hty⟩
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hmono hne
    hS0 hSc
  have hxS : ∀ m, x ∈ S m := mem_iInter.1 hx
  have hsmall : ∀ ε > 0, ∃ m, r m < ε := fun ε hε => by
    obtain ⟨m, hm⟩ := exists_nat_gt (ρ / ε)
    refine ⟨m, ?_⟩
    simp only [r]
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε] at hm
    nlinarith
  have hψx : ψ x ≤ ψ q₀ := le_of_forall_pos_lt_add fun ε hε => by
    obtain ⟨m, hm⟩ := hsmall ε hε
    have h := (hxS m).1.2
    simp only [mem_ofPred_eq] at h
    linarith
  have hq₀x : CausalLE g Y q₀ x := by
    have : q₀ ∈ closure (causalPast g Y x) := Metric.mem_closure_iff.2 fun ε hε => by
      obtain ⟨m, hm⟩ := hsmall ε hε
      obtain ⟨y, hy, hyx⟩ := mem_causalFutureSet.1 (hxS m).1.1
      exact ⟨y, mem_causalPast.2 (mem_causalFuture.1 hyx), by
        rw [dist_comm]; exact (mem_closedBall.1 hy).trans_lt hm⟩
    rw [(isClosed_causalPast hg x).closure_eq] at this
    exact mem_causalPast.1 this
  have hxq : q₀ ≠ x := fun h => by
    have := mem_sphere.1 (hxS 0).2
    rw [← h, dist_self] at this
    linarith
  exact (lt_of_causalLE hg (hψ.smooth.differentiable (by simp)) hψ.past_gradient hq₀x
    hxq).not_ge hψx

end

end LorentzianCalderon
