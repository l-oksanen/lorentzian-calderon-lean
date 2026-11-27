module

public import LorentzianCalderon.Setting.Data

public section

/-!
# Transfer of solutions

Blueprint, Lemma `lem_transfer`: every smooth solution `v'` of `□_{g'} v' = 0` agrees on `O`
with a unique smooth solution `v = 𝒯 v'` of `□_g v = 0`.
-/

namespace LorentzianCalderon

noncomputable section
open Set Filter Function
open scoped ContDiff Matrix Topology

variable {n : ℕ} {T : ℝ} {g g' : MatrixField n} {Y Y' : E n → E n}

/-- A smooth solution of `□_g v = 0` that vanishes on `O` vanishes: it is supported in the
compact set `W ⊆ J⁺(W)`. -/
theorem eq_zero_of_eq_zero_on_O (hg : IsSpacetime g Y) {v : E n → ℝ} (hv : ContDiff ℝ ∞ v)
    (hbox : ∀ x, box g v x = 0) (h0 : ∀ x ∈ O n T, v x = 0) : v = 0 :=
  eq_zero_of_support_subset_causalFutureSet hg hv hbox (isCompact_W (n := n) (T := T))
    fun x hx => subset_causalFutureSet _ (of_not_not fun hxW => hx (h0 x (mem_O.2 hxW)))

/-- Uniqueness in `lem_transfer`. -/
theorem eq_of_eqOn_O (hg : IsSpacetime g Y) {v₁ v₂ : E n → ℝ} (hv₁ : ContDiff ℝ ∞ v₁)
    (hv₂ : ContDiff ℝ ∞ v₂) (hbox₁ : ∀ x, box g v₁ x = 0) (hbox₂ : ∀ x, box g v₂ x = 0)
    (h : ∀ x ∈ O n T, v₁ x = v₂ x) : v₁ = v₂ := by
  have := eq_zero_of_eq_zero_on_O (T := T) hg (hv₁.sub hv₂)
    (fun x => by rw [box_sub hg.smooth hg.det_ne_zero hv₁ hv₂, hbox₁, hbox₂, sub_self])
    fun x hx => sub_eq_zero.2 (h x hx)
  funext x
  exact sub_eq_zero.1 (congr_fun this x)

/-- Existence in `lem_transfer`. -/
theorem exists_transfer (hgA : IsAdmissibleMetric n T g) (hg'A : IsAdmissibleMetric n T g')
    (hg : IsSpacetime g Y) (hg' : IsSpacetime g' Y')
    (hY : ∀ x ∉ M0 n T, form (g x) (EuclideanSpace.single 0 1) (Y x) < 0)
    (hY' : ∀ x ∉ M0 n T, form (g' x) (EuclideanSpace.single 0 1) (Y' x) < 0)
    (hC : CauchyDataSubset n T g g') {v' : E n → ℝ} (hv' : ContDiff ℝ ∞ v')
    (hbox' : ∀ x, box g' v' x = 0) :
    ∃ v : E n → ℝ, ContDiff ℝ ∞ v ∧ (∀ x, box g v x = 0) ∧ ∀ x ∈ O n T, v x = v' x := by
  obtain ⟨r, hr0, hr⟩ := (isCompact_W (n := n) (T := T)).isBounded.subset_closedBall_lt 0 0
  let χ : ContDiffBump (0 : E n) := ⟨r + 1, r + 2, by linarith, by linarith⟩
  set B := Metric.ball (0 : E n) (r + 1)
  have hB : IsOpen B := Metric.isOpen_ball
  have hWB : W n T ⊆ B := fun x hx =>
    Metric.mem_ball.2 (lt_of_le_of_lt (Metric.mem_closedBall.1 (hr hx)) (by linarith))
  have hM0B : M0 n T ⊆ B := M0_subset_W.trans hWB
  have hχ1 : ∀ x ∈ B, χ x = 1 := fun x hx => χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)
  have hχ : ContDiff ℝ ∞ χ := χ.contDiff
  set cv : E n → ℝ := fun x => χ x * v' x
  have hcv : ContDiff ℝ ∞ cv := hχ.mul hv'
  have hcv' : HasCompactSupport cv := χ.hasCompactSupport.mul_right
  set f := box g' cv
  have hf : ContDiff ℝ ∞ f := contDiff_box hg'.smooth hg'.det_ne_zero hcv
  have hf' : HasCompactSupport f := hasCompactSupport_box hcv'
  have hfB : ∀ x ∈ B, f x = 0 := fun x hx => by
    simp only [f]
    rw [box_congr (v := v') (eventually_of_mem (hB.mem_nhds hx) fun y hy => by
      simp [cv, hχ1 y hy]), hbox']
  have hfM : tsupport f ⊆ (M0 n T)ᶜ := by
    refine (closure_minimal (s := support f) (t := Bᶜ) (fun x hx hxB => hx (hfB x hxB))
      hB.isClosed_compl).trans ?_
    exact compl_subset_compl.2 hM0B
  set w : E n → ℝ := fun x => (1 - χ x) * v' x
  have hw : ContDiff ℝ ∞ w := (contDiff_const.sub hχ).mul hv'
  have hwbox : ∀ x, box g w x = box g' w x := by
    intro x
    by_cases hx : x ∈ M0 n T
    · have h0 : w =ᶠ[𝓝 x] 0 := eventually_of_mem (hB.mem_nhds (hM0B hx)) fun y hy => by
        simp [w, hχ1 y hy]
      rw [box_eq_zero_of_eventuallyEq h0, box_eq_zero_of_eventuallyEq h0]
    · have hS : IsOpen (M0 n T)ᶜ := (isCompact_M0 T).isClosed.isOpen_compl
      exact box_congr_metric (eventually_of_mem (hS.mem_nhds hx) fun y hy => by
        rw [hgA.minkowski_exterior y hy, hg'A.minkowski_exterior y hy])
  refine ⟨fun x => w x + retarded g Y f x, hw.add contDiff_retarded, fun x => ?_, fun x hx => ?_⟩
  · rw [box_add hg.smooth hg.det_ne_zero hw contDiff_retarded, box_retarded hg hf hf', hwbox]
    simp only [f]
    rw [← box_add hg'.smooth hg'.det_ne_zero hw hcv]
    have : (fun y => w y + cv y) = v' := by
      funext y
      simp only [w, cv]
      ring
    rw [this, hbox']
  · simp only
    rw [retarded_eq_of_cauchyDataSubset hgA hg'A hg hg' hY hY' hC hf hf' hfM
      (not_mem_M0_of_mem_O hx), retarded_box hg' hcv hcv']
    simp only [w, cv]
    ring

/-- **Transfer of solutions** (blueprint, Lemma `lem_transfer`). -/
theorem existsUnique_transfer (hgA : IsAdmissibleMetric n T g)
    (hg'A : IsAdmissibleMetric n T g') (hg : IsSpacetime g Y) (hg' : IsSpacetime g' Y')
    (hY : ∀ x ∉ M0 n T, form (g x) (EuclideanSpace.single 0 1) (Y x) < 0)
    (hY' : ∀ x ∉ M0 n T, form (g' x) (EuclideanSpace.single 0 1) (Y' x) < 0)
    (hC : CauchyDataSubset n T g g') {v' : E n → ℝ} (hv' : ContDiff ℝ ∞ v')
    (hbox' : ∀ x, box g' v' x = 0) :
    ∃! v : E n → ℝ, ContDiff ℝ ∞ v ∧ (∀ x, box g v x = 0) ∧ ∀ x ∈ O n T, v x = v' x := by
  obtain ⟨v, hv⟩ := exists_transfer hgA hg'A hg hg' hY hY' hC hv' hbox'
  refine ⟨v, hv, fun v₁ hv₁ => eq_of_eqOn_O (T := T) hg hv₁.1 hv.1 hv₁.2.1 hv.2.1 fun x hx => ?_⟩
  rw [hv₁.2.2 x hx, hv.2.2 x hx]

variable (n T g) in
open Classical in
/-- The transfer `𝒯 v'`: the smooth solution of `□_g v = 0` that agrees with `v'` on `O`, if
there is one; `0` otherwise. -/
def transfer (v' : E n → ℝ) : E n → ℝ :=
  if h : ∃ v : E n → ℝ, ContDiff ℝ ∞ v ∧ (∀ x, box g v x = 0) ∧ ∀ x ∈ O n T, v x = v' x then
    h.choose
  else 0

theorem transfer_spec (hgA : IsAdmissibleMetric n T g) (hg'A : IsAdmissibleMetric n T g')
    (hg : IsSpacetime g Y) (hg' : IsSpacetime g' Y')
    (hY : ∀ x ∉ M0 n T, form (g x) (EuclideanSpace.single 0 1) (Y x) < 0)
    (hY' : ∀ x ∉ M0 n T, form (g' x) (EuclideanSpace.single 0 1) (Y' x) < 0)
    (hC : CauchyDataSubset n T g g') {v' : E n → ℝ} (hv' : ContDiff ℝ ∞ v')
    (hbox' : ∀ x, box g' v' x = 0) :
    ContDiff ℝ ∞ (transfer n T g v') ∧ (∀ x, box g (transfer n T g v') x = 0) ∧
      ∀ x ∈ O n T, transfer n T g v' x = v' x := by
  have h := exists_transfer hgA hg'A hg hg' hY hY' hC hv' hbox'
  rw [transfer, dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec

/-- `𝒯 v'` is the only smooth solution of `□_g v = 0` that agrees with `v'` on `O`. -/
theorem eq_transfer (hgA : IsAdmissibleMetric n T g) (hg'A : IsAdmissibleMetric n T g')
    (hg : IsSpacetime g Y) (hg' : IsSpacetime g' Y')
    (hY : ∀ x ∉ M0 n T, form (g x) (EuclideanSpace.single 0 1) (Y x) < 0)
    (hY' : ∀ x ∉ M0 n T, form (g' x) (EuclideanSpace.single 0 1) (Y' x) < 0)
    (hC : CauchyDataSubset n T g g') {v' : E n → ℝ} (hv' : ContDiff ℝ ∞ v')
    (hbox' : ∀ x, box g' v' x = 0) {v : E n → ℝ} (hv : ContDiff ℝ ∞ v)
    (hbox : ∀ x, box g v x = 0) (hvO : ∀ x ∈ O n T, v x = v' x) : v = transfer n T g v' := by
  obtain ⟨h1, h2, h3⟩ := transfer_spec hgA hg'A hg hg' hY hY' hC hv' hbox'
  exact eq_of_eqOn_O (T := T) hg hv h1 hbox h2 fun x hx => by rw [hvO x hx, h3 x hx]

end

end LorentzianCalderon
