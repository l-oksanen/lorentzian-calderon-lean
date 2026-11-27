module

public import LorentzianCalderon.Induction.Unique
public import LorentzianCalderon.Setting.Escape

public section

/-!
# The induction: patching

Blueprint, Lemma `lem_ind_patching`. Given, for every `q₀ ∈ Σ_τ ∩ W`, a local isometry
`Ψ_{q₀}` on an open neighbourhood `V(q₀)` of `q₀` which agrees with `Ψ` on `V(q₀) ∩ A_τ` and is
the identity outside `W`, the maps are patched to a map with the extension property at a lower
level.

The flow boxes are the sets `B(q₀)` of points `x` whose flow line `Φ([0, 2δ(q₀)], x)` stays in
`V(q₀)`. Two local maps agree at `x ∈ B(q₀) ∩ B(q₁)` because the
connected component of `x` in `V(q₀) ∩ V(q₁)` contains a flow line from `x` into `A_τ`.
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Set Filter

variable {n : ℕ} {T : ℝ} {g g' : MatrixField n} {Y Y' : E n → E n} {ψ : E n → ℝ}
  {Φ : ℝ → E n → E n} {τ : ℝ} {Ψ : E n → E n}

/-- A map that agrees near each point of `A_τ` with a local isometry has the extension property
at level `τ`. -/
theorem ExtensionProperty.of_locally {W : Set (E n)} {G : E n → E n}
    (h : ∀ x ∈ A ψ τ, ∃ U ∈ 𝓝 x, ∃ Ψ' : E n → E n, EqOn G Ψ' U ∧ ContDiffAt ℝ ∞ Ψ' x ∧
      g x = (D Ψ' x)ᵀ * g' (Ψ' x) * D Ψ' x ∧ (x ∉ W → Ψ' x = x)) :
    ExtensionProperty g g' ψ W τ G := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx hxW => ?_⟩ <;>
    obtain ⟨U, hU, Ψ', heq, hc, hpull, hself⟩ := h x hx <;>
    have hev : G =ᶠ[𝓝 x] Ψ' := eventually_of_mem hU heq
  · exact (hc.congr_of_eventuallyEq hev).contDiffWithinAt
  · rw [show D G x = D Ψ' x by ext i j; simp only [D_def, hev.fderiv_eq], hev.eq_of_nhds]
    exact hpull
  · rw [hev.eq_of_nhds]
    exact hself hxW

/-- The points whose flow line on `[0, r]` stays in the open set `V` form an open set. -/
lemma isOpen_setOf_forall_flow_mem (hΦ : Continuous fun p : ℝ × E n => Φ p.1 p.2) {V : Set (E n)}
    (hV : IsOpen V) (r : ℝ) : IsOpen {x | ∀ t ∈ Icc 0 r, Φ t x ∈ V} := by
  refine isOpen_iff_mem_nhds.2 fun x hx => ?_
  have := (isCompact_Icc (a := (0 : ℝ)) (b := r)).eventually_forall_of_forall_eventually
    (P := fun (y : E n) (t : ℝ) => Φ t y ∈ V) (x₀ := x) fun t ht => by
      have hc : ContinuousAt (fun p : E n × ℝ => Φ p.2 p.1) (x, t) :=
        (hΦ.comp continuous_swap).continuousAt
      exact hc.eventually_mem (hV.mem_nhds (hx t ht))
  exact this

variable (hg : IsSpacetime g Y) (hg' : IsSpacetime g' Y') (hψc : Continuous ψ)
  (hΦ : Continuous fun p : ℝ × E n => Φ p.1 p.2) (hΦ0 : ∀ x, Φ 0 x = x)
  (hΦψ : ∀ t x, ψ (Φ t x) = ψ x + t)
include hg hg' hψc hΦ hΦ0 hΦψ

/-- Two local isometries which agree with `Ψ` on `A_τ` agree at a point `x` whose flow line on
`[0, r]` stays in both domains and ends in `A_τ`. -/
theorem eq_of_flow_mem {V₁ V₂ : Set (E n)} (hV₁ : IsOpen V₁) (hV₂ : IsOpen V₂)
    {Ψ₁ Ψ₂ : E n → E n} (hs₁ : ContDiffOn ℝ ∞ Ψ₁ V₁) (hs₂ : ContDiffOn ℝ ∞ Ψ₂ V₂)
    (hp₁ : ∀ x ∈ V₁, g x = (D Ψ₁ x)ᵀ * g' (Ψ₁ x) * D Ψ₁ x)
    (hp₂ : ∀ x ∈ V₂, g x = (D Ψ₂ x)ᵀ * g' (Ψ₂ x) * D Ψ₂ x)
    (he₁ : EqOn Ψ₁ Ψ (V₁ ∩ A ψ τ)) (he₂ : EqOn Ψ₂ Ψ (V₂ ∩ A ψ τ)) {x : E n} {r : ℝ}
    (hr : 0 ≤ r) (hx : ∀ t ∈ Icc 0 r, Φ t x ∈ V₁ ∩ V₂) (hxr : τ < ψ x + r) :
    Ψ₁ x = Ψ₂ x := by
  set O := V₁ ∩ V₂
  have hO : IsOpen O := hV₁.inter hV₂
  set C := connectedComponentIn O x
  have hCo : IsOpen C := hO.connectedComponentIn
  have hCO : C ⊆ O := connectedComponentIn_subset O x
  have hseg : (fun t => Φ t x) '' Icc 0 r ⊆ C :=
    (isPreconnected_Icc.image _ (hΦ.comp (continuous_id.prodMk continuous_const)).continuousOn
      ).subset_connectedComponentIn ⟨0, ⟨le_rfl, hr⟩, hΦ0 x⟩ (by
        rintro _ ⟨t, ht, rfl⟩; exact hx t ht)
  have hxC : x ∈ C := by simpa [hΦ0] using hseg ⟨0, ⟨le_rfl, hr⟩, rfl⟩
  have hzC : Φ r x ∈ C := hseg ⟨r, ⟨hr, le_rfl⟩, rfl⟩
  have hzA : Φ r x ∈ A ψ τ := by rw [mem_A, hΦψ]; exact hxr
  refine eqOn_of_pullback_eq hCo isPreconnected_connectedComponentIn
    (fun i j => (hg.smooth i j).contDiffOn) (fun x _ => hg.det_ne_zero x) hg'.smooth hg'.symm
    hg'.det_ne_zero (hs₁.mono fun y hy => (hCO hy).1) (hs₂.mono fun y hy => (hCO hy).2)
    (fun y hy => hp₁ y (hCO hy).1) (fun y hy => hp₂ y (hCO hy).2)
    (hCo.inter (isOpen_A hψc τ)) inter_subset_left ⟨_, hzC, hzA⟩ (fun y hy => ?_) hxC
  rw [he₁ ⟨(hCO hy.1).1, hy.2⟩, he₂ ⟨(hCO hy.1).2, hy.2⟩]

/-- **Patching** (`lem_ind_patching`): if every `q₀ ∈ Σ_τ ∩ W` has a local isometry near it which
agrees with `Ψ` on `A_τ` and is the identity outside `W`, then `P(τ - δ)` holds for some `δ > 0`. -/
theorem ExtensionProperty.exists_extend_below_of_local
    (hP : ExtensionProperty g g' ψ (W n T) τ Ψ) (hgA : IsAdmissibleMetric n T g)
    (hg'A : IsAdmissibleMetric n T g')
    (hloc : ∀ q₀ ∈ W n T, ψ q₀ = τ → ∃ U : Set (E n), IsOpen U ∧ q₀ ∈ U ∧ ∃ Ψ₀ : E n → E n,
      ContDiffOn ℝ ∞ Ψ₀ U ∧ (∀ x ∈ U, g x = (D Ψ₀ x)ᵀ * g' (Ψ₀ x) * D Ψ₀ x) ∧
      EqOn Ψ₀ Ψ (U ∩ A ψ τ) ∧ ∀ x ∈ U, x ∉ W n T → Ψ₀ x = x) :
    ∃ δ > 0, ∃ Ψ' : E n → E n, ExtensionProperty g g' ψ (W n T) (τ - δ) Ψ' := by
  classical
  set K := W n T ∩ ψ ⁻¹' {τ}
  have hK : IsCompact K := isCompact_W.inter_right (isClosed_singleton.preimage hψc)
  have hdata : ∀ q : E n, ∃ U : Set (E n), ∃ Ψ₀ : E n → E n, ∃ r : ℝ, q ∈ K →
      IsOpen U ∧ ContDiffOn ℝ ∞ Ψ₀ U ∧ (∀ x ∈ U, g x = (D Ψ₀ x)ᵀ * g' (Ψ₀ x) * D Ψ₀ x) ∧
      EqOn Ψ₀ Ψ (U ∩ A ψ τ) ∧ (∀ x ∈ U, x ∉ W n T → Ψ₀ x = x) ∧ 0 < r ∧
      ∀ t ∈ Icc 0 (2 * r), Φ t q ∈ U := by
    intro q
    by_cases hq : q ∈ K
    · obtain ⟨U, hU, hqU, Ψ₀, h1, h2, h3, h4⟩ := hloc q hq.1 hq.2
      have hc : ContinuousAt (fun t => Φ t q) 0 :=
        (hΦ.comp (continuous_id.prodMk continuous_const)).continuousAt
      have hev := hc.eventually_mem (by rw [hΦ0]; exact hU.mem_nhds hqU)
      obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
      refine ⟨U, Ψ₀, ε / 4, fun _ => ⟨hU, h1, h2, h3, h4, by positivity, fun t ht => ?_⟩⟩
      refine hball ?_
      rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
      linarith [ht.2]
    · exact ⟨∅, id, 0, fun h => absurd h hq⟩
  choose U Ψ₀ r hdata using hdata
  set B : E n → Set (E n) := fun q => {x | ∀ t ∈ Icc 0 (2 * r q), Φ t x ∈ U q}
  have hBo : ∀ q ∈ K, IsOpen (B q) := fun q hq =>
    isOpen_setOf_forall_flow_mem hΦ (hdata q hq).1 _
  have hBU : ∀ q ∈ K, B q ⊆ U q := fun q hq x hx => by
    simpa [hΦ0] using hx 0 ⟨le_rfl, by linarith [(hdata q hq).2.2.2.2.2.1]⟩
  obtain ⟨t, htK, hcover⟩ := hK.elim_nhds_subcover B fun q hq =>
    (hBo q hq).mem_nhds (hdata q hq).2.2.2.2.2.2
  set Bt := ⋃ q ∈ t, B q
  have hBto : IsOpen Bt := isOpen_biUnion fun q hq => hBo q (htK q hq)
  -- the levels `δ` that work
  have hev₁ : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ q ∈ t, δ ≤ r q := by
    rw [Finset.eventually_all]
    intro q hq
    exact Filter.mem_of_superset (Ioc_mem_nhdsGT (hdata q (htK q hq)).2.2.2.2.2.1)
      fun δ hδ => hδ.2
  have hev₂ : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ x ∈ W n T, τ - δ < ψ x → ψ x ≤ τ → x ∈ Bt := by
    set K' := (W n T ∩ ψ ⁻¹' Iic τ) \ Bt
    have hK' : IsCompact K' :=
      (isCompact_W.inter_right (isClosed_Iic.preimage hψc)).diff hBto
    rcases K'.eq_empty_or_nonempty with he | hne
    · refine Eventually.of_forall fun δ x hxW _ hxτ => ?_
      by_contra hx
      exact (he ▸ (⟨⟨hxW, hxτ⟩, hx⟩ : x ∈ K') : x ∈ (∅ : Set (E n)))
    obtain ⟨y, hyK', hy⟩ := hK'.exists_isMaxOn hne hψc.continuousOn
    have hyτ : ψ y < τ := by
      refine lt_of_le_of_ne hyK'.1.2 fun h => hyK'.2 ?_
      exact hcover ⟨hyK'.1.1, h⟩
    refine Filter.mem_of_superset (Ioo_mem_nhdsGT (sub_pos.2 hyτ)) fun δ hδ x hxW hxδ hxτ => ?_
    by_contra hx
    have := hy ⟨⟨hxW, hxτ⟩, hx⟩
    simp only [mem_ofPred_eq] at this
    linarith [hδ.2]
  obtain ⟨δ, ⟨hδr, hδB⟩, hδ⟩ := (hev₁.and hev₂).and self_mem_nhdsWithin |>.exists
  have hδ : (0 : ℝ) < δ := hδ
  -- agreement on overlaps
  have hover : ∀ q₁ ∈ t, ∀ q₂ ∈ t, ∀ x ∈ B q₁, x ∈ B q₂ → τ - δ < ψ x →
      Ψ₀ q₁ x = Ψ₀ q₂ x := by
    intro q₁ hq₁ q₂ hq₂ x hx₁ hx₂ hxδ
    have h₁ := hdata q₁ (htK q₁ hq₁)
    have h₂ := hdata q₂ (htK q₂ hq₂)
    refine eq_of_flow_mem hg hg' hψc hΦ hΦ0 hΦψ h₁.1 h₂.1 h₁.2.1 h₂.2.1 h₁.2.2.1 h₂.2.2.1
      h₁.2.2.2.1 h₂.2.2.2.1 (r := 2 * δ) (by linarith) (fun s hs => ⟨hx₁ s ⟨hs.1, ?_⟩,
        hx₂ s ⟨hs.1, ?_⟩⟩) (by linarith)
    · linarith [hs.2, hδr q₁ hq₁]
    · linarith [hs.2, hδr q₂ hq₂]
  set G : E n → E n := fun x =>
    if τ < ψ x then Ψ x else if h : ∃ q ∈ t, x ∈ B q then Ψ₀ h.choose x else x
  have hGB : ∀ q ∈ t, ∀ x ∈ B q, τ - δ < ψ x → G x = Ψ₀ q x := by
    intro q hq x hxB hxδ
    have hd := hdata q (htK q hq)
    simp only [G]
    split_ifs with h1 h2
    · exact (hd.2.2.2.1 ⟨hBU q (htK q hq) hxB, (mem_A.2 h1)⟩).symm
    · exact hover _ h2.choose_spec.1 q hq x h2.choose_spec.2 hxB hxδ
    · exact absurd ⟨q, hq, hxB⟩ h2
  have hGO : ∀ x, x ∉ W n T → G x = x := by
    intro x hx
    simp only [G]
    split_ifs with h1 h2
    · exact hP.eq_self x (mem_A.2 h1) hx
    · have hd := hdata _ (htK _ h2.choose_spec.1)
      exact hd.2.2.2.2.1 x (hBU _ (htK _ h2.choose_spec.1) h2.choose_spec.2) hx
    · rfl
  refine ⟨δ, hδ, G, ExtensionProperty.of_locally fun x hx => ?_⟩
  have hAδ : IsOpen (A ψ (τ - δ)) := isOpen_A hψc _
  by_cases hxτ : τ < ψ x
  · refine ⟨A ψ τ, (isOpen_A hψc τ).mem_nhds (mem_A.2 hxτ), Ψ,
      fun y hy => by simp [G, show τ < ψ y from mem_A.1 hy],
      hP.smooth.contDiffAt ((isOpen_A hψc τ).mem_nhds (mem_A.2 hxτ)), hP.pullback x (mem_A.2 hxτ),
      hP.eq_self x (mem_A.2 hxτ)⟩
  by_cases hxW : x ∈ W n T
  · obtain ⟨q, hqt, hxq⟩ := mem_iUnion₂.1 (hδB x hxW (mem_A.1 hx) (not_lt.1 hxτ))
    have hd := hdata q (htK q hqt)
    have hxU := hBU q (htK q hqt) hxq
    exact ⟨B q ∩ A ψ (τ - δ), (hBo q (htK q hqt)).mem_nhds hxq |> inter_mem <|
      hAδ.mem_nhds hx, Ψ₀ q, fun y hy => hGB q hqt y hy.1 (mem_A.1 hy.2),
      hd.2.1.contDiffAt (hd.1.mem_nhds hxU), hd.2.2.1 x hxU, hd.2.2.2.2.1 x hxU⟩
  · refine ⟨(W n T)ᶜ, isClosed_W.isOpen_compl.mem_nhds hxW, id, fun y hy => hGO y hy,
      contDiff_id.contDiffAt, ?_, fun _ => rfl⟩
    have hxM : x ∉ M0 n T := fun h => hxW (M0_subset_W h)
    rw [D_id, id, hgA.minkowski_exterior x hxM, hg'A.minkowski_exterior x hxM]
    simp

end

end LorentzianCalderon
