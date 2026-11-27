module

public import LorentzianCalderon.Defs
public import LorentzianCalderon.Induction.Induction
public import LorentzianCalderon.Assembly.Exterior
public import LorentzianCalderon.Assembly.Diffeo

public section

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix

open Set Filter Topology in
/-- Step 2 of `thm_main`: the maps of the induction glue to a smooth map `Ψ` of `ℝ^{1+n}` with
`Ψ^* g' = g`, `Ψ = id` on `O` and `Ψ(W) ⊆ W`. -/
theorem exists_global_extension {n : ℕ} {T : ℝ} {g g' : MatrixField n}
    {Y Y' : E n → E n} (hgA : IsAdmissibleMetric n T g) (hg'A : IsAdmissibleMetric n T g')
    (hg : IsSpacetime g Y) (hg' : IsSpacetime g' Y')
    (hY : ∀ x ∉ M0 n T, form (g x) (EuclideanSpace.single 0 1) (Y x) < 0)
    (hY' : ∀ x ∉ M0 n T, form (g' x) (EuclideanSpace.single 0 1) (Y' x) < 0)
    (hC : CauchyDataSubset n T g g') :
    ∃ Ψ : E n → E n, ContDiff ℝ ∞ Ψ ∧ (∀ x, g x = (D Ψ x)ᵀ * g' (Ψ x) * D Ψ x) ∧
      (∀ x ∉ W n T, Ψ x = x) ∧ MapsTo Ψ (W n T) (W n T) := by
  obtain ⟨ψ, Φ, hψ, hΦ, hΦ0, -, hΦψ⟩ := Facts.exists_cauchyTemporal hg
  have hψc := hψ.smooth.continuous
  choose F hF using fun τ => exists_extensionProperty hgA hg'A hg hg' hY hY' hC hψ hΦ
    hΦ0 hΦψ τ
  have hℓ : ∀ y : E n, ψ y - 1 ∈ (univ : Set ℝ) ∧ ψ y - 1 < ψ y := fun y => ⟨trivial, by linarith⟩
  have hP : ∀ τ, ExtensionProperty g g' ψ (W n T) τ (fun x => F (ψ x - 1) x) := fun τ =>
    extensionProperty_glue hg hg' hψc hΦ.continuous hΦ0 hΦψ (fun σ _ => hF σ)
      (fun x _ => hℓ x) fun _ _ y _ => hℓ y
  refine ⟨fun x => F (ψ x - 1) x, contDiff_iff_contDiffAt.2 fun x => ?_, fun x => ?_,
    fun x hx => ?_, fun x hx => ?_⟩
  · have hx : x ∈ A ψ (ψ x - 1) := mem_A.2 (by linarith)
    exact (hP _).smooth.contDiffAt ((isOpen_A hψc _).mem_nhds hx)
  · exact (hP (ψ x - 1)).pullback x (mem_A.2 (by linarith))
  · exact (hP (ψ x - 1)).eq_self x (mem_A.2 (by linarith)) hx
  · exact (hP (ψ x - 1)).mapsTo_W_of_admissible hgA hg'A hg hg' hY hY' hψ hΦ.continuous hΦ0 hΦψ
      ⟨mem_A.2 (by linarith), hx⟩

/-- Main theorem: for `n ≥ 2`, two metrics that are Minkowskian outside the box
`M₀` and have the same Cauchy data set on `∂M₀` agree up to a diffeomorphism that is
the identity outside `M₀`. -/
theorem main (n : ℕ) (hn : 2 ≤ n) (T : ℝ) (hT : 0 < T) (g g' : MatrixField n)
    (hg : IsAdmissibleMetric n T g) (hg' : IsAdmissibleMetric n T g')
    (hC : SameCauchyDataSet n T g g') :
    ∃ Ψ : E n ≃ E n, IsIsometryFixingExterior n T Ψ g g' := by
  -- Step 1: time orientations with `∂ₜ` future-directed outside `M₀`.
  have hn1 : 1 ≤ n := by omega
  obtain ⟨Y, hY, hYt⟩ := hg.exists_future_dt hn1 hT.le
  obtain ⟨Y', hY', hY't⟩ := hg'.exists_future_dt hn1 hT.le
  have hgs : IsSpacetime g Y :=
    ⟨hn, hg.smooth, hg.lorentzian, hY, T, 1, Or.inl rfl, fun x hx =>
      ⟨hg.minkowski_exterior x hx, by simpa using hYt x hx⟩⟩
  have hg's : IsSpacetime g' Y' :=
    ⟨hn, hg'.smooth, hg'.lorentzian, hY', T, 1, Or.inl rfl, fun x hx =>
      ⟨hg'.minkowski_exterior x hx, by simpa using hY't x hx⟩⟩
  -- Step 2: the map.
  obtain ⟨Ψ, hΨ, hpull, hO, -⟩ :=
    exists_global_extension hg hg' hgs hg's hYt hY't hC.subset
  -- Step 3: `Ψ` is a diffeomorphism.
  have hinj : ∀ x, Function.Injective (fderiv ℝ Ψ x) := fun x =>
    ExtensionProperty.injective_fderiv (ψ := fun _ => 1) (τ := 0) (W := Set.univ)
      ⟨hΨ.contDiffOn, fun y _ => hpull y, fun y _ h => absurd (Set.mem_univ y) h⟩ hg.lorentzian
      (mem_A.2 one_pos)
  have hproper : IsProperMap Ψ := by
    refine isProperMap_iff_isCompact_preimage.2 ⟨hΨ.continuous, fun K hK => ?_⟩
    refine (hK.union (isCompact_W (T := T))).of_isClosed_subset (hK.isClosed.preimage hΨ.continuous)
      fun x hx => ?_
    by_cases hxW : x ∈ W n T
    · exact Or.inr hxW
    · exact Or.inl (hO x hxW ▸ hx)
  obtain ⟨e, he, he'⟩ := exists_equiv_of_isProperMap hΨ hinj hproper
  -- Step 4: `Ψ = id` outside `M₀`.
  have hid : Set.EqOn Ψ id (M0 n T)ᶜ := by
    refine eqOn_of_pullback_eq (isClosed_M0 T).isOpen_compl
      (isConnected_compl_M0 hn1 hT.le).isPreconnected
      (fun i j => (hg.smooth i j).contDiffOn) (fun x _ => hgs.det_ne_zero x) hg'.smooth hg's.symm
      hg's.det_ne_zero hΨ.contDiffOn contDiff_id.contDiffOn (fun x _ => hpull x)
      (fun x hx => ?_) isOpen_O (fun x hx => not_mem_M0_of_mem_O hx) ?_ (fun x hx => hO x
        (mem_O.1 hx))
    · rw [D_id, id, hg.minkowski_exterior x hx, hg'.minkowski_exterior x hx]
      simp
    · refine ⟨spacetimePoint (T + 1) 0, mem_O.2 fun h => ?_⟩
      have := (mem_W.1 h).2.2
      simp only [spacetimePoint_zero] at this
      linarith
  exact ⟨e, he ▸ hΨ, he', fun x hx => by rw [he]; exact hid hx, fun x => by rw [he]; exact hpull x⟩

end

end LorentzianCalderon
