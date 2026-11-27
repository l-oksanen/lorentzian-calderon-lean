module

public import LorentzianCalderon.Induction.Unique
public import LorentzianCalderon.Setting.Transfer
public import LorentzianCalderon.Waves.Jump
public import LorentzianCalderon.Local.Naturality

public section

/-!
# Propagation of identities

Blueprint, Lemma `lem_propagation`, part (b): under `P(τ)`, the transfer `𝒯 v'` of a solution
`v'` of `□_{g'} v' = 0` is `v' ∘ Ψ` on `A_τ`.

The key step is a vanishing lemma (`eqOn_zero_of_box_eq_zero`): a smooth solution of
`□_g z = 0` on `A_τ` that vanishes outside the compact set `W` vanishes. It is proved by
duality with the retarded solution operator: for a test function `ϑ` supported in `A_τ`,
`ϑ = □_g (ζ G^ret ϑ)` near `supp z` for a cut-off `ζ`, and Green's identity gives
`∫ z ϑ dV = ∫ (□_g z) ζ G^ret ϑ dV = 0`.
-/

namespace LorentzianCalderon

noncomputable section
open MeasureTheory Set Filter Function
open scoped ContDiff Matrix Topology

variable {n : ℕ}

/-! ### Testing on open sets -/

/-- A function continuous on an open set `U` whose integrals against all test functions supported
in `U` vanish is zero on `U`. -/
theorem eqOn_zero_of_integral_mul_eq_zero_of_continuousOn {U : Set (E n)} (hU : IsOpen U)
    {φ : E n → ℝ} (hφ : ContinuousOn φ U)
    (h : ∀ h : E n → ℝ, ContDiff ℝ ∞ h → HasCompactSupport h → tsupport h ⊆ U →
      ∫ x, h x * φ x = 0) : ∀ x ∈ U, φ x = 0 := by
  have hae := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
    (hφ.locallyIntegrableOn hU.measurableSet) fun h' hh hh' hU' => by
      simpa only [smul_eq_mul] using h h' hh hh' hU'
  set V := U ∩ φ ⁻¹' {0}ᶜ
  have hV : IsOpen V := hφ.isOpen_inter_preimage hU isOpen_compl_singleton
  have hV0 : volume V = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hae] with x hx hxV
    exact hxV.2 (hx hxV.1)
  have hVe := (hV.measure_eq_zero_iff volume).1 hV0
  intro x hx
  by_contra hne
  have : x ∈ V := ⟨hx, hne⟩
  rw [hVe] at this
  exact this

section Box

variable {g : MatrixField n}

/-- `□_g` is additive at points of an open set where both functions are smooth. -/
theorem box_sub_of_contDiffOn (hg : ∀ i j, ContDiff ℝ ∞ fun x => g x i j)
    (hdet : ∀ x, (g x).det ≠ 0) {U : Set (E n)} (hU : IsOpen U) {u v : E n → ℝ}
    (hu : ContDiffOn ℝ ∞ u U) (hv : ContDiffOn ℝ ∞ v U) {x : E n} (hx : x ∈ U) :
    box g (fun y => u y - v y) x = box g u x - box g v x := by
  obtain ⟨χ, hχ, -, -, hχU, hχ1⟩ := exists_cutoff (isCompact_singleton (x := x)) hU
    (singleton_subset_iff.2 hx)
  have hloc : ∀ f : E n → ℝ, (fun y => χ y * f y) =ᶠ[𝓝 x] f := fun f =>
    (hχ1 x rfl).mono fun y hy => by simp [hy]
  have hsub : (fun y => χ y * (fun y => u y - v y) y) =
      fun y => (fun y => χ y * u y) y - (fun y => χ y * v y) y := by
    funext y
    ring
  rw [← box_congr (hloc _), hsub, box_sub hg hdet (contDiff_mul_of_tsupport_subset hU hχ hχU hu)
    (contDiff_mul_of_tsupport_subset hU hχ hχU hv), box_congr (hloc u), box_congr (hloc v)]

end Box

/-! ### The vanishing lemma -/

section Vanishing

variable {g : MatrixField n} {Y : E n → E n} {ψ : E n → ℝ}

/-- `A_τ` contains the causal future of each of its subsets. -/
lemma IsCauchyTemporal.causalFutureSet_subset_A (hg : IsSpacetime g Y)
    (hψ : IsCauchyTemporal g Y ψ) {τ : ℝ} {S : Set (E n)} (hS : S ⊆ A ψ τ) :
    causalFutureSet g Y S ⊆ A ψ τ := by
  intro x hx
  obtain ⟨p, hp, hpx⟩ := mem_causalFutureSet.1 hx
  exact hψ.mem_A_of_causalLE hg (hS hp) (mem_causalFuture.1 hpx)

/-- **Vanishing lemma** (the argument of `lem_propagation`): a function smooth on `A_τ`,
solving `□_g z = 0` there and vanishing on `A_τ` outside the compact set `W`, vanishes on
`A_τ`. -/
theorem eqOn_zero_of_box_eq_zero (hg : IsSpacetime g Y) (hψ : IsCauchyTemporal g Y ψ)
    {W : Set (E n)} (hW : IsCompact W) {τ : ℝ} {z : E n → ℝ} (hz : ContDiffOn ℝ ∞ z (A ψ τ))
    (hbox : ∀ x ∈ A ψ τ, box g z x = 0) (hzW : ∀ x ∈ A ψ τ, x ∉ W → z x = 0) :
    ∀ x ∈ A ψ τ, z x = 0 := by
  set U := A ψ τ
  have hU : IsOpen U := isOpen_A hψ.smooth.continuous τ
  set ρ : E n → ℝ := fun x => √|(g x).det|
  have hρ : ContDiff ℝ ∞ ρ := contDiff_sqrt_abs_det hg.smooth hg.det_ne_zero
  have hρpos : ∀ x, 0 < ρ x := fun x => Real.sqrt_pos.2 (abs_pos.2 (hg.det_ne_zero x))
  have key : ∀ x ∈ U, z x * ρ x = 0 := by
    refine eqOn_zero_of_integral_mul_eq_zero_of_continuousOn hU
      (hz.continuousOn.mul hρ.continuous.continuousOn) fun ϑ hϑ hϑc hϑU => ?_
    set S := tsupport ϑ
    have hS : IsCompact S := hϑc
    set χ := retarded g Y ϑ
    have hJU : causalFutureSet g Y S ⊆ U := hψ.causalFutureSet_subset_A hg hϑU
    set K' := causalFutureSet g Y S ∩ causalPastSet g Y W
    have hK' : IsCompact K' := Facts.isCompact_causalFutureSet_inter_causalPastSet hg hS hW
    obtain ⟨ζ, hζ, -, hζc, hζU, hζ1⟩ := exists_cutoff (hK'.union hS) hU
      (union_subset (inter_subset_left.trans hJU) hϑU)
    obtain ⟨ζ₂, hζ₂, -, -, hζ₂U, hζ₂1⟩ := exists_cutoff hζc hU hζU
    set ϑ₁ : E n → ℝ := fun x => ζ x * χ x
    have hϑ₁ : ContDiff ℝ ∞ ϑ₁ := hζ.mul contDiff_retarded
    set u : E n → ℝ := fun x => ζ₂ x * z x
    have hu : ContDiff ℝ ∞ u := contDiff_mul_of_tsupport_subset hU hζ₂ hζ₂U hz
    have htsϑ₁ : tsupport ϑ₁ ⊆ tsupport ζ := tsupport_mul_subset_left
    have hcpt : IsCompact (tsupport u ∩ tsupport ϑ₁) :=
      hζc.of_isClosed_subset ((isClosed_tsupport _).inter (isClosed_tsupport _))
        (inter_subset_right.trans htsϑ₁)
    have hG := integral_mul_box_comm_of_isCompact hg.smooth hg.symm hg.det_ne_zero hu hϑ₁ hcpt
    have hR : ∀ x, ϑ₁ x * box g u x * ρ x = 0 := by
      intro x
      by_cases hx : x ∈ tsupport ζ
      · have : u =ᶠ[𝓝 x] z := (hζ₂1 x hx).mono fun y hy => by simp [u, hy]
        rw [box_congr this, hbox x (hζU hx)]
        ring
      · simp [ϑ₁, image_eq_zero_of_notMem_tsupport hx]
    have hL : ∀ x, u x * box g ϑ₁ x * ρ x = ϑ x * (z x * ρ x) := by
      intro x
      by_cases hxU : x ∈ U
      swap
      · have h1 : ζ₂ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hxU (hζ₂U h)
        have h2 : ϑ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hxU (hϑU h)
        simp [u, h1, h2]
      by_cases hxW : x ∈ W
      swap
      · simp [u, hzW x hxU hxW]
      by_cases hxJ : x ∈ causalFutureSet g Y S
      · have hxK : x ∈ K' := ⟨hxJ, subset_causalPastSet W hxW⟩
        have hζx := hζ1 x (Or.inl hxK)
        have : ϑ₁ =ᶠ[𝓝 x] χ := hζx.mono fun y hy => by simp [ϑ₁, hy]
        have hxζ : x ∈ tsupport ζ := subset_tsupport _ (by
          rw [mem_support, hζx.eq_of_nhds]
          simp)
        rw [box_congr this, box_retarded hg hϑ hϑc]
        simp only [u, (hζ₂1 x hxζ).eq_of_nhds, Pi.one_apply]
        ring
      · have h0 : ϑ₁ =ᶠ[𝓝 x] 0 :=
          (retarded_eventuallyEq_zero hxJ).mono fun y hy => by simp [ϑ₁, χ, hy]
        have h2 : ϑ x = 0 :=
          image_eq_zero_of_notMem_tsupport fun h => hxJ (subset_causalFutureSet S h)
        rw [box_eq_zero_of_eventuallyEq h0, h2]
        ring
    calc ∫ x, ϑ x * (z x * ρ x) = ∫ x, u x * box g ϑ₁ x * ρ x :=
          integral_congr_ae (Eventually.of_forall fun x => (hL x).symm)
      _ = ∫ x, ϑ₁ x * box g u x * ρ x := hG
      _ = 0 := by simp [hR]
  intro x hx
  exact (mul_eq_zero.1 (key x hx)).resolve_right (hρpos x).ne'

end Vanishing

/-! ### Propagation of identities -/

namespace ExtensionProperty

variable {g g' : MatrixField n} {Y Y' : E n → E n} {ψ : E n → ℝ} {τ : ℝ}
  {Ψ : E n → E n}

/-- `□_g (v' ∘ Ψ) = (□_{g'} v') ∘ Ψ` on `A_τ`. -/
theorem box_comp_eq {W : Set (E n)} (hP : ExtensionProperty g g' ψ W τ Ψ) (hg : IsSpacetime g Y)
    (hg' : IsSpacetime g' Y') (hψ : Continuous ψ) {v' : E n → ℝ} (hv' : ContDiff ℝ ∞ v')
    {x : E n} (hx : x ∈ A ψ τ) : box g (fun y => v' (Ψ y)) x = box g' v' (Ψ x) := by
  have hU := isOpen_A hψ τ
  exact box_comp_of_pullback ((hP.smooth.contDiffAt (hU.mem_nhds hx)).of_le (by simp))
    (det_ne_zero_of_pullback (hP.pullback x hx) (hg.det_ne_zero x))
    (fun i j => (hg'.smooth i j).differentiable (by simp) _) (hg'.det_ne_zero _)
    (eventually_of_mem (hU.mem_nhds hx) hP.pullback) (hv'.contDiffAt.of_le (by simp))

/-- A solution `v` of `□_g v = 0` on `A_τ` which agrees with a solution `v'` of `□_{g'} v' = 0`
on `A_τ \ W` is `v' ∘ Ψ` on `A_τ`. -/
theorem eqOn_comp {W : Set (E n)} (hP : ExtensionProperty g g' ψ W τ Ψ) (hg : IsSpacetime g Y)
    (hg' : IsSpacetime g' Y') (hψ : IsCauchyTemporal g Y ψ) (hW : IsCompact W) {v v' : E n → ℝ}
    (hv : ContDiffOn ℝ ∞ v (A ψ τ)) (hbox : ∀ x ∈ A ψ τ, box g v x = 0)
    (hv' : ContDiff ℝ ∞ v') (hbox' : ∀ x, box g' v' x = 0)
    (hvW : ∀ x ∈ A ψ τ, x ∉ W → v x = v' x) : ∀ x ∈ A ψ τ, v x = v' (Ψ x) := by
  have hU := isOpen_A hψ.smooth.continuous τ
  have hcomp : ContDiffOn ℝ ∞ (fun y => v' (Ψ y)) (A ψ τ) := hv'.comp_contDiffOn hP.smooth
  have := eqOn_zero_of_box_eq_zero hg hψ hW (z := fun y => v y - v' (Ψ y)) (hv.sub hcomp)
    (fun x hx => by
      rw [box_sub_of_contDiffOn hg.smooth hg.det_ne_zero hU hv hcomp hx, hbox x hx,
        hP.box_comp_eq hg hg' hψ.smooth.continuous hv' hx, hbox', sub_self])
    fun x hx hxW => by simp only [hP.eq_self x hx hxW, hvW x hx hxW, sub_self]
  exact fun x hx => sub_eq_zero.1 (this x hx)

/-- **Propagation of identities** (blueprint, Lemma `lem_propagation`(b)): under `P(τ)`, the
transfer `𝒯 v'` of a solution of `□_{g'} v' = 0` is `v' ∘ Ψ` on `A_τ`. -/
theorem transfer_eq_comp {T : ℝ} (hP : ExtensionProperty g g' ψ (W n T) τ Ψ)
    (hgA : IsAdmissibleMetric n T g) (hg'A : IsAdmissibleMetric n T g')
    (hg : IsSpacetime g Y) (hg' : IsSpacetime g' Y')
    (hY : ∀ x ∉ M0 n T, form (g x) (EuclideanSpace.single 0 1) (Y x) < 0)
    (hY' : ∀ x ∉ M0 n T, form (g' x) (EuclideanSpace.single 0 1) (Y' x) < 0)
    (hC : CauchyDataSubset n T g g') (hψ : IsCauchyTemporal g Y ψ) {v' : E n → ℝ}
    (hv' : ContDiff ℝ ∞ v') (hbox' : ∀ x, box g' v' x = 0) :
    ∀ x ∈ A ψ τ, transfer n T g v' x = v' (Ψ x) := by
  obtain ⟨h1, h2, h3⟩ := transfer_spec hgA hg'A hg hg' hY hY' hC hv' hbox'
  exact hP.eqOn_comp hg hg' hψ isCompact_W h1.contDiffOn (fun x _ => h2 x) hv' hbox'
    fun x _ hxW => h3 x (mem_O.2 hxW)

end ExtensionProperty

end

end LorentzianCalderon
