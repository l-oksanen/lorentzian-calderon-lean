module

public import LorentzianCalderon.Induction.Frontier
public import LorentzianCalderon.Waves.Source
public import LorentzianCalderon.Setting.Data

public section

/-!
# Propagation of identities for sources in `O`

Blueprint, Lemma `lem_propagation`, part (a): under `P(τ)`, `G^ret_g F = Ψ^* G^ret_{g'} F` on
`A_τ` for sources `F` supported in `O`.

* Smooth sources (`ExtensionProperty.retarded_eq_comp`): `z = G^ret_g f - (G^ret_{g'} f) ∘ Ψ`
  solves `□_g z = 0` on `A_τ` (naturality, and `f ∘ Ψ = f` there by no escape) and vanishes on
  `A_τ \ W` (the data), so the vanishing lemma applies.
* Pull-backs of distributions are only used on the sources of local inverses `φ` of `Ψ`, through
  the push-forward `ϑ̃ = ϑ ∘ φ⁻¹` of test functions (`pushforward`). By duality and the change of
  variables formula, `G^adv_g ϑ = G^adv_{g'} ϑ̃` on `O`
  (`ExtensionProperty.advanced_eq_pushforward`), hence `⟨G^ret_g F, ϑ⟩ = ⟨G^ret_{g'} F, ϑ̃⟩`
  for sources `F` supported in `O` (`ExtensionProperty.retardedS_eq_pushforward`).
* Agreement of `G^ret_{g'} F` with a function `u'` on an open set `N` thus propagates to
  agreement of `G^ret_g F` with `u' ∘ Ψ`, near each point (`exists_agreesOn_retardedS_comp`) and,
  by a partition of unity, on all of `A_τ ∩ Ψ⁻¹(N)` (`agreesOn_retardedS_comp`).
-/

namespace LorentzianCalderon

noncomputable section
open MeasureTheory Set Filter Function
open scoped ContDiff Matrix Topology

variable {n : ℕ}

/-! ### Push-forward of test functions under a local diffeomorphism -/

section Pushforward

variable (φ : OpenPartialHomeomorph (E n) (E n))

/-- The push-forward `ϑ ∘ φ⁻¹` of a function on `φ.source`, extended by zero outside
`φ.target`. -/
def pushforward (ϑ : E n → ℝ) : E n → ℝ :=
  φ.target.indicator (ϑ ∘ φ.symm)

variable {φ} {ϑ : E n → ℝ}

lemma pushforward_apply_of_mem {y : E n} (hy : y ∈ φ.target) :
    pushforward φ ϑ y = ϑ (φ.symm y) :=
  indicator_of_mem hy _

lemma pushforward_apply_self {x : E n} (hx : x ∈ φ.source) : pushforward φ ϑ (φ x) = ϑ x := by
  rw [pushforward_apply_of_mem (φ.map_source hx), φ.left_inv hx]

lemma support_pushforward_subset : support (pushforward φ ϑ) ⊆ φ '' support ϑ := by
  intro y hy
  by_cases hyt : y ∈ φ.target
  · rw [mem_support, pushforward_apply_of_mem hyt] at hy
    exact ⟨φ.symm y, hy, φ.right_inv hyt⟩
  · exact absurd (indicator_of_notMem hyt _) hy

variable (hϑ' : HasCompactSupport ϑ) (hϑs : tsupport ϑ ⊆ φ.source)
include hϑ' hϑs

lemma isCompact_image_tsupport : IsCompact (φ '' tsupport ϑ) :=
  hϑ'.isCompact.image_of_continuousOn (φ.continuousOn.mono hϑs)

lemma tsupport_pushforward_subset : tsupport (pushforward φ ϑ) ⊆ φ '' tsupport ϑ :=
  closure_minimal (support_pushforward_subset.trans (image_mono (subset_tsupport ϑ)))
    (isCompact_image_tsupport hϑ' hϑs).isClosed

lemma tsupport_pushforward_subset_target : tsupport (pushforward φ ϑ) ⊆ φ.target :=
  (tsupport_pushforward_subset hϑ' hϑs).trans
    ((image_mono hϑs).trans φ.image_source_eq_target.subset)

lemma hasCompactSupport_pushforward : HasCompactSupport (pushforward φ ϑ) :=
  (isCompact_image_tsupport hϑ' hϑs).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_pushforward_subset hϑ' hϑs)

lemma contDiff_pushforward (hϑ : ContDiff ℝ ∞ ϑ) (hsymm : ContDiffOn ℝ ∞ φ.symm φ.target) :
    ContDiff ℝ ∞ (pushforward φ ϑ) := by
  refine contDiff_iff_contDiffAt.2 fun y => ?_
  by_cases hyt : y ∈ φ.target
  · have hev : ϑ ∘ φ.symm =ᶠ[𝓝 y] pushforward φ ϑ :=
      eventually_of_mem (φ.open_target.mem_nhds hyt) fun z hz =>
        (pushforward_apply_of_mem hz).symm
    exact (hϑ.contDiffAt.comp y
      (hsymm.contDiffAt (φ.open_target.mem_nhds hyt))).congr_of_eventuallyEq hev.symm
  · have hyK : y ∉ φ '' tsupport ϑ := fun h =>
      hyt ((image_mono hϑs).trans φ.image_source_eq_target.subset h)
    have hev : pushforward φ ϑ =ᶠ[𝓝 y] fun _ => 0 :=
      eventually_of_mem ((isCompact_image_tsupport hϑ' hϑs).isClosed.isOpen_compl.mem_nhds hyK)
        fun z hz => image_eq_zero_of_notMem_tsupport fun h =>
          hz (tsupport_pushforward_subset hϑ' hϑs h)
    exact contDiffAt_const.congr_of_eventuallyEq hev

end Pushforward

/-! ### Locality of agreement -/

section Locality

variable {U : (E n → ℝ) → ℝ}

lemma map_sum_of_map_add
    (hadd : ∀ h₁ h₂ : E n → ℝ, ContDiff ℝ ∞ h₁ → HasCompactSupport h₁ → ContDiff ℝ ∞ h₂ →
      HasCompactSupport h₂ → U (h₁ + h₂) = U h₁ + U h₂)
    {ι : Type*} (s : Finset ι) {φ : ι → E n → ℝ} (hφ : ∀ i, ContDiff ℝ ∞ (φ i))
    (hφ' : ∀ i, HasCompactSupport (φ i)) :
    U (∑ i ∈ s, φ i) = ∑ i ∈ s, U (φ i) ∧ ContDiff ℝ ∞ (∑ i ∈ s, φ i) ∧
      HasCompactSupport (∑ i ∈ s, φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 := hadd 0 0 contDiff_zero_fun HasCompactSupport.zero contDiff_zero_fun
      HasCompactSupport.zero
    simp only [add_zero, left_eq_add] at h0
    simpa [h0] using ⟨contDiff_zero_fun (𝕜 := ℝ) (E := E n) (F := ℝ) (n := ∞),
      HasCompactSupport.zero (α := E n) (β := ℝ)⟩
  | insert a s ha ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ⟨by rw [hadd _ _ (hφ a) (hφ' a) h2 h3, h1], (hφ a).add h2, (hφ' a).add h3⟩

/-- Agreement of an additive functional with a locally integrable function is a local
property. -/
theorem agreesOn_of_forall_exists {g : MatrixField n}
    (hρ : Continuous fun x => √|(g x).det|)
    (hadd : ∀ h₁ h₂ : E n → ℝ, ContDiff ℝ ∞ h₁ → HasCompactSupport h₁ → ContDiff ℝ ∞ h₂ →
      HasCompactSupport h₂ → U (h₁ + h₂) = U h₁ + U h₂)
    {u : E n → ℝ} {V : Set (E n)} (hu : LocallyIntegrableOn u V)
    (hloc : ∀ x ∈ V, ∃ V', IsOpen V' ∧ x ∈ V' ∧ AgreesOn g U u V') : AgreesOn g U u V := by
  refine agreesOn_iff.2 fun h hh hh' hhV => ?_
  choose V' hV'o hxV' hag using hloc
  have hK : IsCompact (tsupport h) := hh'
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : tsupport h => V' x.1 (hhV x.2))
    (fun x => hV'o _ _) fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hxV' _ _⟩
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate (modelWithCornersSelf ℝ (E n))
    (isClosed_tsupport h) (fun i : t => V' i.1.1 (hhV i.1.2)) (fun i => hV'o _ _)
    fun x hx => by
      obtain ⟨i, hi, hx⟩ := mem_iUnion₂.1 (ht hx)
      exact mem_iUnion.2 ⟨⟨i, hi⟩, hx⟩
  set φ : t → E n → ℝ := fun i x => f i x * h x
  have hfs : ∀ i, ContDiff ℝ ∞ (f i) := fun i => contMDiff_iff_contDiff.1 (f i).contMDiff
  have hφ : ∀ i, ContDiff ℝ ∞ (φ i) := fun i => (hfs i).mul hh
  have hφ' : ∀ i, HasCompactSupport (φ i) := fun i => hh'.mul_left
  have hsum : h = ∑ i, φ i := by
    funext x
    rw [Finset.sum_apply]
    by_cases hx : x ∈ tsupport h
    · have := f.sum_eq_one hx
      rw [finsum_eq_sum_of_fintype] at this
      simp only [φ, ← Finset.sum_mul, this, one_mul]
    · simp [φ, image_eq_zero_of_notMem_tsupport hx]
  have hint : ∀ i, Integrable fun x => u x * φ i x * √|(g x).det| := by
    intro i
    have := (hu.integrableOn_compact_subset hhV hK).mul_continuousOn
      (((hφ i).continuous.mul hρ).continuousOn) hK
    refine (this.integrable_of_forall_notMem_eq_zero fun x hx => ?_).congr
      (Eventually.of_forall fun x => by simp only [Pi.mul_apply]; ring)
    simp [φ, image_eq_zero_of_notMem_tsupport hx]
  rw [hsum, (map_sum_of_map_add hadd Finset.univ hφ hφ').1,
    Finset.sum_congr rfl fun i _ => agreesOn_iff.1 (hag _ _) _ (hφ i) (hφ' i)
      (tsupport_mul_subset_left.trans (hf i)),
    ← integral_finsetSum _ fun i _ => hint i]
  congr 1
  funext x
  simp [Finset.sum_apply, Finset.mul_sum, Finset.sum_mul]

end Locality

/-! ### Change of variables -/

lemma det_fderiv_eq_det_D (Ψ : E n → E n) (x : E n) :
    LinearMap.det (fderiv ℝ Ψ x : E n →ₗ[ℝ] E n) = (D Ψ x).det := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis]
  congr 1
  ext i j
  rw [D_def]
  rfl

lemma sqrt_abs_det_pullback {G G' J : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (h : G = Jᵀ * G' * J) : √|G.det| = |J.det| * √|G'.det| := by
  rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    show J.det * G'.det * J.det = |J.det| ^ 2 * G'.det by rw [sq_abs]; ring, abs_mul,
    abs_of_nonneg (sq_nonneg _), Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (abs_nonneg _)]

namespace ExtensionProperty

variable {T : ℝ} {g g' : MatrixField n} {Y Y' : E n → E n} {ψ : E n → ℝ} {τ : ℝ}
  {Ψ : E n → E n} {Φ : ℝ → E n → E n}

/-- A test function supported in `O` is invariant under `Ψ` on `A_τ`. -/
theorem comp_eq_of_tsupport_subset_O (hP : ExtensionProperty g g' ψ (W n T) τ Ψ)
    (hgA : IsAdmissibleMetric n T g) (hg'A : IsAdmissibleMetric n T g')
    (hg : IsSpacetime g Y) (hg' : IsSpacetime g' Y')
    (hY : ∀ x ∉ M0 n T, form (g x) (EuclideanSpace.single 0 1) (Y x) < 0)
    (hY' : ∀ x ∉ M0 n T, form (g' x) (EuclideanSpace.single 0 1) (Y' x) < 0)
    (hψ : IsCauchyTemporal g Y ψ) (hΦ : Continuous fun p : ℝ × E n => Φ p.1 p.2)
    (hΦ0 : ∀ x, Φ 0 x = x) (hΦψ : ∀ t x, ψ (Φ t x) = ψ x + t) {f : E n → ℝ}
    (hfO : tsupport f ⊆ O n T) {x : E n} (hx : x ∈ A ψ τ) : f (Ψ x) = f x := by
  by_cases hxW : x ∈ W n T
  · have hΨx := hP.mapsTo_W_of_admissible hgA hg'A hg hg' hY hY' hψ hΦ hΦ0 hΦψ ⟨hx, hxW⟩
    rw [image_eq_zero_of_notMem_tsupport fun h => mem_O.1 (hfO h) hΨx,
      image_eq_zero_of_notMem_tsupport fun h => mem_O.1 (hfO h) hxW]
  · rw [hP.eq_self x hx hxW]

/-- **Propagation of identities** (blueprint, Lemma `lem_propagation`(a)) for smooth sources:
under `P(τ)`, `G^ret_g f = (G^ret_{g'} f) ∘ Ψ` on `A_τ` for test functions `f` supported in
`O`. -/
theorem retarded_eq_comp (hP : ExtensionProperty g g' ψ (W n T) τ Ψ)
    (hgA : IsAdmissibleMetric n T g) (hg'A : IsAdmissibleMetric n T g')
    (hg : IsSpacetime g Y) (hg' : IsSpacetime g' Y')
    (hY : ∀ x ∉ M0 n T, form (g x) (EuclideanSpace.single 0 1) (Y x) < 0)
    (hY' : ∀ x ∉ M0 n T, form (g' x) (EuclideanSpace.single 0 1) (Y' x) < 0)
    (hC : CauchyDataSubset n T g g') (hψ : IsCauchyTemporal g Y ψ)
    (hΦ : Continuous fun p : ℝ × E n => Φ p.1 p.2) (hΦ0 : ∀ x, Φ 0 x = x)
    (hΦψ : ∀ t x, ψ (Φ t x) = ψ x + t) {f : E n → ℝ} (hf : ContDiff ℝ ∞ f)
    (hf' : HasCompactSupport f) (hfO : tsupport f ⊆ O n T) :
    ∀ x ∈ A ψ τ, retarded g Y f x = retarded g' Y' f (Ψ x) := by
  have hU := isOpen_A hψ.smooth.continuous τ
  have hcomp : ContDiffOn ℝ ∞ (fun y => retarded g' Y' f (Ψ y)) (A ψ τ) :=
    contDiff_retarded.comp_contDiffOn hP.smooth
  have := eqOn_zero_of_box_eq_zero hg hψ isCompact_W
    (z := fun y => retarded g Y f y - retarded g' Y' f (Ψ y))
    (contDiff_retarded.contDiffOn.sub hcomp)
    (fun x hx => by
      rw [box_sub_of_contDiffOn hg.smooth hg.det_ne_zero hU contDiff_retarded.contDiffOn hcomp hx,
        box_retarded hg hf hf', hP.box_comp_eq hg hg' hψ.smooth.continuous contDiff_retarded hx,
        box_retarded hg' hf hf',
        hP.comp_eq_of_tsupport_subset_O hgA hg'A hg hg' hY hY' hψ hΦ hΦ0 hΦψ hfO hx, sub_self])
    fun x hx hxW => by
      have hxM : x ∉ M0 n T := fun h => hxW (M0_subset_W h)
      rw [hP.eq_self x hx hxW, retarded_eq_of_cauchyDataSubset hgA hg'A hg hg' hY hY' hC hf hf'
        (hfO.trans fun y hy => not_mem_M0_of_mem_O hy) hxM, sub_self]
  exact fun x hx => sub_eq_zero.1 (this x hx)

/-- **Change of variables** through a local inverse of `Ψ`, using
`√|det g| = |det DΨ| √|det g'| ∘ Ψ`: `∫ u ϑ̃ dV_{g'} = ∫ (u ∘ Ψ) ϑ dV_g` for the push-forward
`ϑ̃` of `ϑ`, for any function `u`. -/
theorem integral_pushforward {W : Set (E n)} (hP : ExtensionProperty g g' ψ W τ Ψ)
    (hψ : Continuous ψ) {φ : OpenPartialHomeomorph (E n) (E n)} (hφ : ⇑φ = Ψ)
    (hφA : φ.source ⊆ A ψ τ) {ϑ : E n → ℝ} (hϑs : support ϑ ⊆ φ.source) (u : E n → ℝ) :
    ∫ y, u y * pushforward φ ϑ y * √|(g' y).det| = ∫ x, u (Ψ x) * ϑ x * √|(g x).det| := by
  have hUA := isOpen_A hψ τ
  have hs := φ.open_source.measurableSet
  have himg : Ψ '' φ.source = φ.target := by
    rw [← hφ]
    exact φ.image_source_eq_target
  have hcv := integral_image_eq_integral_abs_det_fderiv_smul volume hs (f := Ψ)
    (f' := fun x => fderiv ℝ Ψ x)
    (fun x hx => ((hP.smooth.contDiffAt (hUA.mem_nhds (hφA hx))).differentiableAt
      (by simp)).hasFDerivAt.hasFDerivWithinAt) (hφ ▸ φ.injOn)
    (fun y => u y * pushforward φ ϑ y * √|(g' y).det|)
  rw [himg] at hcv
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := φ.target)
      fun y hy => by simp [pushforward, indicator_of_notMem hy],
    hcv]
  conv_rhs => rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := φ.source)
      fun x hx => by simp [notMem_support.1 fun h => hx (hϑs h)]]
  refine setIntegral_congr_fun hs fun x hx => ?_
  have hpush : pushforward φ ϑ (Ψ x) = ϑ x := hφ ▸ pushforward_apply_self hx
  simp only [smul_eq_mul, hpush, sqrt_abs_det_pullback (hP.pullback x (hφA hx)),
    ContinuousLinearMap.det, det_fderiv_eq_det_D]
  ring

/-- Local inverses of `Ψ` near points of `A_τ`, with image in a given neighbourhood of the
image point. -/
theorem exists_openPartialHomeomorph {W : Set (E n)} (hP : ExtensionProperty g g' ψ W τ Ψ)
    (hg : ∀ x, IsLorentzian (g x)) (hψ : Continuous ψ) {x₀ : E n} (hx₀ : x₀ ∈ A ψ τ)
    {N : Set (E n)} (hN : IsOpen N) (hx₀N : Ψ x₀ ∈ N) :
    ∃ φ : OpenPartialHomeomorph (E n) (E n), ⇑φ = Ψ ∧ x₀ ∈ φ.source ∧ φ.source ⊆ A ψ τ ∧
      φ.target ⊆ N ∧ ContDiffOn ℝ ∞ φ.symm φ.target := by
  have hU := hP.smooth.continuousOn.isOpen_inter_preimage (isOpen_A hψ τ) hN
  obtain ⟨φ, hφ, hx, hsU, hsm, -⟩ := exists_localInverse hU (hP.smooth.mono inter_subset_left)
    (fun z hz => hP.injective_fderiv hg hz.1) ⟨hx₀, hx₀N⟩
  refine ⟨φ, hφ, hx, hsU.trans inter_subset_left, ?_, hsm⟩
  rw [← φ.image_source_eq_target]
  rintro _ ⟨x, hx, rfl⟩
  rw [hφ]
  exact (hsU hx).2

/-- Pairings with test functions supported in `O` do not see the volume density. -/
lemma integral_mul_sqrt_det_of_tsupport_subset_O {G : MatrixField n}
    (hG : IsAdmissibleMetric n T G) {h : E n → ℝ} (hO : tsupport h ⊆ O n T) (a : E n → ℝ) :
    ∫ x, h x * a x * √|(G x).det| = ∫ x, h x * a x := by
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ tsupport h
  · simp [hG.minkowski_exterior x (not_mem_M0_of_mem_O (hO hx)), sqrt_abs_det_minkowski]
  · simp [image_eq_zero_of_notMem_tsupport hx]

/-- **Advanced solutions under local inverses**: under `P(τ)`, for a local inverse `φ` of `Ψ`
on an open subset of `A_τ` and a test function `ϑ` supported there, `G^adv_g ϑ` and
`G^adv_{g'}` of the push-forward of `ϑ` agree on `O`. -/
theorem advanced_eq_pushforward (hP : ExtensionProperty g g' ψ (W n T) τ Ψ)
    (hgA : IsAdmissibleMetric n T g) (hg'A : IsAdmissibleMetric n T g')
    (hg : IsSpacetime g Y) (hg' : IsSpacetime g' Y')
    (hY : ∀ x ∉ M0 n T, form (g x) (EuclideanSpace.single 0 1) (Y x) < 0)
    (hY' : ∀ x ∉ M0 n T, form (g' x) (EuclideanSpace.single 0 1) (Y' x) < 0)
    (hC : CauchyDataSubset n T g g') (hψ : IsCauchyTemporal g Y ψ)
    (hΦ : Continuous fun p : ℝ × E n => Φ p.1 p.2) (hΦ0 : ∀ x, Φ 0 x = x)
    (hΦψ : ∀ t x, ψ (Φ t x) = ψ x + t) {φ : OpenPartialHomeomorph (E n) (E n)} (hφ : ⇑φ = Ψ)
    (hφA : φ.source ⊆ A ψ τ) (hsymm : ContDiffOn ℝ ∞ φ.symm φ.target) {ϑ : E n → ℝ}
    (hϑ : ContDiff ℝ ∞ ϑ) (hϑ' : HasCompactSupport ϑ) (hϑs : tsupport ϑ ⊆ φ.source) :
    ∀ y ∈ O n T, advanced g Y ϑ y = advanced g' Y' (pushforward φ ϑ) y := by
  have hϑ₁ := contDiff_pushforward hϑ' hϑs hϑ hsymm
  have hϑ₁' := hasCompactSupport_pushforward hϑ' hϑs
  refine fun y hy => sub_eq_zero.1 (eqOn_zero_of_integral_mul_eq_zero isOpen_O
    (contDiff_advanced.continuous.sub contDiff_advanced.continuous) (fun h hh hh' hhO => ?_) y hy)
  have key : ∫ x, h x * advanced g Y ϑ x = ∫ x, h x * advanced g' Y' (pushforward φ ϑ) x := by
    rw [← integral_mul_sqrt_det_of_tsupport_subset_O hgA hhO (advanced g Y ϑ),
      ← integral_mul_sqrt_det_of_tsupport_subset_O hg'A hhO (advanced g' Y' (pushforward φ ϑ)),
      ← integral_retarded_mul hg hh hh' hϑ hϑ', ← integral_retarded_mul hg' hh hh' hϑ₁ hϑ₁',
      hP.integral_pushforward hψ.smooth.continuous hφ hφA ((subset_tsupport ϑ).trans hϑs)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ φ.source
    · simp only
      rw [hP.retarded_eq_comp hgA hg'A hg hg' hY hY' hC hψ hΦ hΦ0 hΦψ hh hh' hhO x (hφA hx)]
    · simp [image_eq_zero_of_notMem_tsupport fun h => hx (hϑs h)]
  have hi : ∀ a : E n → ℝ, ContDiff ℝ ∞ a → Integrable fun x => h x * a x := fun a ha =>
    (hh.continuous.mul ha.continuous).integrable_of_hasCompactSupport hh'.mul_right
  show ∫ x, h x * (advanced g Y ϑ x - advanced g' Y' (pushforward φ ϑ) x) = 0
  simp only [mul_sub]
  rw [integral_sub (hi _ contDiff_advanced) (hi _ contDiff_advanced), key, sub_self]

/-- **Propagation of identities** for sources supported in `O` (blueprint, Lemma
`lem_propagation`(a)), tested against a test function `ϑ` supported in the source of a local
inverse `φ` of `Ψ`: `⟨G^ret_g F, ϑ⟩ = ⟨G^ret_{g'} F, ϑ̃⟩` for the push-forward `ϑ̃` of `ϑ`. -/
theorem retardedS_eq_pushforward (hP : ExtensionProperty g g' ψ (W n T) τ Ψ)
    (hgA : IsAdmissibleMetric n T g) (hg'A : IsAdmissibleMetric n T g')
    (hg : IsSpacetime g Y) (hg' : IsSpacetime g' Y')
    (hY : ∀ x ∉ M0 n T, form (g x) (EuclideanSpace.single 0 1) (Y x) < 0)
    (hY' : ∀ x ∉ M0 n T, form (g' x) (EuclideanSpace.single 0 1) (Y' x) < 0)
    (hC : CauchyDataSubset n T g g') (hψ : IsCauchyTemporal g Y ψ)
    (hΦ : Continuous fun p : ℝ × E n => Φ p.1 p.2) (hΦ0 : ∀ x, Φ 0 x = x)
    (hΦψ : ∀ t x, ψ (Φ t x) = ψ x + t) {F : (E n → ℝ) → ℝ} {K : Set (E n)}
    (hF : IsSource F K) (hKO : K ⊆ O n T) {φ : OpenPartialHomeomorph (E n) (E n)} (hφ : ⇑φ = Ψ)
    (hφA : φ.source ⊆ A ψ τ) (hsymm : ContDiffOn ℝ ∞ φ.symm φ.target) {ϑ : E n → ℝ}
    (hϑ : ContDiff ℝ ∞ ϑ) (hϑ' : HasCompactSupport ϑ) (hϑs : tsupport ϑ ⊆ φ.source) :
    retardedS g Y F ϑ = retardedS g' Y' F (pushforward φ ϑ) := by
  rw [retardedS_def, retardedS_def]
  exact hF.congr contDiff_advanced contDiff_advanced (eventually_of_mem (isOpen_O.mem_nhdsSet.2 hKO)
    (hP.advanced_eq_pushforward hgA hg'A hg hg' hY hY' hC hψ hΦ hΦ0 hΦψ hφ hφA hsymm hϑ hϑ' hϑs))

/-- If `G^ret_{g'} F` agrees with `u'` on the open set `N`, then `G^ret_g F` agrees with
`u' ∘ Ψ` on the source of each local inverse `φ` of `Ψ` with image in `N`. -/
theorem agreesOn_retardedS_comp_of_openPartialHomeomorph (hP : ExtensionProperty g g' ψ (W n T) τ Ψ)
    (hgA : IsAdmissibleMetric n T g) (hg'A : IsAdmissibleMetric n T g')
    (hg : IsSpacetime g Y) (hg' : IsSpacetime g' Y')
    (hY : ∀ x ∉ M0 n T, form (g x) (EuclideanSpace.single 0 1) (Y x) < 0)
    (hY' : ∀ x ∉ M0 n T, form (g' x) (EuclideanSpace.single 0 1) (Y' x) < 0)
    (hC : CauchyDataSubset n T g g') (hψ : IsCauchyTemporal g Y ψ)
    (hΦ : Continuous fun p : ℝ × E n => Φ p.1 p.2) (hΦ0 : ∀ x, Φ 0 x = x)
    (hΦψ : ∀ t x, ψ (Φ t x) = ψ x + t) {F : (E n → ℝ) → ℝ} {K : Set (E n)}
    (hF : IsSource F K) (hKO : K ⊆ O n T) {N : Set (E n)} {u' : E n → ℝ}
    (hu' : AgreesOn g' (retardedS g' Y' F) u' N) {φ : OpenPartialHomeomorph (E n) (E n)}
    (hφ : ⇑φ = Ψ) (hφA : φ.source ⊆ A ψ τ) (hφN : φ.target ⊆ N)
    (hsymm : ContDiffOn ℝ ∞ φ.symm φ.target) :
    AgreesOn g (retardedS g Y F) (fun x => u' (Ψ x)) φ.source := by
  refine agreesOn_iff.2 fun ϑ hϑ hϑ' hϑs => ?_
  rw [hP.retardedS_eq_pushforward hgA hg'A hg hg' hY hY' hC hψ hΦ hΦ0 hΦψ hF hKO hφ hφA hsymm
      hϑ hϑ' hϑs,
    (agreesOn_iff.1 hu') _ (contDiff_pushforward hϑ' hϑs hϑ hsymm)
      (hasCompactSupport_pushforward hϑ' hϑs)
      ((tsupport_pushforward_subset_target hϑ' hϑs).trans hφN),
    hP.integral_pushforward hψ.smooth.continuous hφ hφA ((subset_tsupport ϑ).trans hϑs)]

/-- If `G^ret_{g'} F` agrees with `u'` on an open set `N ∋ Ψ x₀`, then `G^ret_g F` agrees with
`u' ∘ Ψ` on an open neighbourhood `V ⊆ A_τ` of `x₀ ∈ A_τ`, on which `Ψ` is injective. -/
theorem exists_agreesOn_retardedS_comp (hP : ExtensionProperty g g' ψ (W n T) τ Ψ)
    (hgA : IsAdmissibleMetric n T g) (hg'A : IsAdmissibleMetric n T g')
    (hg : IsSpacetime g Y) (hg' : IsSpacetime g' Y')
    (hY : ∀ x ∉ M0 n T, form (g x) (EuclideanSpace.single 0 1) (Y x) < 0)
    (hY' : ∀ x ∉ M0 n T, form (g' x) (EuclideanSpace.single 0 1) (Y' x) < 0)
    (hC : CauchyDataSubset n T g g') (hψ : IsCauchyTemporal g Y ψ)
    (hΦ : Continuous fun p : ℝ × E n => Φ p.1 p.2) (hΦ0 : ∀ x, Φ 0 x = x)
    (hΦψ : ∀ t x, ψ (Φ t x) = ψ x + t) {F : (E n → ℝ) → ℝ} {K : Set (E n)}
    (hF : IsSource F K) (hKO : K ⊆ O n T) {N : Set (E n)} (hN : IsOpen N) {u' : E n → ℝ}
    (hu' : AgreesOn g' (retardedS g' Y' F) u' N) {x₀ : E n} (hx₀ : x₀ ∈ A ψ τ)
    (hx₀N : Ψ x₀ ∈ N) :
    ∃ V, IsOpen V ∧ x₀ ∈ V ∧ V ⊆ A ψ τ ∧ InjOn Ψ V ∧ Ψ '' V ⊆ N ∧
      AgreesOn g (retardedS g Y F) (fun x => u' (Ψ x)) V := by
  obtain ⟨φ, hφ, hx, hφA, hφN, hsymm⟩ :=
    hP.exists_openPartialHomeomorph hg.lorentzian hψ.smooth.continuous hx₀ hN hx₀N
  refine ⟨φ.source, φ.open_source, hx, hφA, hφ ▸ φ.injOn, ?_,
    hP.agreesOn_retardedS_comp_of_openPartialHomeomorph hgA hg'A hg hg' hY hY' hC hψ hΦ hΦ0 hΦψ
      hF hKO hu' hφ hφA hφN hsymm⟩
  rw [← hφ, φ.image_source_eq_target]
  exact hφN

/-- If `G^ret_{g'} F` vanishes on an open set `N ∋ Ψ x₀`, then `G^ret_g F` vanishes on an
open neighbourhood `V ⊆ A_τ` of `x₀ ∈ A_τ`. -/
theorem exists_vanishesOn_retardedS (hP : ExtensionProperty g g' ψ (W n T) τ Ψ)
    (hgA : IsAdmissibleMetric n T g) (hg'A : IsAdmissibleMetric n T g')
    (hg : IsSpacetime g Y) (hg' : IsSpacetime g' Y')
    (hY : ∀ x ∉ M0 n T, form (g x) (EuclideanSpace.single 0 1) (Y x) < 0)
    (hY' : ∀ x ∉ M0 n T, form (g' x) (EuclideanSpace.single 0 1) (Y' x) < 0)
    (hC : CauchyDataSubset n T g g') (hψ : IsCauchyTemporal g Y ψ)
    (hΦ : Continuous fun p : ℝ × E n => Φ p.1 p.2) (hΦ0 : ∀ x, Φ 0 x = x)
    (hΦψ : ∀ t x, ψ (Φ t x) = ψ x + t) {F : (E n → ℝ) → ℝ} {K : Set (E n)}
    (hF : IsSource F K) (hKO : K ⊆ O n T) {N : Set (E n)} (hN : IsOpen N)
    (hv : VanishesOn (retardedS g' Y' F) N) {x₀ : E n} (hx₀ : x₀ ∈ A ψ τ) (hx₀N : Ψ x₀ ∈ N) :
    ∃ V, IsOpen V ∧ x₀ ∈ V ∧ V ⊆ A ψ τ ∧ VanishesOn (retardedS g Y F) V := by
  obtain ⟨V, hV, hx, hVA, -, -, hagree⟩ := hP.exists_agreesOn_retardedS_comp hgA hg'A hg hg' hY
    hY' hC hψ hΦ hΦ0 hΦψ hF hKO hN ((vanishesOn_iff_agreesOn_zero (g := g')).1 hv) hx₀ hx₀N
  exact ⟨V, hV, hx, hVA, (vanishesOn_iff_agreesOn_zero (g := g)).2 hagree⟩

/-- Pull-backs by `Ψ` of locally integrable functions are locally integrable. -/
theorem locallyIntegrableOn_comp {W : Set (E n)} (hP : ExtensionProperty g g' ψ W τ Ψ)
    (hg : ∀ x, IsLorentzian (g x)) (hψ : Continuous ψ) {N : Set (E n)} (hN : IsOpen N)
    {u' : E n → ℝ} (hu' : LocallyIntegrableOn u' N) :
    LocallyIntegrableOn (fun x => u' (Ψ x)) (A ψ τ ∩ Ψ ⁻¹' N) := by
  intro x hx
  have hUA := isOpen_A hψ τ
  obtain ⟨φ, hφ, hxs, hφA, hφN, -⟩ := hP.exists_openPartialHomeomorph hg hψ hx.1 hN hx.2
  obtain ⟨K, hK, hxK, hKs⟩ := exists_compact_subset φ.open_source hxs
  refine ⟨K, mem_nhdsWithin_of_mem_nhds (mem_interior_iff_mem_nhds.1 hxK), ?_⟩
  have hKA := hKs.trans hφA
  have himg : Ψ '' K ⊆ N := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← hφ]
    exact hφN (φ.map_source (hKs hy))
  have h1 := hu'.integrableOn_compact_subset himg
    (hK.image_of_continuousOn (hP.smooth.continuousOn.mono hKA))
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hK.measurableSet
    (f' := fun x => fderiv ℝ Ψ x)
    (fun y hy => ((hP.smooth.contDiffAt (hUA.mem_nhds (hKA hy))).differentiableAt
      (by simp)).hasFDerivAt.hasFDerivWithinAt) ((hφ ▸ φ.injOn).mono hKs)] at h1
  have hdet : ∀ y ∈ K, |(fderiv ℝ Ψ y).det| ≠ 0 := fun y hy => by
    rw [abs_ne_zero, ContinuousLinearMap.det, det_fderiv_eq_det_D]
    exact det_ne_zero_of_pullback (hP.pullback y (hKA hy)) (hg y).det_neg.ne
  have hc : ContinuousOn (fun y => |(fderiv ℝ Ψ y).det|⁻¹) K :=
    ((ContinuousLinearMap.continuous_det.comp_continuousOn
      ((hP.smooth.continuousOn_fderiv_of_isOpen hUA (by simp)).mono hKA)).abs).inv₀ hdet
  refine (h1.mul_continuousOn hc hK).congr_fun (fun y hy => ?_) hK.measurableSet
  simp only [smul_eq_mul]
  field_simp [hdet y hy]

/-- **Propagation of identities** for sources supported in `O` (blueprint, Lemma
`lem_propagation`(a)): if `G^ret_{g'} F` agrees on the open set `N` with a locally integrable
function `u'`, then `G^ret_g F` agrees with `u' ∘ Ψ` on `A_τ ∩ Ψ⁻¹(N)`. -/
theorem agreesOn_retardedS_comp (hP : ExtensionProperty g g' ψ (W n T) τ Ψ)
    (hgA : IsAdmissibleMetric n T g) (hg'A : IsAdmissibleMetric n T g')
    (hg : IsSpacetime g Y) (hg' : IsSpacetime g' Y')
    (hY : ∀ x ∉ M0 n T, form (g x) (EuclideanSpace.single 0 1) (Y x) < 0)
    (hY' : ∀ x ∉ M0 n T, form (g' x) (EuclideanSpace.single 0 1) (Y' x) < 0)
    (hC : CauchyDataSubset n T g g') (hψ : IsCauchyTemporal g Y ψ)
    (hΦ : Continuous fun p : ℝ × E n => Φ p.1 p.2) (hΦ0 : ∀ x, Φ 0 x = x)
    (hΦψ : ∀ t x, ψ (Φ t x) = ψ x + t) {F : (E n → ℝ) → ℝ} {K : Set (E n)}
    (hF : IsSource F K) (hKO : K ⊆ O n T) {N : Set (E n)} (hN : IsOpen N) {u' : E n → ℝ}
    (hu'i : LocallyIntegrableOn u' N) (hu' : AgreesOn g' (retardedS g' Y' F) u' N) :
    AgreesOn g (retardedS g Y F) (fun x => u' (Ψ x)) (A ψ τ ∩ Ψ ⁻¹' N) := by
  refine agreesOn_of_forall_exists (contDiff_sqrt_abs_det hg.smooth hg.det_ne_zero).continuous
    (fun h₁ h₂ hh₁ hh₁' hh₂ hh₂' => hF.retardedS_map_add hg hh₁ hh₁' hh₂ hh₂')
    (hP.locallyIntegrableOn_comp hg.lorentzian hψ.smooth.continuous hN hu'i) fun x hx => ?_
  obtain ⟨V, hV, hxV, -, -, -, hag⟩ := hP.exists_agreesOn_retardedS_comp hgA hg'A hg hg' hY hY'
    hC hψ hΦ hΦ0 hΦψ hF hKO hN hu' hx.1 hx.2
  exact ⟨V, hV, hxV, hag⟩

/-- If `G^ret_{g'} F` vanishes on the open set `N`, then `G^ret_g F` vanishes on
`A_τ ∩ Ψ⁻¹(N)`. -/
theorem vanishesOn_retardedS (hP : ExtensionProperty g g' ψ (W n T) τ Ψ)
    (hgA : IsAdmissibleMetric n T g) (hg'A : IsAdmissibleMetric n T g')
    (hg : IsSpacetime g Y) (hg' : IsSpacetime g' Y')
    (hY : ∀ x ∉ M0 n T, form (g x) (EuclideanSpace.single 0 1) (Y x) < 0)
    (hY' : ∀ x ∉ M0 n T, form (g' x) (EuclideanSpace.single 0 1) (Y' x) < 0)
    (hC : CauchyDataSubset n T g g') (hψ : IsCauchyTemporal g Y ψ)
    (hΦ : Continuous fun p : ℝ × E n => Φ p.1 p.2) (hΦ0 : ∀ x, Φ 0 x = x)
    (hΦψ : ∀ t x, ψ (Φ t x) = ψ x + t) {F : (E n → ℝ) → ℝ} {K : Set (E n)}
    (hF : IsSource F K) (hKO : K ⊆ O n T) {N : Set (E n)} (hN : IsOpen N)
    (hv : VanishesOn (retardedS g' Y' F) N) :
    VanishesOn (retardedS g Y F) (A ψ τ ∩ Ψ ⁻¹' N) :=
  (vanishesOn_iff_agreesOn_zero (g := g)).2 (hP.agreesOn_retardedS_comp hgA hg'A hg hg' hY hY' hC
    hψ hΦ hΦ0 hΦψ hF hKO hN locallyIntegrableOn_zero
    ((vanishesOn_iff_agreesOn_zero (g := g')).1 hv))

end ExtensionProperty

end

end LorentzianCalderon
