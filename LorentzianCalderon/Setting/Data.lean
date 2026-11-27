module

public import LorentzianCalderon.Green.Basic
public import LorentzianCalderon.Setting.Escape

public section

/-!
# The data

Blueprint, Lemma `lem_data`, for smooth sources: if the Cauchy data set of `g` is contained in
that of `g'`, the retarded and advanced solutions of `g` and `g'` with sources outside `M₀`
agree outside `M₀`.

The proof tests `G^ret_g f` against
`h = □_{g'} G^adv_{g'} h` for test functions `h` supported outside `M₀`, and integrates by
parts: on `ℝ^{1+n}` for `G^ret_g f`, and on `M₀` for the difference with the solution of `g'`
with the same Cauchy data on `∂M₀`.
-/

namespace LorentzianCalderon

noncomputable section
open MeasureTheory Set Filter Function
open scoped ContDiff Matrix Topology

variable {n : ℕ}

/-! ### Comparison of causal futures -/

section Comparison

variable {g g' : MatrixField n} {Y Y' : E n → E n} {C : Set (E n)}

/-- A smooth causal piece for `(g, Y)` is causal for `(g', Y')` after its last point in `C`,
if the future causal cones agree outside the closed set `C`. -/
theorem causalLE_or_of_isPathPiece (hg' : IsSpacetime g' Y') (hC : IsClosed C)
    (hcone : ∀ x ∉ C, ∀ v, IsFutureCausal g Y x v → IsFutureCausal g' Y' x v)
    {α β : ℝ} {γ : ℝ → E n} (hαβ : α < β) (hγ : IsPathPiece (IsFutureCausal g Y) α β γ) :
    CausalLE g' Y' (γ α) (γ β) ∨ ∃ z ∈ C, CausalLE g' Y' z (γ β) := by
  have hcont : ContinuousOn γ (Icc α β) := (isPathPiece_iff.1 hγ).1.continuousOn
  have hpiece : ∀ t, α ≤ t → t < β → (∀ t' ∈ Icc t β, γ t' ∉ C) →
      CausalLE g' Y' (γ t) (γ β) := by
    intro t hαt htβ hnot
    have hp := hγ.mono_interval hαt htβ le_rfl
    have hp' : IsPathPiece (IsFutureCausal g' Y') t β γ :=
      isPathPiece_iff.2 ⟨(isPathPiece_iff.1 hp).1,
        fun t' ht' => hcone _ (hnot t' ht') _ ((isPathPiece_iff.1 hp).2 t' ht')⟩
    exact causalLE_of_isPathOn
      (isPathOn_iff.2 ⟨htβ, ∅, fun x y hx hxy hy _ => hp'.mono_interval hx hxy hy⟩)
  set S := Icc α β ∩ γ ⁻¹' C
  by_cases hS : S.Nonempty
  · have hSc : IsClosed S := hcont.preimage_isClosed_of_isClosed isClosed_Icc hC
    have hSb : BddAbove S := bddAbove_Icc.mono inter_subset_left
    set t₀ := sSup S
    have ht₀ : t₀ ∈ S := hSc.csSup_mem hS hSb
    right
    refine ⟨γ t₀, ht₀.2, ?_⟩
    rcases eq_or_lt_of_le ht₀.1.2 with h | h
    · rw [h]
    · have hnot : ∀ t' ∈ Ioc t₀ β, γ t' ∉ C := fun t' ht' hC' =>
        not_le.2 ht'.1 (le_csSup hSb ⟨⟨ht₀.1.1.trans ht'.1.le, ht'.2⟩, hC'⟩)
      have hrel : ∀ t ∈ Ioo t₀ β, CausalLE g' Y' (γ t) (γ β) := fun t ht =>
        hpiece t (ht₀.1.1.trans ht.1.le) ht.2 fun t' ht' => hnot t' ⟨ht.1.trans_le ht'.1, ht'.2⟩
      have hlim : Tendsto (fun t => (γ t, γ β)) (𝓝[Ioo t₀ β] t₀) (𝓝 (γ t₀, γ β)) :=
        ((hcont t₀ ht₀.1).mono (fun t ht => ⟨ht₀.1.1.trans ht.1.le, ht.2.le⟩)).tendsto.prodMk_nhds
          tendsto_const_nhds
      have : (𝓝[Ioo t₀ β] t₀).NeBot := left_nhdsWithin_Ioo_neBot h
      exact (Facts.isClosed_causalLE hg').mem_of_tendsto hlim
        (eventually_mem_nhdsWithin.mono fun t ht => hrel t ht)
  · left
    exact hpiece α le_rfl hαβ fun t' ht' hC' => hS ⟨t', ht', hC'⟩

/-- If the future causal cones of `(g, Y)` and `(g', Y')` agree outside the closed set `C`, a
`g`-causal curve is `g'`-causal after its last point in `C`. -/
theorem causalLE_or_of_causalLE (hg' : IsSpacetime g' Y') (hC : IsClosed C)
    (hcone : ∀ x ∉ C, ∀ v, IsFutureCausal g Y x v → IsFutureCausal g' Y' x v) {p q : E n}
    (h : CausalLE g Y p q) : CausalLE g' Y' p q ∨ ∃ z ∈ C, CausalLE g' Y' z q := by
  rcases causalLE_iff.1 h with rfl | ⟨γ, hγ', h0, h1⟩
  · exact Or.inl (CausalLE.refl _)
  obtain ⟨k, s, hs, hγ⟩ := isPathOn_def.1 hγ'
  have key : ∀ m : Fin (k + 2),
      CausalLE g' Y' p (γ (s m)) ∨ ∃ z ∈ C, CausalLE g' Y' z (γ (s m)) := by
    intro m
    induction m using Fin.induction with
    | zero => exact Or.inl (by rw [hs.first, h0])
    | succ i ih =>
      have hsm := hγ.smooth i
      have hvel := hγ.velocity i
      rw [piece_def] at hsm hvel
      have hpc := causalLE_or_of_isPathPiece hg' hC hcone
        (hs.strictMono i.castSucc_lt_succ) (isPathPiece_iff.2 ⟨hsm, hvel⟩)
      rcases hpc with hpc | hpc
      · rcases ih with ih | ⟨z, hz, hzq⟩
        · exact Or.inl (ih.trans hpc)
        · exact Or.inr ⟨z, hz, hzq.trans hpc⟩
      · exact Or.inr hpc
  simpa [hs.last, h1] using key (Fin.last (k + 1))

theorem causalFutureSet_subset_of_cone (hg' : IsSpacetime g' Y') (hC : IsClosed C)
    (hcone : ∀ x ∉ C, ∀ v, IsFutureCausal g Y x v → IsFutureCausal g' Y' x v) (K : Set (E n)) :
    causalFutureSet g Y K ⊆ causalFutureSet g' Y' (K ∪ C) := by
  intro x hx
  obtain ⟨p, hp, hpx⟩ := mem_causalFutureSet.1 hx
  rcases causalLE_or_of_causalLE hg' hC hcone (mem_causalFuture.1 hpx) with h | ⟨z, hz, hzx⟩
  · exact mem_causalFutureSet.2 ⟨p, Or.inl hp, mem_causalFuture.2 h⟩
  · exact mem_causalFutureSet.2 ⟨z, Or.inr hz, mem_causalFuture.2 hzx⟩

end Comparison

/-! ### Testing against functions supported in an open set -/

/-- A continuous function whose integrals against all test functions supported in an open set
vanish is zero on that set. -/
theorem eqOn_zero_of_integral_mul_eq_zero {U : Set (E n)} (hU : IsOpen U) {φ : E n → ℝ}
    (hφ : Continuous φ)
    (h : ∀ h : E n → ℝ, ContDiff ℝ ∞ h → HasCompactSupport h → tsupport h ⊆ U →
      ∫ x, h x * φ x = 0) : ∀ x ∈ U, φ x = 0 := by
  have hae := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
    (hφ.locallyIntegrable.locallyIntegrableOn U) fun h' hh hh' hU' => by
      simpa only [smul_eq_mul] using h h' hh hh' hU'
  set V := U ∩ {x | φ x ≠ 0}
  have hV : IsOpen V := hU.inter (isOpen_ne_fun hφ continuous_const)
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

/-! ### The data -/

lemma det_minkowski : (minkowski n).det = -1 := by
  rw [minkowski_def, Matrix.det_diagonal, Fin.prod_univ_succ]
  simp

lemma sqrt_abs_det_minkowski : √|(minkowski n).det| = 1 := by
  simp [det_minkowski]

lemma isClosed_M0 (T : ℝ) : IsClosed (M0 n T) := (isCompact_M0 T).isClosed

section Data

variable {T : ℝ} {g g' : MatrixField n} {Y Y' : E n → E n}

/-- The retarded case of `lem_data`, assuming only that `g = g' = η` outside `M₀` and that the
future causal cones agree there. -/
theorem retarded_eq_of_cauchyDataSubset_of_cone (hgη : ∀ x ∉ M0 n T, g x = minkowski n)
    (hg'η : ∀ x ∉ M0 n T, g' x = minkowski n) (hg : IsSpacetime g Y) (hg' : IsSpacetime g' Y')
    (hcone : ∀ x ∉ M0 n T, ∀ v, IsFutureCausal g Y x v → IsFutureCausal g' Y' x v)
    (hC : CauchyDataSubset n T g g') {f : E n → ℝ} (hf : ContDiff ℝ ∞ f)
    (hf' : HasCompactSupport f) (hfM : tsupport f ⊆ (M0 n T)ᶜ) :
    ∀ x ∉ M0 n T, retarded g Y f x = retarded g' Y' f x := by
  set S := (M0 n T)ᶜ
  have hS : IsOpen S := (isClosed_M0 T).isOpen_compl
  set u := retarded g Y f
  set r := retarded g' Y' f
  set ρ' : E n → ℝ := fun x => √|(g' x).det|
  have hρ'1 : ∀ x ∈ S, ρ' x = 1 := fun x hx => by simp [ρ', hg'η x hx, sqrt_abs_det_minkowski]
  have hρ'c : Continuous ρ' := (contDiff_sqrt_abs_det hg'.smooth hg'.det_ne_zero).continuous
  have hu : ContDiff ℝ ∞ u := contDiff_retarded
  have hf0 : ∀ x ∈ M0 n T, f x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hfM h hx
  have hbox'u : ∀ x ∈ S, box g' u x = f x := by
    intro x hx
    have hgg : g' =ᶠ[𝓝 x] g := eventually_of_mem (hS.mem_nhds hx) fun y hy => by
      rw [hgη y hy, hg'η y hy]
    rw [box_congr_metric hgg, box_retarded hg hf hf']
  obtain ⟨v, hv, hdata⟩ := cauchyDataSubset_def.1 hC u
    ⟨hu, fun x hx => by rw [box_retarded hg hf hf', hf0 x hx]⟩
  set w : E n → ℝ := fun x => v x - u x
  have hw : ContDiff ℝ ∞ w := hv.smooth.sub hu
  have hdiff : ∀ {φ : E n → ℝ}, ContDiff ℝ ∞ φ → ∀ x, DifferentiableAt ℝ φ x :=
    fun hφ x => (hφ.differentiable (by simp)) x
  have hw0 : ∀ x ∈ frontier (M0 n T), w x = 0 := fun x hx => by
    simp [w, hdata.value x hx]
  have hdw0 : ∀ x ∈ frontier (M0 n T), fderiv ℝ w x = 0 := fun x hx => by
    rw [fderiv_fun_sub (hdiff hv.smooth x) (hdiff hu x), hdata.differential x hx, sub_self]
  refine fun x hx => sub_eq_zero.1 (eqOn_zero_of_integral_mul_eq_zero hS
    (hu.continuous.sub contDiff_retarded.continuous) (fun h hh hh' hhS => ?_) x hx)
  set a := advanced g' Y' h
  have ha : ContDiff ℝ ∞ a := contDiff_advanced
  have hboxa : ∀ x, box g' a x = h x := box_advanced hg' hh hh'
  have hh0 : ∀ x ∈ M0 n T, h x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h' => hhS h' hx
  have hA : ∫ x, r x * h x * ρ' x = ∫ x, f x * a x * ρ' x :=
    integral_retarded_mul hg' hf hf' hh hh'
  have hcpt : IsCompact (tsupport u ∩ tsupport a) := by
    refine (Facts.isCompact_causalFutureSet_inter_causalPastSet hg'
      (hf'.isCompact.union (isCompact_M0 T)) hh'.isCompact).of_isClosed_subset
      ((isClosed_tsupport _).inter (isClosed_tsupport _))
      (inter_subset_inter (tsupport_retarded_subset.trans
        (causalFutureSet_subset_of_cone hg' (isClosed_M0 T) hcone _)) tsupport_advanced_subset)
  have hG := integral_mul_box_comm_of_isCompact hg'.smooth hg'.symm hg'.det_ne_zero hu ha hcpt
  simp only [hboxa] at hG
  have hint : Integrable fun x => a x * box g' u x * ρ' x := by
    refine ((ha.continuous.mul (continuous_box hg'.smooth hg'.det_ne_zero hu)).mul
      hρ'c).integrable_of_hasCompactSupport
      (HasCompactSupport.intro ((isCompact_M0 T).union hf'.isCompact) fun x hx => ?_)
    have hxS : x ∈ S := fun h => hx (Or.inl h)
    simp only [Pi.mul_apply]
    rw [hbox'u x hxS, image_eq_zero_of_notMem_tsupport fun h => hx (Or.inr h)]
    ring
  have hM0 : ∫ x in M0 n T, a x * box g' u x * ρ' x = 0 := by
    have hGM := integral_mul_box_comm (T := T) hg'.smooth hg'.symm hg'.det_ne_zero hw ha hw0
      hdw0
    have h1 : ∫ x in M0 n T, w x * box g' a x * √|(g' x).det| = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
      rw [hboxa, hh0 x hx]
      ring
    rw [h1] at hGM
    rw [← neg_eq_zero, ← integral_neg, hGM]
    refine setIntegral_congr_fun (isClosed_M0 T).measurableSet fun x hx => ?_
    simp only [w, ρ']
    rw [box_sub hg'.smooth hg'.det_ne_zero hv.smooth hu, hv.wave x hx]
    ring
  have hSint : ∫ x in S, a x * box g' u x * ρ' x = ∫ x, f x * a x * ρ' x := by
    rw [setIntegral_congr_fun (g := fun x => a x * f x * ρ' x) hS.measurableSet fun x hx => by
      simp only [hbox'u x hx]]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).trans
      (integral_congr_ae (Eventually.of_forall fun x => by simp only; ring))
    rw [hf0 x (not_not.1 hx)]
    ring
  have hB : ∫ x, u x * h x * ρ' x = ∫ x, f x * a x * ρ' x := by
    rw [hG, ← integral_add_compl (isClosed_M0 T).measurableSet hint, hM0, zero_add, hSint]
  have hρh : ∀ φ : E n → ℝ, (fun x => φ x * h x * ρ' x) = fun x => h x * φ x := by
    intro φ
    funext x
    by_cases hx : x ∈ S
    · rw [hρ'1 x hx]
      ring
    · rw [hh0 x (not_not.1 hx)]
      ring
  have hcs : ∀ φ : E n → ℝ, Continuous φ → Integrable fun x => h x * φ x := fun φ hφ =>
    (hh.continuous.mul hφ).integrable_of_hasCompactSupport hh'.mul_right
  rw [hρh] at hA hB
  simp only [Pi.sub_apply, mul_sub]
  rw [integral_sub (hcs _ hu.continuous) (hcs _ contDiff_retarded.continuous), hA, hB, sub_self]

/-- At points outside `M₀`, where `g` is Minkowskian with `∂ₜ` future-directed, the future
causal cones of `(g, Y)` and `(g', Y')` agree. -/
lemma isFutureCausal_iff_of_exterior (hg : IsSpacetime g Y) (hg' : IsSpacetime g' Y')
    (hgη : ∀ x ∉ M0 n T, g x = minkowski n) (hg'η : ∀ x ∉ M0 n T, g' x = minkowski n)
    (hY : ∀ x ∉ M0 n T, form (g x) (EuclideanSpace.single 0 1) (Y x) < 0)
    (hY' : ∀ x ∉ M0 n T, form (g' x) (EuclideanSpace.single 0 1) (Y' x) < 0) {x : E n}
    (hx : x ∉ M0 n T) (v : E n) : IsFutureCausal g Y x v ↔ IsFutureCausal g' Y' x v := by
  rw [isFutureCausal_iff_of_minkowski (hgη x hx)
      (hg.globallyHyperbolic.timeOrientation.timelike x) (hY x hx),
    isFutureCausal_iff_of_minkowski (hg'η x hx)
      (hg'.globallyHyperbolic.timeOrientation.timelike x) (hY' x hx)]

/-- **The data** (blueprint, Lemma `lem_data`, retarded case): if the Cauchy data set of `g` is
contained in that of `g'`, then `G^ret_g f = G^ret_{g'} f` outside `M₀` for test functions `f`
supported outside `M₀`. -/
theorem retarded_eq_of_cauchyDataSubset (hgA : IsAdmissibleMetric n T g)
    (hg'A : IsAdmissibleMetric n T g') (hg : IsSpacetime g Y) (hg' : IsSpacetime g' Y')
    (hY : ∀ x ∉ M0 n T, form (g x) (EuclideanSpace.single 0 1) (Y x) < 0)
    (hY' : ∀ x ∉ M0 n T, form (g' x) (EuclideanSpace.single 0 1) (Y' x) < 0)
    (hC : CauchyDataSubset n T g g') {f : E n → ℝ} (hf : ContDiff ℝ ∞ f)
    (hf' : HasCompactSupport f) (hfM : tsupport f ⊆ (M0 n T)ᶜ) {x : E n}
    (hx : x ∉ M0 n T) : retarded g Y f x = retarded g' Y' f x :=
  retarded_eq_of_cauchyDataSubset_of_cone hgA.minkowski_exterior hg'A.minkowski_exterior hg hg'
    (fun _ hy v => (isFutureCausal_iff_of_exterior hg hg' hgA.minkowski_exterior
      hg'A.minkowski_exterior hY hY' hy v).1) hC hf hf' hfM x hx

/-- **The data** (blueprint, Lemma `lem_data`, advanced case). -/
theorem advanced_eq_of_cauchyDataSubset (hgA : IsAdmissibleMetric n T g)
    (hg'A : IsAdmissibleMetric n T g') (hg : IsSpacetime g Y) (hg' : IsSpacetime g' Y')
    (hY : ∀ x ∉ M0 n T, form (g x) (EuclideanSpace.single 0 1) (Y x) < 0)
    (hY' : ∀ x ∉ M0 n T, form (g' x) (EuclideanSpace.single 0 1) (Y' x) < 0)
    (hC : CauchyDataSubset n T g g') {f : E n → ℝ} (hf : ContDiff ℝ ∞ f)
    (hf' : HasCompactSupport f) (hfM : tsupport f ⊆ (M0 n T)ᶜ) {x : E n}
    (hx : x ∉ M0 n T) : advanced g Y f x = advanced g' Y' f x := by
  rw [advanced_def, advanced_def]
  exact retarded_eq_of_cauchyDataSubset_of_cone hgA.minkowski_exterior hg'A.minkowski_exterior
    hg.neg
    hg'.neg (fun _ hy v hv => isFutureCausal_neg_iff.2
      ((isFutureCausal_iff_of_exterior hg hg' hgA.minkowski_exterior hg'A.minkowski_exterior hY
        hY' hy (-v)).1 (isFutureCausal_neg_iff.1 hv))) hC hf hf' hfM x hx

end Data

end

end LorentzianCalderon
