module

public import LorentzianCalderon.Green.Temporal
public import LorentzianCalderon.Geometry.CausalClosed
public import LorentzianCalderon.Green.BoxCalculus
public import LorentzianCalderon.Green.Retarded
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

public section

/-!
# Retarded and advanced solution operators

For a spacetime `(g, Y)`, `retarded g Y f` is a smooth solution of `□_g v = f` supported in
`J⁺(supp f)` (chosen by `Facts.exists_retarded`) and `advanced g Y f = retarded g (-Y) f`, for
test functions `f`. Uniqueness of such solutions (by duality: Green's identity against
advanced solutions) gives linearity, `G^ret □_g f = f`, the duality
`∫ (G^ret f) h dV_g = ∫ f (G^adv h) dV_g` and smooth dependence on parameters.
-/

namespace LorentzianCalderon

noncomputable section
open MeasureTheory Set Filter Function
open scoped ContDiff Matrix Topology

variable {n : ℕ} {g : MatrixField n} {Y : E n → E n}

/-! ### Preliminaries -/

lemma causalFutureSet_mono {A B : Set (E n)} (h : A ⊆ B) :
    causalFutureSet g Y A ⊆ causalFutureSet g Y B := by
  rw [causalFutureSet_def, causalFutureSet_def]
  exact biUnion_subset_biUnion_left h

lemma causalPastSet_mono {A B : Set (E n)} (h : A ⊆ B) :
    causalPastSet g Y A ⊆ causalPastSet g Y B := by
  rw [causalPastSet_def, causalPastSet_def]
  exact biUnion_subset_biUnion_left h

lemma causalFutureSet_union (A B : Set (E n)) :
    causalFutureSet g Y (A ∪ B) = causalFutureSet g Y A ∪ causalFutureSet g Y B := by
  simp only [causalFutureSet_def]
  exact biUnion_union A B _

lemma eventuallyEq_zero_of_isOpen {v : E n → ℝ} {U : Set (E n)} (hU : IsOpen U)
    (hv : ∀ y ∈ U, v y = 0) {x : E n} (hx : x ∈ U) : v =ᶠ[𝓝 x] 0 :=
  eventually_of_mem (hU.mem_nhds hx) hv

/-- A function vanishing on an open set has vanishing Cauchy data there. -/
lemma fderiv_eq_zero_of_isOpen {v : E n → ℝ} {U : Set (E n)} (hU : IsOpen U)
    (hv : ∀ y ∈ U, v y = 0) {x : E n} (hx : x ∈ U) : fderiv ℝ v x = 0 := by
  rw [(eventuallyEq_zero_of_isOpen hU hv hx).fderiv_eq]
  exact fderiv_const_apply 0

/-! ### The retarded and advanced operators -/

/-- A smooth solution of `□_g v = f` supported in `J⁺(supp f)`, for a test function `f`: the
constant family in `Facts.exists_retarded`. -/
theorem exists_retarded (hg : IsSpacetime g Y) {f : E n → ℝ} (hf : ContDiff ℝ ∞ f)
    (hf' : HasCompactSupport f) :
    ∃ v : E n → ℝ, ContDiff ℝ ∞ v ∧ (∀ x, box g v x = f x) ∧
      support v ⊆ causalFutureSet g Y (tsupport f) := by
  obtain ⟨V, hV, hV'⟩ := Facts.exists_retarded hg (F := fun _ => f) (hf.comp contDiff_snd)
    hf'.isCompact fun _ => subset_tsupport f
  exact ⟨V 0, hV.comp (contDiff_const.prodMk contDiff_id), (hV' 0).1, (hV' 0).2⟩

variable (g Y) in
open Classical in
/-- The retarded solution operator `G^ret`: a smooth solution of `□_g v = f` supported in
`J⁺(supp f)`, for a test function `f`; `0` otherwise. -/
def retarded (f : E n → ℝ) : E n → ℝ :=
  if h : IsSpacetime g Y ∧ ContDiff ℝ ∞ f ∧ HasCompactSupport f then
    (exists_retarded h.1 h.2.1 h.2.2).choose
  else 0

variable (g Y) in
/-- The advanced solution operator `G^adv`, the retarded one for the reversed time
orientation. -/
def advanced (f : E n → ℝ) : E n → ℝ :=
  retarded g (-Y) f

theorem advanced_def (f : E n → ℝ) : advanced g Y f = retarded g (-Y) f := by rfl

variable {f h : E n → ℝ}

theorem contDiff_retarded : ContDiff ℝ ∞ (retarded g Y f) := by
  unfold retarded
  split_ifs with h
  · exact (exists_retarded h.1 h.2.1 h.2.2).choose_spec.1
  · exact contDiff_const

theorem box_retarded (hg : IsSpacetime g Y) (hf : ContDiff ℝ ∞ f) (hf' : HasCompactSupport f)
    (x : E n) : box g (retarded g Y f) x = f x := by
  have h : IsSpacetime g Y ∧ ContDiff ℝ ∞ f ∧ HasCompactSupport f := ⟨hg, hf, hf'⟩
  rw [retarded, dite_eq_left_of_eq_true (eq_true h)]
  exact (exists_retarded h.1 h.2.1 h.2.2).choose_spec.2.1 x

theorem support_retarded_subset : support (retarded g Y f) ⊆ causalFutureSet g Y (tsupport f) := by
  unfold retarded
  split_ifs with h
  · exact (exists_retarded h.1 h.2.1 h.2.2).choose_spec.2.2
  · simp

theorem tsupport_retarded_subset :
    tsupport (retarded g Y f) ⊆ causalFutureSet g Y (tsupport f) := by
  by_cases h : IsSpacetime g Y ∧ ContDiff ℝ ∞ f ∧ HasCompactSupport f
  · exact closure_minimal support_retarded_subset (isClosed_causalFutureSet h.1 h.2.2)
  · simp [retarded, dite_eq_right_of_eq_false (eq_false h)]

/-- The retarded operator vanishes outside `J⁺(supp f)`, an open condition. -/
theorem retarded_eventuallyEq_zero {x : E n} (hx : x ∉ causalFutureSet g Y (tsupport f)) :
    retarded g Y f =ᶠ[𝓝 x] 0 :=
  notMem_tsupport_iff_eventuallyEq.1 fun h => hx (tsupport_retarded_subset h)

theorem contDiff_advanced : ContDiff ℝ ∞ (advanced g Y f) := contDiff_retarded

theorem box_advanced (hg : IsSpacetime g Y) (hf : ContDiff ℝ ∞ f) (hf' : HasCompactSupport f)
    (x : E n) : box g (advanced g Y f) x = f x :=
  box_retarded hg.neg hf hf' x

theorem support_advanced_subset : support (advanced g Y f) ⊆ causalPastSet g Y (tsupport f) := by
  rw [← causalFutureSet_neg]
  exact support_retarded_subset

theorem tsupport_advanced_subset :
    tsupport (advanced g Y f) ⊆ causalPastSet g Y (tsupport f) := by
  rw [← causalFutureSet_neg]
  exact tsupport_retarded_subset

theorem advanced_eventuallyEq_zero {x : E n} (hx : x ∉ causalPastSet g Y (tsupport f)) :
    advanced g Y f =ᶠ[𝓝 x] 0 :=
  retarded_eventuallyEq_zero (by rwa [causalFutureSet_neg])

/-! ### Uniqueness -/

/-- **Uniqueness.** A smooth solution of `□_g v = 0` supported in `J⁺(K)`, `K` compact,
vanishes: by Green's identity, `∫ v ϑ dV_g = ∫ v □_g (G^adv ϑ) dV_g = ∫ (□_g v) G^adv ϑ dV_g = 0`
for every test function `ϑ`. -/
theorem eq_zero_of_support_subset_causalFutureSet (hg : IsSpacetime g Y) {v : E n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hbox : ∀ x, box g v x = 0) {K : Set (E n)} (hK : IsCompact K)
    (hsupp : support v ⊆ causalFutureSet g Y K) : v = 0 := by
  set ρ : E n → ℝ := fun x => √|(g x).det|
  have hρ : ContDiff ℝ ∞ ρ := contDiff_sqrt_abs_det hg.smooth hg.det_ne_zero
  have hts : tsupport v ⊆ causalFutureSet g Y K :=
    closure_minimal hsupp (isClosed_causalFutureSet hg hK)
  have hae : ∀ᵐ x ∂volume, v x * ρ x = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hv.continuous.mul hρ.continuous).locallyIntegrable fun ϑ hϑ hϑc => ?_
    have hcpt : IsCompact (tsupport v ∩ tsupport (advanced g Y ϑ)) :=
      (Facts.isCompact_causalFutureSet_inter_causalPastSet hg hK hϑc.isCompact).of_isClosed_subset
        ((isClosed_tsupport _).inter (isClosed_tsupport _))
        (inter_subset_inter hts tsupport_advanced_subset)
    have hG := integral_mul_box_comm_of_isCompact hg.smooth hg.symm hg.det_ne_zero hv
      contDiff_advanced hcpt
    simp only [box_advanced hg hϑ hϑc, hbox, mul_zero, zero_mul, integral_zero] at hG
    rw [← hG]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only [smul_eq_mul, ρ]; ring)
  have h0 := (Continuous.ae_eq_iff_eq volume (hv.continuous.mul hρ.continuous)
    continuous_const).1 hae
  funext x
  have hx := congr_fun h0 x
  have hρx : ρ x ≠ 0 := (Real.sqrt_pos.2 (abs_pos.2 (hg.det_ne_zero x))).ne'
  exact (mul_eq_zero.1 hx).resolve_right hρx

/-- **Uniqueness**, past version. -/
theorem eq_zero_of_support_subset_causalPastSet (hg : IsSpacetime g Y) {v : E n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hbox : ∀ x, box g v x = 0) {K : Set (E n)} (hK : IsCompact K)
    (hsupp : support v ⊆ causalPastSet g Y K) : v = 0 :=
  eq_zero_of_support_subset_causalFutureSet hg.neg hv hbox hK
    (by rwa [causalFutureSet_neg])

/-- A smooth solution of `□_g v = f` supported in `J⁺(K)`, `K` compact, is `G^ret f`. -/
theorem retarded_eq_of_support (hg : IsSpacetime g Y) (hf : ContDiff ℝ ∞ f)
    (hf' : HasCompactSupport f) {v : E n → ℝ} (hv : ContDiff ℝ ∞ v) (hbox : ∀ x, box g v x = f x)
    {K : Set (E n)} (hK : IsCompact K) (hsupp : support v ⊆ causalFutureSet g Y K) :
    retarded g Y f = v := by
  have hD := eq_zero_of_support_subset_causalFutureSet hg
    (contDiff_retarded.sub hv) (fun x => by
      rw [box_sub hg.smooth hg.det_ne_zero contDiff_retarded hv, box_retarded hg hf hf', hbox,
        sub_self])
    (hf'.isCompact.union hK) (K := tsupport f ∪ K) (fun x hx => by
      rw [causalFutureSet_union]
      by_cases h1 : retarded g Y f x = 0
      · exact Or.inr (hsupp fun h2 => hx (by simp [h1, h2]))
      · exact Or.inl (support_retarded_subset h1))
  funext x
  exact sub_eq_zero.1 (congr_fun hD x)

theorem retarded_linear (hg : IsSpacetime g Y) {f₁ f₂ : E n → ℝ} (hf₁ : ContDiff ℝ ∞ f₁)
    (hf₁' : HasCompactSupport f₁) (hf₂ : ContDiff ℝ ∞ f₂) (hf₂' : HasCompactSupport f₂)
    (a b : ℝ) :
    retarded g Y (fun x => a * f₁ x + b * f₂ x) =
      fun x => a * retarded g Y f₁ x + b * retarded g Y f₂ x := by
  have hf : ContDiff ℝ ∞ fun x => a * f₁ x + b * f₂ x :=
    (contDiff_const.mul hf₁).add (contDiff_const.mul hf₂)
  have hf' : HasCompactSupport fun x => a * f₁ x + b * f₂ x :=
    (hf₁'.mul_left).add hf₂'.mul_left
  refine retarded_eq_of_support hg hf hf' ((contDiff_const.mul contDiff_retarded).add
    (contDiff_const.mul contDiff_retarded))
    (fun x => by rw [box_linear hg.smooth hg.det_ne_zero contDiff_retarded contDiff_retarded,
      box_retarded hg hf₁ hf₁', box_retarded hg hf₂ hf₂'])
    (hf₁'.isCompact.union hf₂'.isCompact) fun x hx => ?_
  rw [causalFutureSet_union]
  by_cases h1 : retarded g Y f₁ x = 0
  · by_cases h2 : retarded g Y f₂ x = 0
    · exact absurd (by simp [h1, h2]) hx
    · exact Or.inr (support_retarded_subset h2)
  · exact Or.inl (support_retarded_subset h1)

theorem retarded_add (hg : IsSpacetime g Y) {f₁ f₂ : E n → ℝ} (hf₁ : ContDiff ℝ ∞ f₁)
    (hf₁' : HasCompactSupport f₁) (hf₂ : ContDiff ℝ ∞ f₂) (hf₂' : HasCompactSupport f₂) :
    retarded g Y (f₁ + f₂) = retarded g Y f₁ + retarded g Y f₂ := by
  have := retarded_linear hg hf₁ hf₁' hf₂ hf₂' 1 1
  simp only [one_mul] at this
  exact this

theorem retarded_smul (hg : IsSpacetime g Y) (hf : ContDiff ℝ ∞ f) (hf' : HasCompactSupport f)
    (a : ℝ) : retarded g Y (a • f) = a • retarded g Y f := by
  have := retarded_linear hg hf hf' hf hf' a 0
  simp only [zero_mul, add_zero] at this
  exact this

/-- `G^ret □_g f = f` for test functions `f`. -/
theorem retarded_box (hg : IsSpacetime g Y) (hf : ContDiff ℝ ∞ f) (hf' : HasCompactSupport f) :
    retarded g Y (box g f) = f :=
  retarded_eq_of_support hg (contDiff_box hg.smooth hg.det_ne_zero hf) (hasCompactSupport_box hf') hf (fun _ => rfl)
    hf'.isCompact ((subset_tsupport f).trans (subset_causalFutureSet _))

/-- Smooth dependence on parameters: for jointly smooth sources with supports in a fixed
compact set, the retarded solutions are jointly smooth. -/
theorem contDiff_retarded_param (hg : IsSpacetime g Y) {F : ℝ → E n → ℝ}
    (hF : ContDiff ℝ ∞ fun p : ℝ × E n => F p.1 p.2) {K : Set (E n)} (hK : IsCompact K)
    (hsupp : ∀ s, support (F s) ⊆ K) :
    ContDiff ℝ ∞ fun p : ℝ × E n => retarded g Y (F p.1) p.2 := by
  obtain ⟨V, hV, hV'⟩ := Facts.exists_retarded hg hF hK hsupp
  have heq : ∀ s, retarded g Y (F s) = V s := fun s =>
    retarded_eq_of_support hg (hF.comp (contDiff_const.prodMk contDiff_id))
      (HasCompactSupport.intro hK fun x hx => notMem_support.1 fun h => hx (hsupp s h))
      (hV.comp (contDiff_const.prodMk contDiff_id)) (hV' s).1 hK (hV' s).2
  simp only [heq]
  exact hV

/-! ### The advanced operator -/

theorem advanced_eq_of_support (hg : IsSpacetime g Y) (hf : ContDiff ℝ ∞ f)
    (hf' : HasCompactSupport f) {v : E n → ℝ} (hv : ContDiff ℝ ∞ v) (hbox : ∀ x, box g v x = f x)
    {K : Set (E n)} (hK : IsCompact K) (hsupp : support v ⊆ causalPastSet g Y K) :
    advanced g Y f = v :=
  retarded_eq_of_support hg.neg hf hf' hv hbox hK (by rwa [causalFutureSet_neg])

theorem advanced_linear (hg : IsSpacetime g Y) {f₁ f₂ : E n → ℝ} (hf₁ : ContDiff ℝ ∞ f₁)
    (hf₁' : HasCompactSupport f₁) (hf₂ : ContDiff ℝ ∞ f₂) (hf₂' : HasCompactSupport f₂)
    (a b : ℝ) :
    advanced g Y (fun x => a * f₁ x + b * f₂ x) =
      fun x => a * advanced g Y f₁ x + b * advanced g Y f₂ x :=
  retarded_linear hg.neg hf₁ hf₁' hf₂ hf₂' a b

theorem advanced_add (hg : IsSpacetime g Y) {f₁ f₂ : E n → ℝ} (hf₁ : ContDiff ℝ ∞ f₁)
    (hf₁' : HasCompactSupport f₁) (hf₂ : ContDiff ℝ ∞ f₂) (hf₂' : HasCompactSupport f₂) :
    advanced g Y (f₁ + f₂) = advanced g Y f₁ + advanced g Y f₂ :=
  retarded_add hg.neg hf₁ hf₁' hf₂ hf₂'

theorem advanced_smul (hg : IsSpacetime g Y) (hf : ContDiff ℝ ∞ f) (hf' : HasCompactSupport f)
    (a : ℝ) : advanced g Y (a • f) = a • advanced g Y f :=
  retarded_smul hg.neg hf hf' a

theorem advanced_box (hg : IsSpacetime g Y) (hf : ContDiff ℝ ∞ f) (hf' : HasCompactSupport f) :
    advanced g Y (box g f) = f :=
  retarded_box hg.neg hf hf'

theorem contDiff_advanced_param (hg : IsSpacetime g Y) {F : ℝ → E n → ℝ}
    (hF : ContDiff ℝ ∞ fun p : ℝ × E n => F p.1 p.2) {K : Set (E n)} (hK : IsCompact K)
    (hsupp : ∀ s, support (F s) ⊆ K) :
    ContDiff ℝ ∞ fun p : ℝ × E n => advanced g Y (F p.1) p.2 :=
  contDiff_retarded_param hg.neg hF hK hsupp

/-! ### Duality -/

/-- The supports of `G^ret f` and `G^adv h` meet in a compact set. -/
theorem isCompact_tsupport_retarded_inter_advanced (hg : IsSpacetime g Y)
    (hf' : HasCompactSupport f) (hh' : HasCompactSupport h) :
    IsCompact (tsupport (retarded g Y f) ∩ tsupport (advanced g Y h)) :=
  (Facts.isCompact_causalFutureSet_inter_causalPastSet hg hf'.isCompact hh'.isCompact).of_isClosed_subset
    ((isClosed_tsupport _).inter (isClosed_tsupport _))
    (inter_subset_inter tsupport_retarded_subset tsupport_advanced_subset)

/-- **Duality** `∫ (G^ret f) h dV_g = ∫ f (G^adv h) dV_g`. -/
theorem integral_retarded_mul (hg : IsSpacetime g Y) (hf : ContDiff ℝ ∞ f)
    (hf' : HasCompactSupport f) (hh : ContDiff ℝ ∞ h) (hh' : HasCompactSupport h) :
    ∫ x, retarded g Y f x * h x * √|(g x).det| =
      ∫ x, f x * advanced g Y h x * √|(g x).det| := by
  have := integral_mul_box_comm_of_isCompact hg.smooth hg.symm hg.det_ne_zero
    contDiff_retarded contDiff_advanced (isCompact_tsupport_retarded_inter_advanced hg hf' hh')
  simp only [box_advanced hg hh hh', box_retarded hg hf hf'] at this
  rw [this]
  exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)

end

end LorentzianCalderon
