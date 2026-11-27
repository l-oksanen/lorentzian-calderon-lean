module

public import LorentzianCalderon.Green.Basic

public section

/-!
# Sources and their retarded solutions

Distributions are handled as functionals `U : (E n → ℝ) → ℝ`, evaluated on test functions
(smooth with compact support), and functions `u` act through the pairing
`h ↦ ∫ u h dV_g` with `dV_g = √|det g| dx`.

A *source* supported in a compact set `K` is a functional that is additive and homogeneous
on smooth functions and vanishes on smooth functions vanishing near `K`. Its retarded solution
is defined by duality, `⟨G^ret F, h⟩ = F (G^adv h)`, which makes sense since `G^adv h` is smooth.
For a smooth source `f` this is the retarded solution `G^ret f` (`integral_retarded_mul`), and
for the source `□_g Π` of a compactly supported bounded measurable `Π` it is `Π`.
-/

namespace LorentzianCalderon

noncomputable section
open MeasureTheory Set Filter Function
open scoped ContDiff Topology

variable {n : ℕ} {g : MatrixField n} {Y : E n → E n}

/-! ### Distributions, sources and retarded solutions -/

variable (g) in
/-- The functional `U` agrees on the open set `V` with the function `u`:
`U h = ∫ u h dV_g` for test functions `h` supported in `V`. -/
def AgreesOn (U : (E n → ℝ) → ℝ) (u : E n → ℝ) (V : Set (E n)) : Prop :=
  ∀ h : E n → ℝ, ContDiff ℝ ∞ h → HasCompactSupport h → tsupport h ⊆ V →
    U h = ∫ x, u x * h x * √|(g x).det|

theorem agreesOn_iff {U : (E n → ℝ) → ℝ} {u : E n → ℝ} {V : Set (E n)} :
    AgreesOn g U u V ↔
      ∀ h : E n → ℝ, ContDiff ℝ ∞ h → HasCompactSupport h → tsupport h ⊆ V →
        U h = ∫ x, u x * h x * √|(g x).det| := Iff.rfl

/-- The functional `U` vanishes on `V`: `U h = 0` for test functions `h` supported in `V`. -/
def VanishesOn (U : (E n → ℝ) → ℝ) (V : Set (E n)) : Prop :=
  ∀ h : E n → ℝ, ContDiff ℝ ∞ h → HasCompactSupport h → tsupport h ⊆ V → U h = 0

theorem vanishesOn_iff {U : (E n → ℝ) → ℝ} {V : Set (E n)} :
    VanishesOn U V ↔
      ∀ h : E n → ℝ, ContDiff ℝ ∞ h → HasCompactSupport h → tsupport h ⊆ V → U h = 0 := Iff.rfl

/-- `F` is a source supported in the compact set `K`: additive and homogeneous on smooth
functions, and vanishing on smooth functions that vanish on a neighbourhood of `K`. -/
structure IsSource (F : (E n → ℝ) → ℝ) (K : Set (E n)) : Prop where
  isCompact : IsCompact K
  map_add : ∀ φ ψ : E n → ℝ, ContDiff ℝ ∞ φ → ContDiff ℝ ∞ ψ → F (φ + ψ) = F φ + F ψ
  map_smul : ∀ (c : ℝ) (φ : E n → ℝ), ContDiff ℝ ∞ φ → F (c • φ) = c * F φ
  eq_zero : ∀ φ : E n → ℝ, ContDiff ℝ ∞ φ → (∀ᶠ x in 𝓝ˢ K, φ x = 0) → F φ = 0

variable (g) in
/-- The source given by a function `f`: `φ ↦ ∫ f φ dV_g`. -/
def funSource (f : E n → ℝ) : (E n → ℝ) → ℝ :=
  fun φ => ∫ x, f x * φ x * √|(g x).det|

variable (g) in
/-- The source `□_g P` of a function `P`, by duality: `φ ↦ ∫ P □_g φ dV_g`. -/
def boxSource (P : E n → ℝ) : (E n → ℝ) → ℝ :=
  fun φ => ∫ x, P x * box g φ x * √|(g x).det|

variable (g Y) in
/-- The retarded solution `G^ret F` of a source, by duality: `⟨G^ret F, h⟩ = F (G^adv h)`. -/
def retardedS (F : (E n → ℝ) → ℝ) : (E n → ℝ) → ℝ :=
  fun h => F (advanced g Y h)

theorem retardedS_def (F : (E n → ℝ) → ℝ) :
    retardedS g Y F = fun h => F (advanced g Y h) := by rfl

/-! ### Sources -/

namespace IsSource

variable {F G : (E n → ℝ) → ℝ} {K L : Set (E n)}

theorem map_zero (hF : IsSource F K) : F 0 = 0 := by
  have := hF.map_smul 0 0 contDiff_const
  simpa using this

theorem map_neg (hF : IsSource F K) {φ : E n → ℝ} (hφ : ContDiff ℝ ∞ φ) : F (-φ) = -F φ := by
  have := hF.map_smul (-1) φ hφ
  simpa using this

theorem map_sub (hF : IsSource F K) {φ ψ : E n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hψ : ContDiff ℝ ∞ ψ) : F (φ - ψ) = F φ - F ψ := by
  rw [sub_eq_add_neg, hF.map_add φ (-ψ) hφ (hψ.neg : ContDiff ℝ ∞ (-ψ)), hF.map_neg hψ,
    sub_eq_add_neg]

/-- A source depends only on the values of a smooth function near its support. -/
theorem congr (hF : IsSource F K) {φ ψ : E n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ)
    (h : ∀ᶠ x in 𝓝ˢ K, φ x = ψ x) : F φ = F ψ := by
  have := hF.eq_zero (φ - ψ) (hφ.sub hψ) (h.mono fun x hx => by simp [hx])
  rw [hF.map_sub hφ hψ] at this
  exact sub_eq_zero.1 this

theorem mono (hF : IsSource F K) (hKL : K ⊆ L) (hL : IsCompact L) : IsSource F L where
  isCompact := hL
  map_add := hF.map_add
  map_smul := hF.map_smul
  eq_zero φ hφ h := hF.eq_zero φ hφ (h.filter_mono (nhdsSet_mono hKL))

protected theorem add (hF : IsSource F K) (hG : IsSource G L) : IsSource (F + G) (K ∪ L) where
  isCompact := hF.isCompact.union hG.isCompact
  map_add φ ψ hφ hψ := by
    simp only [Pi.add_apply, hF.map_add φ ψ hφ hψ, hG.map_add φ ψ hφ hψ]
    ring
  map_smul c φ hφ := by
    simp only [Pi.add_apply, hF.map_smul c φ hφ, hG.map_smul c φ hφ]
    ring
  eq_zero φ hφ h := by
    rw [nhdsSet_union, eventually_sup] at h
    simp [hF.eq_zero φ hφ h.1, hG.eq_zero φ hφ h.2]

protected theorem smul (hF : IsSource F K) (c : ℝ) : IsSource (c • F) K where
  isCompact := hF.isCompact
  map_add φ ψ hφ hψ := by
    simp only [Pi.smul_apply, smul_eq_mul, hF.map_add φ ψ hφ hψ]
    ring
  map_smul a φ hφ := by
    simp only [Pi.smul_apply, smul_eq_mul, hF.map_smul a φ hφ]
    ring
  eq_zero φ hφ h := by simp [hF.eq_zero φ hφ h]

protected theorem neg (hF : IsSource F K) : IsSource (-F) K := by
  simpa using hF.smul (-1)

protected theorem sub (hF : IsSource F K) (hG : IsSource G L) : IsSource (F - G) (K ∪ L) := by
  simpa [sub_eq_add_neg] using hF.add hG.neg

/-- A source supported in the empty set is zero on smooth functions. -/
theorem eq_zero_of_empty (hF : IsSource F ∅) {φ : E n → ℝ} (hφ : ContDiff ℝ ∞ φ) : F φ = 0 :=
  hF.eq_zero φ hφ (by simp)

end IsSource

/-- A bounded measurable function vanishing outside a compact set, times a continuous
function, is integrable. -/
theorem integrable_mul_of_bounded {f q : E n → ℝ} {K : Set (E n)} (hK : IsCompact K)
    (hf : AEStronglyMeasurable f volume) {C : ℝ} (hC : ∀ x, |f x| ≤ C)
    (hfK : ∀ x ∉ K, f x = 0) (hq : Continuous q) : Integrable fun x => f x * q x := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hq.continuousOn
  refine Integrable.mono'
    ((integrableOn_const (C := C * M) hK.measure_lt_top.ne).integrable_indicator
    hK.measurableSet) (hf.mul hq.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ K
  · rw [indicator_of_mem hx, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hC x) (by simpa using hM x hx) (abs_nonneg _)
      ((abs_nonneg _).trans (hC x))
  · simp [indicator_of_notMem hx, hfK x hx]

section Integrals

variable (hg : ∀ i j, ContDiff ℝ ∞ fun x => g x i j) (hdet : ∀ x, (g x).det ≠ 0)
include hg hdet

/-- The pairing `∫ f φ dV_g` of a bounded measurable `f` vanishing outside a compact set with a
continuous `φ` is integrable. -/
theorem integrable_pairing {f φ : E n → ℝ} {K : Set (E n)} (hK : IsCompact K)
    (hf : AEStronglyMeasurable f volume) {C : ℝ} (hC : ∀ x, |f x| ≤ C)
    (hfK : ∀ x ∉ K, f x = 0) (hφ : Continuous φ) :
    Integrable fun x => f x * φ x * √|(g x).det| := by
  have := integrable_mul_of_bounded hK hf hC hfK (q := fun x => φ x * √|(g x).det|)
    (hφ.mul (contDiff_sqrt_abs_det hg hdet).continuous)
  simpa only [mul_assoc] using this

/-- The source of a bounded measurable function `f` vanishing outside the compact set `K`. -/
theorem isSource_funSource {f : E n → ℝ} {K : Set (E n)} (hK : IsCompact K)
    (hf : AEStronglyMeasurable f volume) {C : ℝ} (hC : ∀ x, |f x| ≤ C)
    (hfK : ∀ x ∉ K, f x = 0) : IsSource (funSource g f) K where
  isCompact := hK
  map_add φ ψ hφ hψ := by
    simp only [funSource, Pi.add_apply]
    rw [← integral_add (integrable_pairing hg hdet hK hf hC hfK hφ.continuous)
      (integrable_pairing hg hdet hK hf hC hfK hψ.continuous)]
    congr 1
    ext x
    ring
  map_smul c φ hφ := by
    simp only [funSource, Pi.smul_apply, smul_eq_mul]
    rw [← integral_const_mul]
    congr 1
    ext x
    ring
  eq_zero φ hφ h := by
    simp only [funSource]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ K
    · simp [(h.self_of_nhdsSet x hx)]
    · simp [hfK x hx]

/-- The source `□_g P` of a bounded measurable `P` vanishing outside the compact set `K`. -/
theorem isSource_boxSource {P : E n → ℝ} {K : Set (E n)} (hK : IsCompact K)
    (hP : AEStronglyMeasurable P volume) {C : ℝ} (hC : ∀ x, |P x| ≤ C)
    (hPK : ∀ x ∉ K, P x = 0) : IsSource (boxSource g P) K where
  isCompact := hK
  map_add φ ψ hφ hψ := by
    simp only [boxSource]
    rw [← integral_add (integrable_pairing hg hdet hK hP hC hPK (continuous_box hg hdet hφ))
      (integrable_pairing hg hdet hK hP hC hPK (continuous_box hg hdet hψ))]
    congr 1
    ext x
    rw [show φ + ψ = fun y => φ y + ψ y from rfl, box_add hg hdet hφ hψ]
    ring
  map_smul c φ hφ := by
    simp only [boxSource]
    rw [← integral_const_mul]
    congr 1
    ext x
    rw [show c • φ = fun y => c * φ y from rfl, box_const_mul hg hdet hφ]
    ring
  eq_zero φ hφ h := by
    simp only [boxSource]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ K
    · have hev : φ =ᶠ[𝓝 x] 0 := by
        have := (h.filter_mono (nhds_le_nhdsSet hx))
        filter_upwards [this] with y hy
        simp [hy]
      simp [box_eq_zero_of_eventuallyEq hev]
    · simp [hPK x hx]

end Integrals

/-! ### Retarded solutions of sources -/

section Retarded

variable {F G : (E n → ℝ) → ℝ} {K L : Set (E n)}

theorem retardedS_add : retardedS g Y (F + G) = retardedS g Y F + retardedS g Y G := by rfl

theorem retardedS_sub : retardedS g Y (F - G) = retardedS g Y F - retardedS g Y G := by rfl

theorem retardedS_smul (c : ℝ) : retardedS g Y (c • F) = c • retardedS g Y F := by rfl

theorem retardedS_neg : retardedS g Y (-F) = -retardedS g Y F := by rfl

variable (hg : IsSpacetime g Y)
include hg

/-- `G^ret F` is additive on test functions. -/
theorem IsSource.retardedS_map_add (hF : IsSource F K) {h₁ h₂ : E n → ℝ}
    (hh₁ : ContDiff ℝ ∞ h₁) (hh₁' : HasCompactSupport h₁) (hh₂ : ContDiff ℝ ∞ h₂)
    (hh₂' : HasCompactSupport h₂) :
    retardedS g Y F (h₁ + h₂) = retardedS g Y F h₁ + retardedS g Y F h₂ := by
  simp only [retardedS]
  rw [advanced_add hg hh₁ hh₁' hh₂ hh₂', hF.map_add _ _ contDiff_advanced contDiff_advanced]

/-- `G^ret F` is homogeneous on test functions. -/
theorem IsSource.retardedS_map_smul (hF : IsSource F K) {h : E n → ℝ} (hh : ContDiff ℝ ∞ h)
    (hh' : HasCompactSupport h) (c : ℝ) :
    retardedS g Y F (c • h) = c * retardedS g Y F h := by
  simp only [retardedS]
  rw [advanced_smul hg hh hh', hF.map_smul _ _ contDiff_advanced]

/-- The advanced solution of a test function `h` vanishes near every compact set `K` with
`supp h ∩ J⁺(K) = ∅`. -/
theorem advanced_eventually_eq_zero_nhdsSet {h : E n → ℝ} (hh' : HasCompactSupport h)
    (hK : tsupport h ⊆ (causalFutureSet g Y K)ᶜ) :
    ∀ᶠ x in 𝓝ˢ K, advanced g Y h x = 0 := by
  have hC := isClosed_causalPastSet hg (Y := Y) hh'.isCompact
  have hKC : K ⊆ (causalPastSet g Y (tsupport h))ᶜ := by
    intro p hp hpC
    obtain ⟨q, hq, hpq⟩ := mem_causalPastSet.1 hpC
    exact hK hq (mem_causalFutureSet.2 ⟨p, hp, mem_causalFuture.2 (mem_causalPast.1 hpq)⟩)
  filter_upwards [hC.isOpen_compl.mem_nhdsSet.2 hKC] with x hx
  by_contra h0
  exact hx (support_advanced_subset h0)

/-- `G^ret F` vanishes outside `J⁺(K)`, an open set. -/
theorem IsSource.vanishesOn_retardedS (hF : IsSource F K) :
    VanishesOn (retardedS g Y F) (causalFutureSet g Y K)ᶜ :=
  fun _ _ hh' hK => hF.eq_zero _ contDiff_advanced (advanced_eventually_eq_zero_nhdsSet hg hh' hK)

theorem isOpen_compl_causalFutureSet (hK : IsCompact K) : IsOpen (causalFutureSet g Y K)ᶜ :=
  (isClosed_causalFutureSet hg hK).isOpen_compl

/-- For a smooth source `f`, `G^ret f` in the sense of sources is the retarded solution. -/
theorem agreesOn_retardedS_funSource {f : E n → ℝ} (hf : ContDiff ℝ ∞ f)
    (hf' : HasCompactSupport f) :
    AgreesOn g (retardedS g Y (funSource g f)) (retarded g Y f) univ :=
  fun _ hh hh' _ => (integral_retarded_mul hg hf hf' hh hh').symm

/-- `G^ret □_g P = P` for a bounded measurable `P` with compact support. -/
theorem agreesOn_retardedS_boxSource (P : E n → ℝ) :
    AgreesOn g (retardedS g Y (boxSource g P)) P univ := by
  intro h hh hh' _
  simp only [retardedS, boxSource]
  congr 1
  ext x
  rw [box_advanced hg hh hh']

end Retarded

/-! ### Agreement and vanishing -/

section Agree

variable {U W : (E n → ℝ) → ℝ} {u v : E n → ℝ} {V V' : Set (E n)}

theorem AgreesOn.mono (h : AgreesOn g U u V) (hV : V' ⊆ V) : AgreesOn g U u V' :=
  fun φ hφ hφ' hs => h φ hφ hφ' (hs.trans hV)

theorem VanishesOn.mono (h : VanishesOn U V) (hV : V' ⊆ V) : VanishesOn U V' :=
  fun φ hφ hφ' hs => h φ hφ hφ' (hs.trans hV)

/-- Agreement only depends on the function on `V`. -/
theorem AgreesOn.congr (h : AgreesOn g U u V) (huv : ∀ x ∈ V, u x = v x) : AgreesOn g U v V := by
  intro φ hφ hφ' hs
  rw [h φ hφ hφ' hs]
  congr 1
  ext x
  by_cases hx : x ∈ tsupport φ
  · rw [huv x (hs hx)]
  · simp [image_eq_zero_of_notMem_tsupport hx]

theorem AgreesOn.add_vanishesOn (h : AgreesOn g U u V) (hW : VanishesOn W V) :
    AgreesOn g (U + W) u V := fun φ hφ hφ' hs => by
  simp [h φ hφ hφ' hs, hW φ hφ hφ' hs]

theorem AgreesOn.sub_vanishesOn (h : AgreesOn g U u V) (hW : VanishesOn W V) :
    AgreesOn g (U - W) u V := fun φ hφ hφ' hs => by
  simp [h φ hφ hφ' hs, hW φ hφ hφ' hs]

theorem vanishesOn_iff_agreesOn_zero : VanishesOn U V ↔ AgreesOn g U 0 V := by
  simp [VanishesOn, AgreesOn]

end Agree

end

end LorentzianCalderon
