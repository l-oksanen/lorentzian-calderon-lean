module

public import LorentzianCalderon.Geometry.Lagrangian

public section

/-!
# Jacobi fields of geodesic variations

A geodesic variation is a smooth two-parameter map `Γ(s, u)` whose longitudinal curves
`u ↦ Γ(s, u)` are geodesics; its variation field `J(u) = ∂ₛΓ(0, u)` is a Jacobi field. In the
Lagrangian form used here, with `a(u) = (Γ(0, u), ∂ᵤΓ(0, u))`:

* `d/du ∂²L(a)((J, J'), (0, X)) = ∂²L(a)((J, J'), (X, X'))` for every vector field `X`
  (`IsGeodesicVariation.hasDerivAt_jacobi`), the linearized Euler–Lagrange equation;
* `dL(a)(J, J')` is constant (`IsGeodesicVariation.fderiv_lagrangian_eq`), the derivative of the
  conserved energy;
* `(J, J')(u)` is the image of `(J, J')(r)` under the derivative of the geodesic flow
  (`IsGeodesicVariation.eq_fderiv_flow`), so Jacobi fields are determined by their data at
  one point.
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Set Filter Function

variable {n : ℕ} {g : MatrixField n} {Y : E n → E n}

section Mixed

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem hasDerivAt_uncurry_fst {f : ℝ → ℝ → G} {O : Set (ℝ × ℝ)} (hO : IsOpen O)
    (hf : ContDiffOn ℝ ∞ (uncurry f) O) {s u : ℝ} (h : (s, u) ∈ O) :
    HasDerivAt (fun s => f s u) (fderiv ℝ (uncurry f) (s, u) (1, 0)) s := by
  have hd : HasFDerivAt (uncurry f) (fderiv ℝ (uncurry f) (s, u)) (s, u) :=
    ((hf.differentiableOn (by simp)).differentiableAt (hO.mem_nhds h)).hasFDerivAt
  exact hd.comp_hasDerivAt (x := s) (f := fun s => (s, u)) ((hasDerivAt_id s).prodMk
    (hasDerivAt_const s u))

theorem hasDerivAt_uncurry_snd {f : ℝ → ℝ → G} {O : Set (ℝ × ℝ)} (hO : IsOpen O)
    (hf : ContDiffOn ℝ ∞ (uncurry f) O) {s u : ℝ} (h : (s, u) ∈ O) :
    HasDerivAt (f s) (fderiv ℝ (uncurry f) (s, u) (0, 1)) u := by
  have hd : HasFDerivAt (uncurry f) (fderiv ℝ (uncurry f) (s, u)) (s, u) :=
    ((hf.differentiableOn (by simp)).differentiableAt (hO.mem_nhds h)).hasFDerivAt
  exact hd.comp_hasDerivAt (x := u) (f := fun u => (s, u)) ((hasDerivAt_const u s).prodMk
    (hasDerivAt_id u))

/-- Mixed partial derivatives commute: `∂ᵤ∂ₛf = ∂ₛ∂ᵤf`. -/
theorem hasDerivAt_mixed {f : ℝ → ℝ → G} {O : Set (ℝ × ℝ)} (hO : IsOpen O)
    (hf : ContDiffOn ℝ ∞ (uncurry f) O) {s u : ℝ} (h : (s, u) ∈ O) :
    HasDerivAt (fun u => deriv (fun s => f s u) s)
        (fderiv ℝ (fderiv ℝ (uncurry f)) (s, u) (1, 0) (0, 1)) u ∧
      HasDerivAt (fun s => deriv (f s) u)
        (fderiv ℝ (fderiv ℝ (uncurry f)) (s, u) (1, 0) (0, 1)) s := by
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ (uncurry f)) O := hf.fderiv_of_isOpen hO (by simp)
  have hDD : HasFDerivAt (fderiv ℝ (uncurry f)) (fderiv ℝ (fderiv ℝ (uncurry f)) (s, u)) (s, u) :=
    ((hD.differentiableOn (by simp)).differentiableAt (hO.mem_nhds h)).hasFDerivAt
  have hsymm : fderiv ℝ (fderiv ℝ (uncurry f)) (s, u) (0, 1) (1, 0) =
      fderiv ℝ (fderiv ℝ (uncurry f)) (s, u) (1, 0) (0, 1) :=
    ((hf.contDiffAt (hO.mem_nhds h)).isSymmSndFDerivAt (by simp)) _ _
  constructor
  · have h1 := (hDD.comp_hasDerivAt (x := u) (f := fun u => (s, u)) ((hasDerivAt_const u s).prodMk
      (hasDerivAt_id u))).clm_apply (hasDerivAt_const u ((1 : ℝ), (0 : ℝ)))
    simp only [map_zero, add_zero, hsymm] at h1
    refine h1.congr_of_eventuallyEq ?_
    have hOu : ∀ᶠ u' in 𝓝 u, (s, u') ∈ O :=
      (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hO.mem_nhds h)
    filter_upwards [hOu] with u' hu'
    exact (hasDerivAt_uncurry_fst hO hf hu').deriv
  · have h1 := (hDD.comp_hasDerivAt (x := s) (f := fun s => (s, u)) ((hasDerivAt_id s).prodMk
      (hasDerivAt_const s u))).clm_apply (hasDerivAt_const s ((0 : ℝ), (1 : ℝ)))
    simp only [map_zero, add_zero] at h1
    refine h1.congr_of_eventuallyEq ?_
    have hOs : ∀ᶠ s' in 𝓝 s, (s', u) ∈ O :=
      (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds (hO.mem_nhds h)
    filter_upwards [hOs] with s' hs'
    exact (hasDerivAt_uncurry_snd hO hf hs').deriv

theorem contDiffOn_deriv_uncurry_snd {f : ℝ → ℝ → G} {O : Set (ℝ × ℝ)} (hO : IsOpen O)
    (hf : ContDiffOn ℝ ∞ (uncurry f) O) :
    ContDiffOn ℝ ∞ (uncurry fun s u => deriv (f s) u) O := by
  have hD : ContDiffOn ℝ ∞ (fun p => fderiv ℝ (uncurry f) p ((0 : ℝ), (1 : ℝ))) O :=
    (hf.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const
  exact hD.congr fun p hp => (hasDerivAt_uncurry_snd hO hf (s := p.1) (u := p.2) hp).deriv

end Mixed

/-- `Γ` is a geodesic variation on `(-δ, δ) × (α, β)`: smooth, with geodesic longitudinal
curves `u ↦ Γ(s, u)`. -/
structure IsGeodesicVariation (g : MatrixField n) (Γ : ℝ → ℝ → E n) (δ α β : ℝ) : Prop where
  pos : 0 < δ
  smooth : ContDiffOn ℝ ∞ (uncurry Γ) (Ioo (-δ) δ ×ˢ Ioo α β)
  geodesic : ∀ s ∈ Ioo (-δ) δ, IsGeodesic g (Γ s) (Ioo α β)

/-- The variation field `J(u) = ∂ₛΓ(0, u)`. -/
def varField (Γ : ℝ → ℝ → E n) (u : ℝ) : E n := deriv (fun s => Γ s u) 0

theorem varField_def (Γ : ℝ → ℝ → E n) (u : ℝ) :
    varField Γ u =
      deriv (fun s => Γ s u) 0 := by rfl

namespace IsGeodesicVariation

variable {Γ : ℝ → ℝ → E n} {δ α β : ℝ}

lemma isOpen_rect : IsOpen (Ioo (-δ) δ ×ˢ Ioo α β) := isOpen_Ioo.prod isOpen_Ioo

lemma mem_rect (hv : IsGeodesicVariation g Γ δ α β) {u : ℝ} (hu : u ∈ Ioo α β) :
    ((0 : ℝ), u) ∈ Ioo (-δ) δ ×ˢ Ioo α β :=
  ⟨⟨by linarith [hv.pos], hv.pos⟩, hu⟩

theorem contDiffOn_varField (hv : IsGeodesicVariation g Γ δ α β) :
    ContDiffOn ℝ ∞ (varField Γ) (Ioo α β) := by
  have hD : ContDiffOn ℝ ∞ (fun u => fderiv ℝ (uncurry Γ) ((0 : ℝ), u) ((1 : ℝ), (0 : ℝ)))
      (Ioo α β) :=
    ((hv.smooth.fderiv_of_isOpen isOpen_rect (by simp)).comp
      (contDiffOn_const.prodMk contDiffOn_id) fun u hu => hv.mem_rect hu).clm_apply
      contDiffOn_const
  exact hD.congr fun u hu => (hasDerivAt_uncurry_fst isOpen_rect hv.smooth (hv.mem_rect hu)).deriv

theorem hasDerivAt_varField (hv : IsGeodesicVariation g Γ δ α β) {u : ℝ} (hu : u ∈ Ioo α β) :
    HasDerivAt (varField Γ) (deriv (varField Γ) u) u :=
  ((hv.contDiffOn_varField.differentiableOn (by simp)).differentiableAt
    (isOpen_Ioo.mem_nhds hu)).hasDerivAt

/-- The derivative in `s` of the initial data `(Γ(s, u), ∂ᵤΓ(s, u))` is `(J(u), J'(u))`. -/
theorem hasDerivAt_data (hv : IsGeodesicVariation g Γ δ α β) {u : ℝ} (hu : u ∈ Ioo α β) :
    HasDerivAt (fun s => (Γ s u, deriv (Γ s) u)) (varField Γ u, deriv (varField Γ) u) 0 := by
  obtain ⟨h1, h2⟩ := hasDerivAt_mixed isOpen_rect hv.smooth (hv.mem_rect hu)
  have hJ : deriv (varField Γ) u = fderiv ℝ (fderiv ℝ (uncurry Γ)) (0, u) (1, 0) (0, 1) :=
    h1.deriv
  rw [hJ]
  refine HasDerivAt.prodMk ?_ h2
  have := hasDerivAt_uncurry_fst isOpen_rect hv.smooth (hv.mem_rect hu)
  rwa [← this.deriv] at this

theorem contDiffOn_data (hv : IsGeodesicVariation g Γ δ α β) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => (Γ p.1 p.2, deriv (Γ p.1) p.2)) (Ioo (-δ) δ ×ˢ Ioo α β) :=
  hv.smooth.prodMk (contDiffOn_deriv_uncurry_snd isOpen_rect hv.smooth)

/-- The linearized Euler–Lagrange equation: for `a = (Γ(0, ·), ∂ᵤΓ(0, ·))` and every smooth
`X`, `d/du ∂²L(a)((J, J'), (0, X)) = ∂²L(a)((J, J'), (X, X'))`. -/
theorem hasDerivAt_jacobi (hg : IsSpacetime g Y) (hv : IsGeodesicVariation g Γ δ α β)
    {X : ℝ → E n} (hX : ContDiffOn ℝ ∞ X (Ioo α β)) {u : ℝ} (hu : u ∈ Ioo α β) :
    HasDerivAt (fun u => fderiv ℝ (fderiv ℝ (lagrangian g)) (Γ 0 u, deriv (Γ 0) u)
        (varField Γ u, deriv (varField Γ) u) (0, X u))
      (fderiv ℝ (fderiv ℝ (lagrangian g)) (Γ 0 u, deriv (Γ 0) u)
        (varField Γ u, deriv (varField Γ) u) (X u, deriv X u)) u := by
  set R := Ioo (-δ) δ ×ˢ Ioo α β
  have hL := contDiff_lagrangian hg
  have hXd : ∀ u ∈ Ioo α β, HasDerivAt X (deriv X u) u := fun u hu =>
    ((hX.differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hu)).hasDerivAt
  set Φ : ℝ → ℝ → ℝ := fun s u => fderiv ℝ (lagrangian g) (Γ s u, deriv (Γ s) u) (0, X u)
  have hΦ : ContDiffOn ℝ ∞ (uncurry Φ) R := by
    have hDL : ContDiff ℝ ∞ (fderiv ℝ (lagrangian g)) := hL.fderiv_right (m := ∞) (by simp)
    exact (hDL.comp_contDiffOn hv.contDiffOn_data).clm_apply
      (contDiffOn_const.prodMk (hX.comp contDiffOn_snd fun p hp => hp.2))
  obtain ⟨h1, h2⟩ := hasDerivAt_mixed isOpen_rect hΦ (hv.mem_rect hu)
  have hs : HasDerivAt (fun s => Φ s u)
      (fderiv ℝ (fderiv ℝ (lagrangian g)) (Γ 0 u, deriv (Γ 0) u)
        (varField Γ u, deriv (varField Γ) u) (0, X u)) 0 := by
    have := hasDerivAt_fderiv_apply hL (hv.hasDerivAt_data hu) (hasDerivAt_const (0 : ℝ)
      ((0 : E n), X u))
    simpa using this
  have hEL : ∀ s ∈ Ioo (-δ) δ, deriv (Φ s) u =
      fderiv ℝ (lagrangian g) (Γ s u, deriv (Γ s) u) (X u, deriv X u) := fun s hs =>
    ((hv.geodesic s hs).hasDerivAt_momentum hg hu (hXd u hu)).deriv
  have hu2 : HasDerivAt (fun s => deriv (Φ s) u)
      (fderiv ℝ (fderiv ℝ (lagrangian g)) (Γ 0 u, deriv (Γ 0) u)
        (varField Γ u, deriv (varField Γ) u) (X u, deriv X u)) 0 := by
    have := hasDerivAt_fderiv_apply hL (hv.hasDerivAt_data hu) (hasDerivAt_const (0 : ℝ)
      (X u, deriv X u))
    simp only [map_zero, add_zero] at this
    refine this.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds (by linarith [hv.pos] : -δ < 0) hv.pos] with s hs
    exact hEL s hs
  rw [← h2.unique hu2]
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds hu] with u' hu'
  have := hasDerivAt_fderiv_apply hL (hv.hasDerivAt_data hu') (hasDerivAt_const (0 : ℝ)
    ((0 : E n), X u'))
  simp only [map_zero, add_zero] at this
  exact this.deriv.symm

/-- The derivative of the conserved energy: `dL(a)(J, J')` is constant along the variation. -/
theorem fderiv_lagrangian_eq (hg : IsSpacetime g Y) (hv : IsGeodesicVariation g Γ δ α β)
    {u u₀ : ℝ} (hu : u ∈ Ioo α β) (hu₀ : u₀ ∈ Ioo α β) :
    fderiv ℝ (lagrangian g) (Γ 0 u, deriv (Γ 0) u) (varField Γ u, deriv (varField Γ) u) =
      fderiv ℝ (lagrangian g) (Γ 0 u₀, deriv (Γ 0) u₀)
        (varField Γ u₀, deriv (varField Γ) u₀) := by
  have hL := contDiff_lagrangian hg
  have hd : ∀ u ∈ Ioo α β, HasDerivAt (fun s => lagrangian g (Γ s u, deriv (Γ s) u))
      (fderiv ℝ (lagrangian g) (Γ 0 u, deriv (Γ 0) u)
        (varField Γ u, deriv (varField Γ) u)) 0 := fun u hu =>
    (hL.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt 0 (hv.hasDerivAt_data hu)
  refine (hd u hu).unique ((hd u₀ hu₀).congr_of_eventuallyEq ?_)
  filter_upwards [Ioo_mem_nhds (by linarith [hv.pos] : -δ < 0) hv.pos] with s hs
  simpa only [lagrangian_def] using
    (hv.geodesic s hs).form_deriv_eq hg subset_rfl ordConnected_Ioo hu hu₀

/-- Jacobi fields are determined by their data at one point: `(J, J')(u)` is the derivative
of the geodesic flow `X` applied to `(J, J')(r)`. -/
theorem eq_fderiv_flow (hv : IsGeodesicVariation g Γ δ α β)
    {X : ℝ × ℝ × (E n × E n) × ℝ → E n × E n} (hS : IsOpen (sprayDomain g))
    (hX : ContDiffOn ℝ ∞ X (sprayDomain g))
    (hrep : ∀ (p : ℝ) (x : ℝ → E n × E n) (I : Set ℝ),
      Facts.IsODESolution (sprayField g) univ p x I → ∀ t₀ ∈ I, ∀ t ∈ I, X (t, t₀, x t₀, p) = x t)
    {u r : ℝ} (hu : u ∈ Ioo α β) (hr : r ∈ Ioo α β) :
    (varField Γ u, deriv (varField Γ) u) =
      fderiv ℝ X (u, r, (Γ 0 r, deriv (Γ 0) r), 0)
        (0, 0, (varField Γ r, deriv (varField Γ) r), 0) := by
  have hsol : ∀ s ∈ Ioo (-δ) δ, Facts.IsODESolution (sprayField g) univ 0
      (fun t => (Γ s t, deriv (Γ s) t)) (Ioo α β) := fun s hs =>
    (hv.geodesic s hs).isODESolution subset_rfl ordConnected_Ioo 0
  have hmem : (u, r, (Γ 0 r, deriv (Γ 0) r), (0 : ℝ)) ∈ sprayDomain g :=
    mem_sprayDomain (hsol 0 ⟨by linarith [hv.pos], hv.pos⟩) hu hr
  have hXd : HasFDerivAt X (fderiv ℝ X (u, r, (Γ 0 r, deriv (Γ 0) r), 0))
      (u, r, (Γ 0 r, deriv (Γ 0) r), 0) :=
    ((hX.differentiableOn (by simp)).differentiableAt (hS.mem_nhds hmem)).hasFDerivAt
  have hin : HasDerivAt (fun s => (u, r, (Γ s r, deriv (Γ s) r), (0 : ℝ)))
      ((0 : ℝ), (0 : ℝ), (varField Γ r, deriv (varField Γ) r), (0 : ℝ)) 0 :=
    (hasDerivAt_const _ _).prodMk ((hasDerivAt_const _ _).prodMk
      ((hv.hasDerivAt_data hr).prodMk (hasDerivAt_const _ _)))
  have h := hXd.comp_hasDerivAt (x := (0 : ℝ)) hin
  refine (hv.hasDerivAt_data hu).unique (h.congr_of_eventuallyEq ?_)
  filter_upwards [Ioo_mem_nhds (by linarith [hv.pos] : -δ < 0) hv.pos] with s hs
  exact (hrep 0 _ _ (hsol s hs) r hr u hu).symm

end IsGeodesicVariation

end

end LorentzianCalderon
