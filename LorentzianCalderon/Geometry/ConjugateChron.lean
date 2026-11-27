module

public import LorentzianCalderon.Geometry.Jacobi
public import LorentzianCalderon.Geometry.Variation

public section

/-!
# Null geodesics beyond a conjugate point

If `exp_y` is singular at `r σ'(0)` for a future-directed null geodesic `σ` from `y = σ 0` and
`0 < r < b`, then `σ b` lies in the chronological future of `y`
(`Facts.chronLT_of_conjugate`; O'Neill, Semi-Riemannian geometry, Corollary 14.5, p. 404, and
Proposition 10.48, p. 296).

The proof, in the single chart `ℝ^{1+n}`: a kernel vector `u₀` of `d(exp_y)_{r σ'(0)}` gives
the Jacobi field `J(u) = ∂ₛ exp_y(u (σ'(0) + s u₀))` with `J(0) = J(r) = 0`, `J'(0) = u₀`.
It is orthogonal to `σ'`, and `J'(r)` is not a multiple of `σ'(r)`. The broken field equal to
`J + ε W` on `[0, r]` and to `ε W` on `[r, b]`, for a suitable field `W ⊥ σ'` vanishing at `0`
and `b`, has negative index form; adding a second-order term `s² Z` along a field `N` with
`g(σ', N) = 1/2` makes the second variation of the energy density negative at every point, so
the curves `σ + s V + s² Z` are timelike for small `s > 0` (`eventually_isPathOn_variation`).
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Set Filter Function

variable {n : ℕ} {g : MatrixField n} {Y : E n → E n}

/-- The Euler–Lagrange equation in the form used for the variations: if `∂_ξ L(σ, σ') X = f`
along a geodesic `σ`, then `dL(σ, σ')(X, X') = f'`. -/
theorem IsGeodesic.fderiv_lagrangian_eq_deriv (hg : IsSpacetime g Y) {σ : ℝ → E n}
    {I U : Set ℝ} (hσ : IsGeodesic g σ I) (hU : IsOpen U) (hUI : U ⊆ I) {X : ℝ → E n}
    (hX : ContDiffOn ℝ ∞ X U) {f : ℝ → ℝ}
    (hf : ∀ u ∈ U, fderiv ℝ (lagrangian g) (σ u, deriv σ u) (0, X u) = f u) {u : ℝ}
    (hu : u ∈ U) :
    fderiv ℝ (lagrangian g) (σ u, deriv σ u) (X u, deriv X u) = deriv f u := by
  have hXd : HasDerivAt X (deriv X u) u :=
    ((hX.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hu)).hasDerivAt
  have h := hσ.hasDerivAt_momentum hg (hUI hu) hXd
  refine (h.congr_of_eventuallyEq ?_).deriv.symm
  filter_upwards [hU.mem_nhds hu] with u' hu'
  exact (hf u' hu').symm

/-- A smooth field `N` along a geodesic with nonzero velocity, with `g(σ', N) = 1/2`. -/
theorem IsGeodesic.exists_dual_field (hg : IsSpacetime g Y) {σ : ℝ → E n} {I : Set ℝ}
    (hσ : IsGeodesic g σ I) (hne : ∀ u ∈ I, deriv σ u ≠ 0) :
    ∃ N : ℝ → E n, ContDiffOn ℝ ∞ N I ∧ ∀ u ∈ I, form (g (σ u)) (deriv σ u) (N u) = 1 / 2 := by
  set w : ℝ → E n := fun u => WithLp.toLp 2 (g (σ u) *ᵥ (deriv σ u).ofLp)
  have hw : ContDiffOn ℝ ∞ w I := by
    refine contDiffOn_piLp' (𝕜 := ℝ) (p := 2) fun k => ?_
    simp only [w, Matrix.mulVec, dotProduct]
    refine ContDiffOn.sum fun j _ => ?_
    exact ((hg.smooth k j).comp_contDiffOn hσ.smooth).mul
      ((EuclideanSpace.proj j : E n →L[ℝ] ℝ).contDiff.comp_contDiffOn hσ.contDiffOn_deriv)
  set ν : ℝ → ℝ := fun u => form (g (σ u)) (deriv σ u) (w u)
  have hν : ContDiffOn ℝ ∞ ν I :=
    (contDiff_form hg).comp_contDiffOn (hσ.smooth.prodMk (hσ.contDiffOn_deriv.prodMk hw))
  have hν0 : ∀ u ∈ I, ν u ≠ 0 := fun u hu => by
    have hsymm := hg.symm (σ u)
    have e : ν u = (g (σ u) *ᵥ (deriv σ u).ofLp) ⬝ᵥ (g (σ u) *ᵥ (deriv σ u).ofLp) := by
      simp only [ν, w, form_eq_dotProduct, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
        hsymm]
    rw [e]
    intro h0
    have hz := dotProduct_self_eq_zero.1 h0
    obtain ⟨z, hz'⟩ := exists_form_ne_zero hg (σ u) (hne u hu)
    refine hz' ?_
    rw [form_eq_dotProduct, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsymm, hz,
      zero_dotProduct]
  refine ⟨fun u => (2 * ν u)⁻¹ • w u,
    ((contDiffOn_const.mul hν).inv fun u hu => mul_ne_zero two_ne_zero (hν0 u hu)).smul hw,
    fun u hu => ?_⟩
  rw [form_smul_right]
  have := hν0 u hu
  change (2 * ν u)⁻¹ * ν u = 1 / 2
  field_simp

/-- The variation `Γ(s, u) = exp_y (u (σ'(0) + s u₀))` of a geodesic `σ` from `y = σ 0`
through geodesics. -/
theorem IsGeodesic.exists_expVariation (hg : IsSpacetime g Y) {σ : ℝ → E n} {I : Set ℝ}
    (hσ : IsGeodesic g σ I) {α β : ℝ} (hα : α < 0) (hβ : 0 < β) (hI : Icc α β ⊆ I)
    (u₀ : E n) :
    ∃ δ, IsGeodesicVariation g (fun s u => expMap g (σ 0) (u • (deriv σ 0 + s • u₀))) δ α β ∧
      (∀ s ∈ Ioo (-δ) δ,
        deriv (fun u : ℝ => expMap g (σ 0) (u • (deriv σ 0 + s • u₀))) 0 = deriv σ 0 + s • u₀) ∧
      ∀ u ∈ Ioo α β, expMap g (σ 0) (u • deriv σ 0) = σ u := by
  obtain ⟨X, hS, -, -⟩ := exists_sprayFlow hg
  have h0 : (0 : ℝ) ∈ Icc α β := ⟨hα.le, hβ.le⟩
  have hsol := hσ.isODESolution hI ordConnected_Icc 0
  have hA := mem_sprayDomain hsol (left_mem_Icc.2 (hα.trans hβ).le) h0
  have hB := mem_sprayDomain hsol (right_mem_Icc.2 (hα.trans hβ).le) h0
  set O : Set ℝ := { s | (α, (0 : ℝ), (σ 0, deriv σ 0 + s • u₀), (0 : ℝ)) ∈ sprayDomain g ∧
    (β, (0 : ℝ), (σ 0, deriv σ 0 + s • u₀), (0 : ℝ)) ∈ sprayDomain g }
  have hO : IsOpen O := (hS.preimage (by fun_prop)).inter (hS.preimage (by fun_prop))
  have h0O : (0 : ℝ) ∈ O := by simpa [O] using And.intro hA hB
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hO 0 h0O
  have hsO : ∀ s ∈ Ioo (-δ) δ, s ∈ O := fun s hs => hball (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]; exact hs)
  have h0αβ : (0 : ℝ) ∈ Ioo α β := ⟨hα, hβ⟩
  have key : ∀ s ∈ Ioo (-δ) δ, ∃ γ : ℝ → E n, IsGeodesic g γ (Ioo α β) ∧
      deriv γ 0 = deriv σ 0 + s • u₀ ∧ ∀ u ∈ Ioo α β,
        InExpDomain g (σ 0) (u • (deriv σ 0 + s • u₀)) ∧
          expMap g (σ 0) (u • (deriv σ 0 + s • u₀)) = γ u := fun s hs => by
    obtain ⟨γ, hγ, hγ0, hγ0'⟩ := exists_isGeodesic_of_mem_sprayDomain hg hα hβ (hsO s hs).1
      (hsO s hs).2
    refine ⟨γ, hγ, hγ0', fun u hu => ?_⟩
    have := hγ.expMap_smul_eq hg (ordConnected_Ioo.uIcc_subset h0αβ hu)
    rwa [hγ0, hγ0'] at this
  refine ⟨δ, ⟨hδ, ?_, fun s hs => ?_⟩, fun s hs => ?_, fun u hu => ?_⟩
  · refine (contDiffOn_expMap hg).comp
      (f := fun p : ℝ × ℝ => (σ 0, p.2 • (deriv σ 0 + p.1 • u₀))) (by fun_prop) ?_
    rintro ⟨s, u⟩ ⟨hs, hu⟩
    obtain ⟨γ, -, -, hγ⟩ := key s hs
    exact (hγ u hu).1
  · obtain ⟨γ, hγ, -, hγe⟩ := key s hs
    exact hγ.congr fun u hu => (hγe u hu).2
  · obtain ⟨γ, -, hγ0', hγe⟩ := key s hs
    refine (Filter.EventuallyEq.deriv_eq ?_).trans hγ0'
    filter_upwards [isOpen_Ioo.mem_nhds h0αβ] with u hu
    exact (hγe u hu).2
  · exact (hσ.expMap_smul_eq hg ((ordConnected_Ioo.uIcc_subset h0αβ hu).trans
      (Ioo_subset_Icc_self.trans hI))).2

/-- The variation `Γ(s, u) = σ(u + c s (u - r))` of a geodesic by affine reparametrizations. -/
theorem IsGeodesic.affineVariation {σ : ℝ → E n} {I : Set ℝ} (hσ : IsGeodesic g σ I)
    {α β r c δ : ℝ} (hδ : 0 < δ)
    (hsub : ∀ s ∈ Ioo (-δ) δ, ∀ u ∈ Ioo α β, u + c * s * (u - r) ∈ I) :
    IsGeodesicVariation g (fun s u => σ (u + c * s * (u - r))) δ α β := by
  refine ⟨hδ, ?_, fun s hs => ?_⟩
  · exact hσ.smooth.comp (by fun_prop : ContDiff ℝ ∞ fun p : ℝ × ℝ =>
      p.2 + c * p.1 * (p.2 - r)).contDiffOn fun p hp => hsub p.1 hp.1 p.2 hp.2
  · have heq : ∀ u, (1 + c * s) * u + -(c * s * r) = u + c * s * (u - r) := fun u => by ring
    have h := (hσ.comp_affine (1 + c * s) (-(c * s * r))).mono (J := Ioo α β)
      (fun u hu => by show (1 + c * s) * u + -(c * s * r) ∈ I; rw [heq]; exact hsub s hs u hu) isOpen_Ioo
    exact h.congr fun u _ => by simp only [heq]

namespace Facts

/-- Beyond a conjugate point a future-directed null geodesic enters the chronological future
of its initial point. O'Neill, Semi-Riemannian geometry, Corollary 14.5, p. 404, with conjugate
points characterized by the singularity of the exponential map, Proposition 10.10, p. 271. -/
theorem chronLT_of_conjugate {g : MatrixField n} {Y : E n → E n} (hg : IsSpacetime g Y)
    {σ : ℝ → E n} {I : Set ℝ} (hσ : IsGeodesic g σ I) {b r : ℝ} (hbI : Set.Icc 0 b ⊆ I)
    (hnull : form (g (σ 0)) (deriv σ 0) (deriv σ 0) = 0)
    (hfut : IsFutureCausal g Y (σ 0) (deriv σ 0))
    (hr : r ∈ Set.Ioo 0 b) (hconj : IsConjugateAt g (σ 0) (r • deriv σ 0)) :
    ChronLT g Y (σ 0) (σ b) := by
  have hb : 0 < b := hr.1.trans hr.2
  obtain ⟨ε₀, hε₀, hε₀I⟩ := exists_Icc_subset_of_isOpen hσ.isOpen hb.le hbI
  set α : ℝ := -(ε₀ / 2) with hαdef
  set β : ℝ := b + ε₀ / 2 with hβdef
  have hα : α < 0 := by linarith
  have hβ : 0 < β := by linarith
  have hαβI : Icc α β ⊆ I := (Icc_subset_Icc (by linarith) (by linarith)).trans hε₀I
  have hUI : Ioo α β ⊆ I := Ioo_subset_Icc_self.trans hαβI
  have hbU : Icc 0 b ⊆ Ioo α β := Icc_subset_Ioo hα (by linarith)
  have h0U : (0 : ℝ) ∈ Ioo α β := hbU ⟨le_rfl, hb.le⟩
  have hrU : r ∈ Ioo α β := hbU ⟨hr.1.le, hr.2.le⟩
  have hσU : IsGeodesic g σ (Ioo α β) := hσ.mono hUI isOpen_Ioo
  have hL := contDiff_lagrangian hg
  have hDL : ContDiff ℝ ∞ (fderiv ℝ (lagrangian g)) := hL.fderiv_right (m := ∞) (by simp)
  have hD2L : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ (lagrangian g))) :=
    hDL.fderiv_right (m := ∞) (by simp)
  have hsym : ∀ z v w, fderiv ℝ (fderiv ℝ (lagrangian g)) z v w =
      fderiv ℝ (fderiv ℝ (lagrangian g)) z w v := fun z v w =>
    (hL.contDiffAt.isSymmSndFDerivAt (by simp)) v w
  have hd : ∀ {f : ℝ → E n}, ContDiffOn ℝ ∞ f (Ioo α β) → ∀ u ∈ Ioo α β,
      HasDerivAt f (deriv f u) u := fun hf u hu =>
    ((hf.differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hu)).hasDerivAt
  have hderivs : ∀ {f : ℝ → E n}, ContDiffOn ℝ ∞ f (Ioo α β) →
      ContDiffOn ℝ ∞ (deriv f) (Ioo α β) := fun hf =>
    hf.deriv_of_isOpen isOpen_Ioo (m := ∞) (by simp)
  have hσs : ContDiffOn ℝ ∞ σ (Ioo α β) := hσU.smooth
  have hσ's : ContDiffOn ℝ ∞ (deriv σ) (Ioo α β) := hσU.contDiffOn_deriv
  have hsplit : ∀ (x y : E n) (t : ℝ),
      ((0 : E n), x + t • y) = ((0 : E n), x) + t • ((0 : E n), y) := fun x y t => by
    ext <;> simp
  obtain ⟨u₀, hu₀, hker⟩ : ∃ u₀, u₀ ≠ 0 ∧ fderiv ℝ (expMap g (σ 0)) (r • deriv σ 0) u₀ = 0 := by
    by_contra! h
    refine (isConjugateAt_iff.1 hconj) ⟨fun a c hac => ?_, ?_⟩
    · by_contra hne
      exact h (a - c) (sub_ne_zero.2 hne) (by rw [map_sub, hac, sub_self])
    · refine (LinearMap.injective_iff_surjective (f := ((fderiv ℝ (expMap g (σ 0))
        (r • deriv σ 0)) : E n →ₗ[ℝ] E n))).1 fun a c hac => ?_
      by_contra hne
      exact h (a - c) (sub_ne_zero.2 hne) (by
        change fderiv ℝ (expMap g (σ 0)) (r • deriv σ 0) a =
          fderiv ℝ (expMap g (σ 0)) (r • deriv σ 0) c at hac
        rw [map_sub, hac, sub_self])
  obtain ⟨δ, hv, hΓd0, hΓσ⟩ := hσ.exists_expVariation hg hα hβ hαβI u₀
  set Γ : ℝ → ℝ → E n := fun s u => expMap g (σ 0) (u • (deriv σ 0 + s • u₀)) with hΓdef
  set J := varField Γ with hJdef
  have hΓ0 : ∀ u ∈ Ioo α β, Γ 0 u = σ u := fun u hu => by
    simp only [Γ, zero_smul, add_zero]
    exact hΓσ u hu
  have hdata : ∀ u ∈ Ioo α β, (Γ 0 u, deriv (Γ 0) u) = (σ u, deriv σ u) := fun u hu => by
    refine Prod.ext (hΓ0 u hu) (Filter.EventuallyEq.deriv_eq ?_)
    filter_upwards [isOpen_Ioo.mem_nhds hu] with u' hu'
    exact hΓ0 u' hu'
  have hJs : ContDiffOn ℝ ∞ J (Ioo α β) := hv.contDiffOn_varField
  have hJ's : ContDiffOn ℝ ∞ (deriv J) (Ioo α β) := hderivs hJs
  have hJ0 : J 0 = 0 := by
    show varField Γ 0 = 0
    rw [varField_def]
    simp only [Γ, zero_smul, expMap_zero hg]
    exact deriv_const _ _
  have hJr : J r = 0 := by
    have hdom : InExpDomain g (σ 0) (r • deriv σ 0) :=
      (hσ.expMap_smul_eq hg ((uIcc_subset_Icc ⟨le_rfl, hb.le⟩ ⟨hr.1.le, hr.2.le⟩).trans
        hbI)).1
    have hexpd : DifferentiableAt ℝ (expMap g (σ 0)) (r • deriv σ 0) := by
      have := ((contDiffOn_expMap hg).differentiableOn (by simp)).differentiableAt
        ((isOpen_expDomain hg).mem_nhds (show (σ 0, r • deriv σ 0) ∈
          { p : E n × E n | InExpDomain g p.1 p.2 } from hdom))
      exact this.comp (r • deriv σ 0) ((differentiableAt_const _).prodMk differentiableAt_id)
    have hline : HasDerivAt (fun s : ℝ => r • (deriv σ 0 + s • u₀)) (r • u₀) 0 := by
      have := (((hasDerivAt_id (0 : ℝ)).smul_const u₀).const_add (deriv σ 0)).const_smul r
      simp only [id, one_smul] at this
      exact this
    have hpt : r • (deriv σ 0 + (0 : ℝ) • u₀) = r • deriv σ 0 := by simp
    have h1 : HasFDerivAt (expMap g (σ 0)) (fderiv ℝ (expMap g (σ 0)) (r • deriv σ 0))
        (r • (deriv σ 0 + (0 : ℝ) • u₀)) := by
      rw [hpt]
      exact hexpd.hasFDerivAt
    have h2 := h1.comp_hasDerivAt (0 : ℝ) hline
    show varField Γ r = 0
    rw [varField_def]
    have : (fun s => Γ s r) = expMap g (σ 0) ∘ fun s : ℝ => r • (deriv σ 0 + s • u₀) := rfl
    rw [this, h2.deriv, map_smul, hker, smul_zero]
  have hJ'0 : deriv J 0 = u₀ := by
    have h1 := (hasFDerivAt_snd (p := (Γ 0 0, deriv (Γ 0) 0))).comp_hasDerivAt (0 : ℝ)
      (hv.hasDerivAt_data h0U)
    simp only [ContinuousLinearMap.coe_snd'] at h1
    have h2 : HasDerivAt (fun s => deriv (Γ s) 0) u₀ 0 := by
      have : HasDerivAt (fun s : ℝ => deriv σ 0 + s • u₀) u₀ 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u₀).const_add (deriv σ 0)
      refine this.congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds (by linarith [hv.pos] : -δ < 0) hv.pos] with s hs
      exact hΓd0 s hs
    exact h1.unique h2
  have hJac : ∀ {X : ℝ → E n}, ContDiffOn ℝ ∞ X (Ioo α β) → ∀ u ∈ Ioo α β,
      HasDerivAt (fun u => fderiv ℝ (fderiv ℝ (lagrangian g)) (σ u, deriv σ u)
          (J u, deriv J u) (0, X u))
        (fderiv ℝ (fderiv ℝ (lagrangian g)) (σ u, deriv σ u)
          (J u, deriv J u) (X u, deriv X u)) u := by
    intro X hX u hu
    have h := hv.hasDerivAt_jacobi hg hX hu
    rw [hdata u hu] at h
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds hu] with u' hu'
    exact (congrArg (fun z => fderiv ℝ (fderiv ℝ (lagrangian g)) z (J u', deriv J u') (0, X u'))
      (hdata u' hu')).symm
  have hEL : ∀ {X : ℝ → E n}, ContDiffOn ℝ ∞ X (Ioo α β) → ∀ {f : ℝ → ℝ},
      (∀ u ∈ Ioo α β, fderiv ℝ (lagrangian g) (σ u, deriv σ u) (0, X u) = f u) →
      ∀ u ∈ Ioo α β, fderiv ℝ (lagrangian g) (σ u, deriv σ u) (X u, deriv X u) = deriv f u :=
    fun hX _ hf _ hu => hσ.fderiv_lagrangian_eq_deriv hg isOpen_Ioo hUI hX hf hu
  set κ := fderiv ℝ (lagrangian g) (σ 0, deriv σ 0) (J 0, deriv J 0)
  have hκ : ∀ u ∈ Ioo α β,
      fderiv ℝ (lagrangian g) (σ u, deriv σ u) (J u, deriv J u) = κ := fun u hu => by
    have := hv.fderiv_lagrangian_eq hg hu h0U
    rwa [hdata u hu, hdata 0 h0U] at this
  set f : ℝ → ℝ := fun u => fderiv ℝ (lagrangian g) (σ u, deriv σ u) (0, J u) - κ * u
  have hfd : ∀ u ∈ Ioo α β, HasDerivAt f 0 u := fun u hu => by
    have h := (hσ.hasDerivAt_momentum hg (hUI hu) (hv.hasDerivAt_varField hu)).sub
      ((hasDerivAt_id u).const_mul κ)
    convert h using 1
    · funext t
      simp [f, J]
    · rw [hκ u hu]
      ring
  have hconst : ∀ x ∈ Ioo α β, ∀ y ∈ Ioo α β, f x = f y := fun x hx y hy =>
    isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun u hu => (hfd u hu).differentiableAt.differentiableWithinAt)
      (fun u hu => (hfd u hu).deriv) hx hy
  have hf0 : f 0 = 0 := by simp [f, hJ0, Prod.mk_zero_zero]
  have hκ0 : κ = 0 := by
    have := hconst r hrU 0 h0U
    simp only [f, hJr, Prod.mk_zero_zero, map_zero, zero_sub, hf0] at this
    have hr0 : r ≠ 0 := hr.1.ne'
    have : κ * r = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right hr0
  have hJorth : ∀ u ∈ Ioo α β, fderiv ℝ (lagrangian g) (σ u, deriv σ u) (0, J u) = 0 :=
    fun u hu => by
      have := hconst u hu 0 h0U
      simp only [f, hκ0, zero_mul, sub_zero] at this
      rwa [hJ0, Prod.mk_zero_zero, map_zero] at this
  have hnotpar : ∀ c : ℝ, deriv J r ≠ c • deriv σ r := by
    intro c hc
    obtain ⟨X, hS, hX, hrep⟩ := exists_sprayFlow hg
    have e1 := hv.eq_fderiv_flow hS hX hrep h0U hrU
    rw [hdata r hrU, ← hJdef] at e1
    set δ₂ := ε₀ / (2 * ((|c| + 1) * (b + ε₀))) with hδ₂def
    have hδ₂ : 0 < δ₂ := by positivity
    have hsub : ∀ s ∈ Ioo (-δ₂) δ₂, ∀ u ∈ Ioo α β, u + c * s * (u - r) ∈ I := by
      intro s hs u hu
      have hs' : |s| < δ₂ := abs_lt.2 hs
      have hur : |u - r| ≤ b + ε₀ :=
        abs_le.2 ⟨by linarith [hu.1, hr.2], by linarith [hu.2, hr.1]⟩
      have hc1 : |c| ≤ |c| + 1 := by linarith
      have h1 : |c * s * (u - r)| ≤ (|c| + 1) * δ₂ * (b + ε₀) := by
        rw [abs_mul, abs_mul]
        exact mul_le_mul (mul_le_mul hc1 hs'.le (abs_nonneg _) (by positivity)) hur
          (abs_nonneg _) (by positivity)
      have h2 : (|c| + 1) * δ₂ * (b + ε₀) = ε₀ / 2 := by
        rw [hδ₂def]
        field_simp
      have h3 := abs_le.1 (h1.trans h2.le)
      exact hε₀I ⟨by linarith [hu.1, h3.1], by linarith [hu.2, h3.2]⟩
    have hv₂ := hσ.affineVariation hδ₂ hsub
    set Γ₂ : ℝ → ℝ → E n := fun s u => σ (u + c * s * (u - r)) with hΓ₂def
    set K := varField Γ₂ with hKdef
    have hK : ∀ u ∈ Ioo α β, K u = (c * (u - r)) • deriv σ u := fun u hu => by
      have hin : HasDerivAt (fun s : ℝ => u + c * s * (u - r)) (c * (u - r)) 0 := by
        have := (((hasDerivAt_id (0 : ℝ)).const_mul c).mul_const (u - r)).const_add u
        simpa using this
      have hσd : HasDerivAt σ (deriv σ (u + c * 0 * (u - r))) (u + c * 0 * (u - r)) := by
        simpa using hσU.hasDerivAt hu
      have := (hσd.scomp (0 : ℝ) hin).deriv
      simp only [mul_zero, zero_mul, add_zero] at this
      rw [hKdef, varField_def]
      exact this
    have hKr : K r = 0 := by rw [hK r hrU]; simp
    have hK'r : deriv K r = c • deriv σ r := by
      have h := (((hasDerivAt_id r).sub_const r).const_mul c).smul (hσU.hasDerivAt_deriv hrU)
      have h' : HasDerivAt K ((c * (id r - r)) • deriv (deriv σ) r + (c * 1) • deriv σ r) r :=
        h.congr_of_eventuallyEq (by
          filter_upwards [isOpen_Ioo.mem_nhds hrU] with u hu
          exact hK u hu)
      rw [h'.deriv]
      simp
    have hΓ₂0 : Γ₂ 0 = σ := funext fun u => by simp [Γ₂]
    have e2 := hv₂.eq_fderiv_flow hS hX hrep h0U hrU
    rw [hΓ₂0, ← hKdef] at e2
    rw [hJr, hc, ← hK'r, ← hKr] at e1
    have e3 := e1.trans e2.symm
    have hc0 : c = 0 := by
      have h := congrArg Prod.fst e3
      simp only [hJ0, hK 0 h0U] at h
      rcases smul_eq_zero.1 h.symm with h | h
      · rcases mul_eq_zero.1 h with h | h
        · exact h
        · exact absurd (by linarith : r = 0) hr.1.ne'
      · exact absurd h hfut.ne_zero
    have e4 := hv.eq_fderiv_flow hS hX hrep h0U hrU
    rw [← hJdef, hJr, hc, hc0, zero_smul, Prod.mk_zero_zero, Prod.mk_zero_zero, Prod.mk_zero_zero,
      Prod.mk_zero_zero, map_zero] at e4
    exact hu₀ (hJ'0 ▸ (Prod.ext_iff.1 e4).2)
  obtain ⟨N, hN, hNσ⟩ := hσU.exists_dual_field hg fun u hu =>
    hσ.deriv_ne_zero hg hUI ordConnected_Ioo h0U hfut.ne_zero hu
  set j := deriv J r with hjdef
  set c₀ := 2 * form (g (σ r)) j (N r) with hc₀def
  have hm : j - c₀ • deriv σ r ≠ 0 := fun h => hnotpar c₀ (sub_eq_zero.1 h)
  obtain ⟨e, he⟩ : ∃ e, form (g (σ r)) (j - c₀ • deriv σ r) e < 0 := by
    obtain ⟨e, he⟩ := exists_form_ne_zero hg (σ r) hm
    rcases he.lt_or_gt with h | h
    · exact ⟨e, h⟩
    · exact ⟨-e, by rw [form_neg_right]; linarith⟩
  set W : ℝ → E n := fun u =>
    (u * (b - u)) • (e - (2 * form (g (σ u)) (deriv σ u) e) • N u) with hWdef
  have hWs : ContDiffOn ℝ ∞ W (Ioo α β) :=
    (contDiffOn_id.mul (contDiffOn_const.sub contDiffOn_id)).smul (contDiffOn_const.sub
      ((contDiffOn_const.mul ((contDiff_form hg).comp_contDiffOn
        (hσs.prodMk (hσ's.prodMk contDiffOn_const)))).smul hN))
  have hW's : ContDiffOn ℝ ∞ (deriv W) (Ioo α β) := hderivs hWs
  have hWorth : ∀ u ∈ Ioo α β, form (g (σ u)) (deriv σ u) (W u) = 0 := fun u hu => by
    simp only [W, form_smul_right, form_sub_right, hNσ u hu]
    ring
  have hW0 : W 0 = 0 := by simp [W]
  have hWb : W b = 0 := by simp [W]
  have hDLW : ∀ u ∈ Ioo α β, fderiv ℝ (lagrangian g) (σ u, deriv σ u) (0, W u) = 0 :=
    fun u hu => by rw [fderiv_lagrangian_inr hg, hWorth u hu, mul_zero]
  set A := 2 * fderiv ℝ (fderiv ℝ (lagrangian g)) (σ r, deriv σ r) (0, j) (0, W r) with hAdef
  have hA : A < 0 := by
    have e1 : form (g (σ r)) j (W r) =
        (r * (b - r)) * form (g (σ r)) (j - c₀ • deriv σ r) e := by
      simp only [W, c₀, form_smul_right, form_sub_right, form_sub_left, form_smul_left]
      ring
    have hrb : 0 < r * (b - r) := mul_pos hr.1 (by linarith [hr.2])
    rw [hAdef, fderiv_fderiv_lagrangian_inr hg, e1]
    nlinarith
  set q : ℝ → ℝ := fun u => fderiv ℝ (fderiv ℝ (lagrangian g)) (σ u, deriv σ u)
    (W u, deriv W u) (W u, deriv W u) with hqdef
  have hqc : ContinuousOn q (Icc 0 b) :=
    ((((hD2L.continuous.comp_continuousOn (hσs.continuousOn.prodMk hσ's.continuousOn)).clm_apply
      (hWs.continuousOn.prodMk hW's.continuousOn)).clm_apply
      (hWs.continuousOn.prodMk hW's.continuousOn))).mono hbU
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hqc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, hb.le⟩)
  set ε := -A / (2 * b * (M + 1)) with hεdef
  have hε : 0 < ε := div_pos (by linarith) (by positivity)
  set κ' := -(ε * A) / b with hκ'def
  have hκ'b : κ' * b = -(ε * A) := by rw [hκ'def]; field_simp
  have hkey : ∀ u ∈ Icc 0 b, ε ^ 2 * q u - κ' < 0 := by
    intro u hu
    have h1 : ε ^ 2 * q u ≤ ε ^ 2 * M :=
      mul_le_mul_of_nonneg_left ((le_abs_self _).trans (by simpa using hM u hu)) (sq_nonneg ε)
    have h2 : ε * (M + 1) = -A / (2 * b) := by rw [hεdef]; field_simp
    have h3 : -A / (2 * b) < -A / b := by
      rw [div_lt_div_iff₀ (by positivity) hb]
      nlinarith
    have h4 : ε ^ 2 * M < κ' := by
      calc ε ^ 2 * M ≤ ε ^ 2 * (M + 1) := by nlinarith
        _ = ε * (-A / (2 * b)) := by rw [← h2]; ring
        _ < ε * (-A / b) := mul_lt_mul_of_pos_left h3 hε
        _ = κ' := by rw [hκ'def]; ring
    linarith
  have hJd : ∀ u ∈ Ioo α β, HasDerivAt J (deriv J u) u := hd hJs
  have hWd : ∀ u ∈ Ioo α β, HasDerivAt W (deriv W u) u := hd hWs
  set X₁ : ℝ → E n := fun u => J u + (2 * ε) • W u with hX₁def
  have hX₁s : ContDiffOn ℝ ∞ X₁ (Ioo α β) := hJs.add (hWs.const_smul _)
  have hX₁d : ∀ u ∈ Ioo α β, deriv X₁ u = deriv J u + (2 * ε) • deriv W u := fun u hu => by
    have h : HasDerivAt X₁ (deriv J u + (2 * ε) • deriv W u) u :=
      (hJd u hu).add ((hWd u hu).const_smul (2 * ε))
    exact h.deriv
  set Ψ : ℝ → ℝ := fun u => fderiv ℝ (fderiv ℝ (lagrangian g)) (σ u, deriv σ u)
    (J u, deriv J u) (0, X₁ u) with hΨdef
  have hΨs : ContDiffOn ℝ ∞ Ψ (Ioo α β) :=
    ((hD2L.comp_contDiffOn (hσs.prodMk hσ's)).clm_apply (hJs.prodMk hJ's)).clm_apply
      (contDiffOn_const.prodMk hX₁s)
  set V₁ : ℝ → E n := fun u => J u + ε • W u with hV₁def
  set Z₁ : ℝ → E n := fun u => (-(Ψ u + κ' * u) / 2) • N u with hZ₁def
  set V₂ : ℝ → E n := fun u => ε • W u with hV₂def
  set Z₂ : ℝ → E n := fun u => (-(ε * A + κ' * u) / 2) • N u with hZ₂def
  have hV₁s : ContDiffOn ℝ ∞ V₁ (Ioo α β) := hJs.add (hWs.const_smul _)
  have hV₂s : ContDiffOn ℝ ∞ V₂ (Ioo α β) := hWs.const_smul _
  have hZ₁s : ContDiffOn ℝ ∞ Z₁ (Ioo α β) :=
    ((hΨs.add (contDiffOn_const.mul contDiffOn_id)).neg.div_const _).smul hN
  have hZ₂s : ContDiffOn ℝ ∞ Z₂ (Ioo α β) :=
    ((contDiffOn_const.add (contDiffOn_const.mul contDiffOn_id)).neg.div_const _).smul hN
  have hNZ : ∀ (φ : ℝ → ℝ) u, u ∈ Ioo α β →
      fderiv ℝ (lagrangian g) (σ u, deriv σ u) (0, φ u • N u) = φ u := fun φ u hu => by
    rw [fderiv_lagrangian_inr hg, form_smul_right, hNσ u hu]
    ring
  have hZ₁d : ∀ u ∈ Ioo α β, fderiv ℝ (lagrangian g) (σ u, deriv σ u) (Z₁ u, deriv Z₁ u) =
      -(fderiv ℝ (fderiv ℝ (lagrangian g)) (σ u, deriv σ u) (J u, deriv J u)
        (X₁ u, deriv X₁ u) + κ') / 2 := fun u hu => by
    rw [hEL hZ₁s (f := fun u => -(Ψ u + κ' * u) / 2)
      (fun u hu => hNZ (fun u => -(Ψ u + κ' * u) / 2) u hu) u hu]
    have h := (((hJac hX₁s u hu).add ((hasDerivAt_id u).const_mul κ')).neg.div_const 2)
    simp only [id, mul_one] at h
    exact h.deriv
  have hZ₂d : ∀ u ∈ Ioo α β, fderiv ℝ (lagrangian g) (σ u, deriv σ u) (Z₂ u, deriv Z₂ u) =
      -κ' / 2 := fun u hu => by
    rw [hEL hZ₂s (f := fun u => -(ε * A + κ' * u) / 2)
      (fun u hu => hNZ (fun u => -(ε * A + κ' * u) / 2) u hu) u hu]
    have h := (((hasDerivAt_id u).const_mul κ').const_add (ε * A)).neg.div_const 2
    simp only [id, mul_one] at h
    exact h.deriv
  have hV₁0 : ∀ u ∈ Ioo α β, fderiv ℝ (lagrangian g) (σ u, deriv σ u) (0, V₁ u) = 0 :=
    fun u hu => by rw [hV₁def, hsplit, map_add, map_smul, hJorth u hu, hDLW u hu]; simp
  have hV₂0 : ∀ u ∈ Ioo α β, fderiv ℝ (lagrangian g) (σ u, deriv σ u) (0, V₂ u) = 0 :=
    fun u hu => by
      rw [hV₂def, show ((0 : E n), ε • W u) = ε • ((0 : E n), W u) by ext <;> simp, map_smul,
        hDLW u hu, smul_zero]
  have hfutI : ∀ u ∈ Icc 0 b, IsFutureCausal g Y (σ u) (deriv σ u) := fun u hu =>
    hσ.isFutureCausal hg hbI ordConnected_Icc ⟨le_rfl, hb.le⟩ hfut hu
  have hnullI : ∀ u ∈ Icc 0 b, form (g (σ u)) (deriv σ u) (deriv σ u) = 0 := fun u hu =>
    (hσ.form_deriv_eq hg hbI ordConnected_Icc hu ⟨le_rfl, hb.le⟩).trans hnull
  have hI1 : Icc 0 r ⊆ Icc 0 b := Icc_subset_Icc le_rfl hr.2.le
  have hI2 : Icc r b ⊆ Icc 0 b := Icc_subset_Icc hr.1.le le_rfl
  have hp1 := eventually_isPathOn_variation hg isOpen_Ioo hr.1 (hI1.trans hbU) hσs hV₁s hZ₁s
    (fun u hu => hfutI u (hI1 hu)) (fun u hu => hnullI u (hI1 hu))
    (fun u hu => by
      have := hEL hV₁s (f := fun _ => 0) (fun u hu => hV₁0 u hu) u (hbU (hI1 hu))
      rwa [deriv_const] at this)
    (fun u hu => by
      have hu' := hbU (hI1 hu)
      have hV₁d : deriv V₁ u = deriv J u + ε • deriv W u := by
        have h : HasDerivAt V₁ (deriv J u + ε • deriv W u) u :=
          (hJd u hu').add ((hWd u hu').const_smul ε)
        exact h.deriv
      rw [hZ₁d u hu', hV₁d, hX₁d u hu']
      have e1 : (V₁ u, deriv J u + ε • deriv W u) =
          (J u, deriv J u) + ε • (W u, deriv W u) := by ext <;> simp [V₁]
      have e2 : (X₁ u, deriv J u + (2 * ε) • deriv W u) =
          (J u, deriv J u) + (2 * ε) • (W u, deriv W u) := by ext <;> simp [X₁]
      rw [e1, e2]
      simp only [map_add, map_smul, add_apply,
        smul_apply, smul_eq_mul]
      rw [hsym _ (W u, deriv W u) (J u, deriv J u)]
      have := hkey u (hI1 hu)
      simp only [q] at this
      linarith)
  have hp2 := eventually_isPathOn_variation hg isOpen_Ioo hr.2 (hI2.trans hbU) hσs hV₂s hZ₂s
    (fun u hu => hfutI u (hI2 hu)) (fun u hu => hnullI u (hI2 hu))
    (fun u hu => by
      have := hEL hV₂s (f := fun _ => 0) (fun u hu => hV₂0 u hu) u (hbU (hI2 hu))
      rwa [deriv_const] at this)
    (fun u hu => by
      have hu' := hbU (hI2 hu)
      have hV₂d : deriv V₂ u = ε • deriv W u := by
        have h : HasDerivAt V₂ (ε • deriv W u) u := (hWd u hu').const_smul ε
        exact h.deriv
      rw [hZ₂d u hu', hV₂d]
      have e1 : (V₂ u, ε • deriv W u) = ε • (W u, deriv W u) := by ext <;> simp [V₂]
      rw [e1]
      simp only [map_smul, smul_apply, smul_eq_mul]
      have := hkey u (hI2 hu)
      simp only [q] at this
      nlinarith)
  obtain ⟨s, hs1, hs2⟩ := (hp1.and hp2).exists
  have c1 := chronLT_of_isPathOn hs1
  have c2 := chronLT_of_isPathOn hs2
  have hΨ0 : Ψ 0 = 0 := by
    simp only [Ψ, X₁, hJ0, hW0, smul_zero, add_zero, Prod.mk_zero_zero, map_zero]
  have hΨr : Ψ r = ε * A := by
    simp only [Ψ, X₁, hJr, zero_add]
    rw [show ((0 : E n), (2 * ε) • W r) = (2 * ε) • ((0 : E n), W r) by ext <;> simp, map_smul,
      smul_eq_mul, hAdef]
    ring
  have hx0 : σ 0 + s • V₁ 0 + s ^ 2 • Z₁ 0 = σ 0 := by
    simp [V₁, Z₁, hJ0, hW0, hΨ0]
  have hxr : σ r + s • V₁ r + s ^ 2 • Z₁ r = σ r + s • V₂ r + s ^ 2 • Z₂ r := by
    simp only [V₁, V₂, Z₁, Z₂, hJr, hΨr, zero_add]
  have hxb : σ b + s • V₂ b + s ^ 2 • Z₂ b = σ b := by
    have : -(ε * A + κ' * b) / 2 = 0 := by rw [hκ'b]; ring
    simp only [V₂, Z₂, hWb, this, smul_zero, zero_smul, add_zero]
  rw [hx0, hxr] at c1
  rw [hxb] at c2
  exact c1.trans c2

end Facts

end

end LorentzianCalderon
