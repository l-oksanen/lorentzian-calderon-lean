module

public import LorentzianCalderon.Geometry.WorldFunction
public import LorentzianCalderon.Geometry.Gauss

public section

/-!
# Derivatives of the local world function

Blueprint, Lemma `lem_world_function` (c): for the world function `Q(y, p) = g_y(w, w)`,
`(y, w) = 𝐞⁻¹(y, p)`, of an exponential chart, `d_p Q = 2 g_p(ċ(1), ·)` and
`d_y Q = -2 g_y(ċ(0), ·)`, where `c(r) = exp_y (r w)`.
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Set Filter

variable {n : ℕ} {g : MatrixField n} {Y : E n → E n}

/-- The geodesic `c(r) = exp_y (r w)` traversed backwards: it starts at `exp_y w` with velocity
`-ċ(1)`, ends at `y` with velocity `-ċ(0) = -w`, and `g(ċ(1), ċ(1)) = g(ċ(0), ċ(0))`. -/
theorem InExpDomain.reverse (hg : IsSpacetime g Y) {y w : E n} (h : InExpDomain g y w) :
    InExpDomain g (expMap g y w) (-fderiv ℝ (expMap g y) w w) ∧
      expMap g (expMap g y w) (-fderiv ℝ (expMap g y) w w) = y ∧
      fderiv ℝ (expMap g (expMap g y w)) (-fderiv ℝ (expMap g y) w w)
        (-fderiv ℝ (expMap g y) w w) = -w ∧
      form (g (expMap g y w)) (fderiv ℝ (expMap g y) w w) (fderiv ℝ (expMap g y) w w) =
        form (g y) w w := by
  obtain ⟨ε, hε, hc, -, h0, h0'⟩ := h.isGeodesic_expMap_smul hg
  set c := fun t : ℝ => expMap g y (t • w)
  have hc1 : deriv c 1 = fderiv ℝ (expMap g y) w w := (hasDerivAt_expMap_smul_one hg h).deriv
  have hc1' : c 1 = expMap g y w := by simp [c]
  have hr := hc.comp_affine (-1) 1
  have hmem : ∀ t ∈ Ioo (-ε) (1 + ε), t ∈ (fun s => -1 * s + 1) ⁻¹' Ioo (-ε) (1 + ε) :=
    fun t ht => ⟨by simp; linarith [ht.2], by simp; linarith [ht.1]⟩
  have hsub : ∀ t ∈ Ioo (-ε) (1 + ε),
      uIcc 0 t ⊆ (fun s => -1 * s + 1) ⁻¹' Ioo (-ε) (1 + ε) := fun t ht =>
    ((ordConnected_Ioo.uIcc_subset ⟨by linarith, by linarith⟩ ht)).trans fun s hs => hmem s hs
  have hd : ∀ t ∈ Ioo (-ε) (1 + ε),
      deriv (fun s => c (-1 * s + 1)) t = -deriv c (-1 * t + 1) := fun t ht => by
    rw [hc.deriv_comp_affine (hmem t ht), neg_one_smul]
  have hd0 : deriv (fun s => c (-1 * s + 1)) 0 = -fderiv ℝ (expMap g y) w w := by
    rw [hd 0 ⟨by linarith, by linarith⟩]
    simp [hc1]
  have h11 : (1 : ℝ) ∈ Ioo (-ε) (1 + ε) := ⟨by linarith, by linarith⟩
  have hst := hr.expMap_smul_eq hg (hsub 1 h11)
  simp only [one_smul, hd0, mul_zero, zero_add, mul_one, neg_add_cancel, hc1'] at hst
  refine ⟨hst.1, ?_, ?_, ?_⟩
  · rw [hst.2]
    simpa [c] using h0
  · have hev : (fun t : ℝ => expMap g (expMap g y w) (t • -fderiv ℝ (expMap g y) w w)) =ᶠ[𝓝 1]
        fun s => c (-1 * s + 1) := by
      filter_upwards [isOpen_Ioo.mem_nhds h11] with t ht
      have := (hr.expMap_smul_eq hg (hsub t ht))
      simp only [mul_zero, zero_add, hc1', hd0] at this
      exact this.2
    have hD := (hasDerivAt_expMap_smul_one hg hst.1).deriv
    rw [← hD, hev.deriv_eq, hd 1 h11]
    simp [h0']
  · have := hc.form_deriv_eq hg (J := Icc 0 1) (fun t ht => ⟨by linarith [ht.1], by
      linarith [ht.2]⟩) ordConnected_Icc (left_mem_Icc.2 zero_le_one)
      (right_mem_Icc.2 zero_le_one)
    have hc0 : c 0 = y := by simpa [c] using h0
    rw [hc1, hc1', h0', hc0] at this
    exact this.symm

/-! ### The world function of an exponential chart -/

/-- The world function `Q(y, p) = g_y(w, w)`, `w = W(y, p)`. -/
def worldFn (g : MatrixField n) (W : E n × E n → E n) (q : E n × E n) : ℝ :=
  form (g q.1) (W q) (W q)

theorem worldFn_def (g : MatrixField n) (W : E n × E n → E n) (q : E n × E n) :
    worldFn g W q =
      form (g q.1) (W q) (W q) := by rfl

/-- The velocity `-ċ(1)` at `p` of the reversed geodesic from `p` to `y`, `c(r) = exp_y (r w)`,
`w = W(y, p)`. -/
def revVel (g : MatrixField n) (W : E n × E n → E n) (q : E n × E n) : E n :=
  -fderiv ℝ (expMap g q.1) (W q) (W q)

variable {U U' : Set (E n × E n)} {W : E n × E n → E n}

theorem IsExpChart.contDiffOn_worldFn (hg : IsSpacetime g Y) (hc : IsExpChart g U U' W) :
    ContDiffOn ℝ ∞ (worldFn g W) U' :=
  (contDiff_form hg).comp_contDiffOn (contDiffOn_fst.prodMk (hc.smooth.prodMk hc.smooth))

theorem IsExpChart.contDiffOn_revVel (hg : IsSpacetime g Y) (hc : IsExpChart g U U' W) :
    ContDiffOn ℝ ∞ (revVel g W) U' := by
  have hL : ContDiffOn ℝ ∞ (fderiv ℝ (fun p : E n × E n => expMap g p.1 p.2))
      { p | InExpDomain g p.1 p.2 } :=
    (contDiffOn_expMap hg).fderiv_of_isOpen (isOpen_expDomain hg) (by simp)
  have hP : ContDiffOn ℝ ∞ (fun q : E n × E n => (q.1, W q)) U' := contDiffOn_fst.prodMk hc.smooth
  have h1 := hL.comp hP fun q hq => hc.inExpDomain _ (hc.inv_mem q hq)
  have h2 : ContDiffOn ℝ ∞ (fun q : E n × E n => ((0 : E n), W q)) U' :=
    contDiffOn_const.prodMk hc.smooth
  refine (h1.clm_apply h2).neg.congr fun q hq => ?_
  simp only [revVel, Function.comp_apply]
  rw [(hasFDerivAt_expMap hg (p := (q.1, W q)) (hc.inExpDomain _ (hc.inv_mem q hq))).fderiv]
  rfl

/-- `Q(y, p) = g_p(ċ(1), ċ(1))`. -/
theorem IsExpChart.worldFn_eq (hg : IsSpacetime g Y) (hc : IsExpChart g U U' W) {q : E n × E n}
    (hq : q ∈ U') :
    worldFn g W q = form (g q.2) (fderiv ℝ (expMap g q.1) (W q) (W q))
      (fderiv ℝ (expMap g q.1) (W q) (W q)) := by
  have := (hc.inExpDomain _ (hc.inv_mem q hq)).reverse hg
  rw [hc.expMap_inv q hq] at this
  exact this.2.2.2.symm

/-- The reversed geodesic: `exp_p (w̃) = y`, `g_p(w̃, w̃) = Q(y, p)`, `d(exp_p)_{w̃} w̃ = -w`, for
`w̃ = -ċ(1)`. -/
theorem IsExpChart.revVel_spec (hg : IsSpacetime g Y) (hc : IsExpChart g U U' W)
    {q : E n × E n} (hq : q ∈ U') :
    InExpDomain g q.2 (revVel g W q) ∧ expMap g q.2 (revVel g W q) = q.1 ∧
      fderiv ℝ (expMap g q.2) (revVel g W q) (revVel g W q) = -W q ∧
      form (g q.2) (revVel g W q) (revVel g W q) = worldFn g W q := by
  have h := (hc.inExpDomain _ (hc.inv_mem q hq)).reverse hg
  rw [hc.expMap_inv q hq] at h
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  rw [revVel, form_neg_left, form_neg_right, neg_neg, h.2.2.2]
  rfl

theorem IsExpChart.differentiableAt_worldFn (hg : IsSpacetime g Y) (hc : IsExpChart g U U' W)
    {q : E n × E n} (hq : q ∈ U') : DifferentiableAt ℝ (worldFn g W) q :=
  ((hc.contDiffOn_worldFn hg).differentiableOn (by simp)).differentiableAt
    (hc.isOpen'.mem_nhds hq)

/-- Blueprint, Lemma `lem_world_function` (c), first formula: `d_p Q = 2 g_p(ċ(1), ·)`. -/
theorem IsExpChart.fderiv_worldFn_snd (hg : IsSpacetime g Y) (hc : IsExpChart g U U' W)
    {q : E n × E n} (hq : q ∈ U') :
    DifferentiableAt ℝ (fun x => worldFn g W (q.1, x)) q.2 ∧
      ∀ η, fderiv ℝ (fun x => worldFn g W (q.1, x)) q.2 η =
        2 * form (g q.2) (fderiv ℝ (expMap g q.1) (W q) (W q)) η := by
  obtain ⟨y, p⟩ := q
  dsimp only
  have hdiff : DifferentiableAt ℝ (fun x => worldFn g W (y, x)) p :=
    (hc.differentiableAt_worldFn hg hq).comp p (differentiableAt_const y |>.prodMk
      differentiableAt_id)
  refine ⟨hdiff, ?_⟩
  set w := W (y, p)
  have hyw : (y, w) ∈ U := hc.inv_mem _ hq
  have hdom : InExpDomain g y w := hc.inExpDomain _ hyw
  have hexp : expMap g y w = p := hc.expMap_inv _ hq
  have hdexp : DifferentiableAt ℝ (expMap g y) w :=
    (hasFDerivAt_expMap hg (p := (y, w)) hdom).differentiableAt
  have key : ∀ ξ, fderiv ℝ (fun x => worldFn g W (y, x)) p (fderiv ℝ (expMap g y) w ξ) =
      2 * form (g y) w ξ := by
    intro ξ
    have hA := hasDerivAt_line hdexp ξ
    have hF : HasFDerivAt (fun x => worldFn g W (y, x))
        (fderiv ℝ (fun x => worldFn g W (y, x)) p) (expMap g y (w + (0 : ℝ) • ξ)) := by
      rw [zero_smul, add_zero, hexp]
      exact hdiff.hasFDerivAt
    have hcomp := hF.comp_hasDerivAt (0 : ℝ) hA
    have hl : HasDerivAt (fun s : ℝ => w + s • ξ) ξ 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const ξ).const_add w
    have hform := hasDerivAt_form_self (hg.lorentzian y).symm hl
    have hcurve : Tendsto (fun s : ℝ => (y, w + s • ξ)) (𝓝 0) (𝓝 (y, w)) := by
      have : Continuous fun s : ℝ => (y, w + s • ξ) := by fun_prop
      simpa using this.tendsto 0
    have hev : (fun s : ℝ => form (g y) (w + s • ξ) (w + s • ξ)) =ᶠ[𝓝 0]
        (fun x => worldFn g W (y, x)) ∘ fun s : ℝ => expMap g y (w + s • ξ) := by
      filter_upwards [hcurve.eventually (hc.isOpen.mem_nhds hyw)] with s hs
      show _ = form (g y) (W (y, expMap g y (w + s • ξ))) (W (y, expMap g y (w + s • ξ)))
      rw [← expPair_mk, hc.inv_expPair _ hs]
    have := (hform.congr_of_eventuallyEq hev.symm).unique hcomp
    rw [← this, zero_smul, add_zero]
  intro η
  obtain ⟨ξ, rfl⟩ := (hc.bijective _ hyw).2 η
  rw [key, ← Facts.gauss hg hdom ξ, hexp]

/-- Blueprint, Lemma `lem_world_function` (c), second formula: `d_y Q = -2 g_y(ċ(0), ·)`. -/
theorem IsExpChart.fderiv_worldFn_fst (hg : IsSpacetime g Y) (hc : IsExpChart g U U' W)
    {q : E n × E n} (hq : q ∈ U') :
    DifferentiableAt ℝ (fun x => worldFn g W (x, q.2)) q.1 ∧
      ∀ X, fderiv ℝ (fun x => worldFn g W (x, q.2)) q.1 X = -2 * form (g q.1) (W q) X := by
  obtain ⟨y, p⟩ := q
  dsimp only
  have hdiff : DifferentiableAt ℝ (fun x => worldFn g W (x, p)) y :=
    DifferentiableAt.comp (g := worldFn g W) (f := fun x : E n => (x, p)) y
      (hc.differentiableAt_worldFn hg hq) (differentiableAt_id.prodMk (differentiableAt_const p))
  refine ⟨hdiff, fun X => ?_⟩
  have hcurve : Tendsto (fun s : ℝ => (y + s • X, p)) (𝓝 0) (𝓝 (y, p)) := by
    have : Continuous fun s : ℝ => (y + s • X, p) := by fun_prop
    simpa using this.tendsto 0
  have hev := hcurve.eventually (hc.isOpen'.mem_nhds hq)
  set u : ℝ → E n := fun s => revVel g W (y + s • X, p)
  have hu0 : u 0 = revVel g W (y, p) := by simp [u]
  have hrv : DifferentiableAt ℝ (revVel g W) (y, p) :=
    ((hc.contDiffOn_revVel hg).differentiableOn (by simp)).differentiableAt
      (hc.isOpen'.mem_nhds hq)
  have hud : DifferentiableAt ℝ u 0 := by
    have hl : DifferentiableAt ℝ (fun s : ℝ => (y + s • X, p)) 0 := by fun_prop
    have hrv' : DifferentiableAt ℝ (revVel g W) (y + (0 : ℝ) • X, p) := by simpa using hrv
    exact DifferentiableAt.comp (g := revVel g W) (f := fun s : ℝ => (y + s • X, p)) 0 hrv' hl
  have hu := hud.hasDerivAt
  set u' := deriv u 0
  obtain ⟨hdom, hexp, hvel, -⟩ := hc.revVel_spec hg hq
  dsimp only at hdom hexp hvel
  have hX : fderiv ℝ (expMap g p) (revVel g W (y, p)) u' = X := by
    have hE : HasFDerivAt (expMap g p) (fderiv ℝ (expMap g p) (revVel g W (y, p))) (u 0) := by
      rw [hu0]
      exact (hasFDerivAt_expMap hg (p := (p, revVel g W (y, p))) hdom).differentiableAt
        |>.hasFDerivAt
    have hcomp := hE.comp_hasDerivAt (0 : ℝ) hu
    have hl : HasDerivAt (fun s : ℝ => y + s • X) X 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const X).const_add y
    have hev' : (fun s : ℝ => y + s • X) =ᶠ[𝓝 0] expMap g p ∘ u := by
      filter_upwards [hev] with s hs
      exact ((hc.revVel_spec hg hs).2.1).symm
    exact ((hl.congr_of_eventuallyEq hev'.symm).unique hcomp).symm
  have hQ : fderiv ℝ (fun x => worldFn g W (x, p)) y X =
      2 * form (g p) (revVel g W (y, p)) u' := by
    have hform := hasDerivAt_form_self (hg.lorentzian p).symm hu
    rw [hu0] at hform
    have hev' : (fun s : ℝ => form (g p) (u s) (u s)) =ᶠ[𝓝 0]
        fun s : ℝ => worldFn g W (y + s • X, p) := by
      filter_upwards [hev] with s hs
      exact (hc.revVel_spec hg hs).2.2.2
    exact (hasDerivAt_line hdiff X).unique (hform.congr_of_eventuallyEq hev'.symm)
  have hgauss := Facts.gauss hg hdom u'
  rw [hexp, hvel, hX, form_neg_left] at hgauss
  rw [hQ, ← hgauss]
  ring

end

end LorentzianCalderon
