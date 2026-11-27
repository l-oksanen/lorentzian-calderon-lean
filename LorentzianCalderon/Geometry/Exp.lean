module

public import LorentzianCalderon.Causal.Chron
public import LorentzianCalderon.Setting.BoxGreen
public import LorentzianCalderon.Facts.Vocabulary
public import LorentzianCalderon.ODE.Dependence
public import LorentzianCalderon.Waves.Flow

public section

/-!
# Geodesics and the exponential map

The geodesic equation as the first-order system `ż = S(z)` for `z = (γ, γ̇)`, with the smooth
geodesic spray `S(x, v) = (v, -Γ(x)(v, v))`. From smooth dependence on initial data
(`Facts.ode_smooth_dependence`) we derive:

* uniqueness of geodesics with given initial data (`IsGeodesic.eqOn`);
* the domain of the exponential map is open (`isOpen_expDomain`), and `exp` is smooth on it
  (`contDiffOn_expMap`);
* `exp_y (t w) = γ(t)` for the geodesic `γ` with `γ(0) = y`, `γ̇(0) = w`
  (`IsGeodesic.expMap_smul_eq`);
* `g(γ̇, γ̇)` is constant along a geodesic (`IsGeodesic.form_deriv_eq`), and a geodesic that is
  future-directed causal (timelike) at one time is so at all times
  (`IsGeodesic.isFutureCausal`, `IsGeodesic.isFutureTimelike`).
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Set Filter

variable {n : ℕ} {g : MatrixField n} {Y : E n → E n}

/-- The quadratic term `Γ(x)(v, v)ᵏ = Γᵏᵢⱼ vⁱ vʲ` of the geodesic equation. -/
def christoffelQuad (g : MatrixField n) (x v : E n) : E n :=
  WithLp.toLp 2 fun k => ∑ i, ∑ j, christoffel g x k i j * v i * v j

/-- The geodesic spray `(x, v) ↦ (v, -Γ(x)(v, v))`. -/
def geodesicSpray (g : MatrixField n) (z : E n × E n) : E n × E n :=
  (z.2, -christoffelQuad g z.1 z.2)

theorem geodesicSpray_def (g : MatrixField n) (z : E n × E n) :
    geodesicSpray g z =
      (z.2, -christoffelQuad g z.1 z.2) := by rfl

lemma christoffelQuad_apply (x v : E n) (k : Fin (n + 1)) :
    christoffelQuad g x v k = ∑ i, ∑ j, christoffel g x k i j * v i * v j :=
  by rfl

theorem contDiff_christoffel (hg : IsSpacetime g Y) (k i j : Fin (n + 1)) :
    ContDiff ℝ ∞ fun x => christoffel g x k i j := by
  simp only [christoffel_def]
  refine contDiff_const.mul (ContDiff.sum fun l _ => ?_)
  exact (contDiff_inv_apply hg.smooth hg.det_ne_zero k l).mul
    (((contDiff_d (hg.smooth j l) i).add (contDiff_d (hg.smooth i l) j)).sub
      (contDiff_d (hg.smooth i j) l))

theorem contDiff_geodesicSpray (hg : IsSpacetime g Y) : ContDiff ℝ ∞ (geodesicSpray g) := by
  refine contDiff_snd.prodMk (ContDiff.neg ?_)
  refine (contDiff_piLp 2).2 fun k => ?_
  simp only [christoffelQuad, PiLp.toLp_apply]
  refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
  have hc : ∀ i, ContDiff ℝ ∞ fun z : E n × E n => z.2 i := fun i => by fun_prop
  exact (((contDiff_christoffel hg k i j).comp contDiff_fst).mul (hc i)).mul (hc j)

/-! ### The geodesic equation as a first-order system -/

/-- The geodesic spray as a time-dependent vector field with a (dummy) parameter. -/
abbrev sprayField (g : MatrixField n) : ℝ → E n × E n → ℝ → E n × E n :=
  fun _ z _ => geodesicSpray g z

/-- The set of `(t, t₀, z₀, p)` for which the solution of `ż = S(z)` with `z(t₀) = z₀` reaches
the time `t`. -/
def sprayDomain (g : MatrixField n) : Set (ℝ × ℝ × (E n × E n) × ℝ) :=
  { q | q.2.2.2 ∈ (univ : Set ℝ) ∧ ∃ (x : ℝ → E n × E n) (I : Set ℝ),
    Facts.IsODESolution (sprayField g) univ q.2.2.2 x I ∧ q.1 ∈ I ∧ q.2.1 ∈ I ∧
      x q.2.1 = q.2.2.1 }

theorem exists_sprayFlow (hg : IsSpacetime g Y) :
    ∃ X : ℝ × ℝ × (E n × E n) × ℝ → E n × E n,
      IsOpen (sprayDomain g) ∧ ContDiffOn ℝ ∞ X (sprayDomain g) ∧
      ∀ (p : ℝ) (x : ℝ → E n × E n) (I : Set ℝ),
        Facts.IsODESolution (sprayField g) univ p x I →
        ∀ t₀ ∈ I, ∀ t ∈ I, X (t, t₀, x t₀, p) = x t := by
  obtain ⟨X, hS, hX, hrep⟩ :=
    Facts.ode_smooth_dependence (P := ℝ) isOpen_univ (contDiff_geodesicSpray hg).contDiffOn
  refine ⟨X, ?_, ?_, hrep⟩
  · convert hS using 1
    ext q
    simp [sprayDomain]
  · convert hX using 1
    ext q
    simp [sprayDomain]

lemma mem_sprayDomain {x : ℝ → E n × E n} {I : Set ℝ} {p : ℝ}
    (hx : Facts.IsODESolution (sprayField g) univ p x I) {t t₀ : ℝ} (ht : t ∈ I)
    (ht₀ : t₀ ∈ I) : (t, t₀, x t₀, p) ∈ sprayDomain g :=
  ⟨mem_univ _, x, I, hx, ht, ht₀, rfl⟩

/-! ### Geodesics -/

section Geodesic

variable {γ γ₁ γ₂ : ℝ → E n} {I I₁ I₂ J : Set ℝ} {t : ℝ}

theorem IsGeodesic.hasDerivAt (hγ : IsGeodesic g γ I) (ht : t ∈ I) :
    HasDerivAt γ (deriv γ t) t :=
  ((hγ.smooth.differentiableOn (by simp)).differentiableAt
    (hγ.isOpen.mem_nhds ht)).hasDerivAt

theorem IsGeodesic.contDiffOn_deriv (hγ : IsGeodesic g γ I) : ContDiffOn ℝ ∞ (deriv γ) I :=
  hγ.smooth.deriv_of_isOpen hγ.isOpen (by simp)

theorem IsGeodesic.hasDerivAt_deriv (hγ : IsGeodesic g γ I) (ht : t ∈ I) :
    HasDerivAt (deriv γ) (deriv (deriv γ) t) t :=
  ((hγ.contDiffOn_deriv.differentiableOn (by simp)).differentiableAt
    (hγ.isOpen.mem_nhds ht)).hasDerivAt

theorem IsGeodesic.deriv_deriv (hγ : IsGeodesic g γ I) (ht : t ∈ I) :
    deriv (deriv γ) t = -christoffelQuad g (γ t) (deriv γ t) := by
  ext k
  have := hγ.equation t ht k
  simp only [PiLp.neg_apply, christoffelQuad_apply]
  linarith

theorem IsGeodesic.hasDerivAt_spray (hγ : IsGeodesic g γ I) (ht : t ∈ I) :
    HasDerivAt (fun s => (γ s, deriv γ s)) (geodesicSpray g (γ t, deriv γ t)) t := by
  have := (hγ.hasDerivAt ht).prodMk (hγ.hasDerivAt_deriv ht)
  rwa [hγ.deriv_deriv ht] at this

theorem IsGeodesic.isODESolution (hγ : IsGeodesic g γ I) (hJ : J ⊆ I) (hJc : J.OrdConnected)
    (p : ℝ) : Facts.IsODESolution (sprayField g) univ p (fun s => (γ s, deriv γ s)) J where
  interval := hJc
  mem _ _ := mem_univ _
  deriv _ ht := (hγ.hasDerivAt_spray (hJ ht)).hasDerivWithinAt

/-- Uniqueness of geodesics: geodesics with the same position and velocity at some time agree on
every interval containing that time on which both are defined. -/
theorem IsGeodesic.eqOn (hg : IsSpacetime g Y) (h₁ : IsGeodesic g γ₁ I₁) (h₂ : IsGeodesic g γ₂ I₂)
    (hJ₁ : J ⊆ I₁) (hJ₂ : J ⊆ I₂) (hJ : J.OrdConnected) {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    (h0 : γ₁ t₀ = γ₂ t₀) (h0' : deriv γ₁ t₀ = deriv γ₂ t₀) :
    EqOn γ₁ γ₂ J ∧ EqOn (deriv γ₁) (deriv γ₂) J := by
  obtain ⟨X, -, -, hrep⟩ := exists_sprayFlow hg
  have key : ∀ t ∈ J, (γ₁ t, deriv γ₁ t) = (γ₂ t, deriv γ₂ t) := fun t ht => by
    have e₁ := hrep 0 _ J (h₁.isODESolution hJ₁ hJ 0) t₀ ht₀ t ht
    have e₂ := hrep 0 _ J (h₂.isODESolution hJ₂ hJ 0) t₀ ht₀ t ht
    simp only [h0, h0'] at e₁ e₂
    exact e₁.symm.trans e₂
  exact ⟨fun t ht => (Prod.ext_iff.1 (key t ht)).1, fun t ht => (Prod.ext_iff.1 (key t ht)).2⟩

/-- A geodesic from solutions of the spray equation reaching the times `a < 0 < b`. -/
theorem exists_isGeodesic_of_mem_sprayDomain (hg : IsSpacetime g Y) {a b : ℝ} (ha : a < 0)
    (hb : 0 < b) {z : E n × E n} (hza : (a, 0, z, 0) ∈ sprayDomain g)
    (hzb : (b, 0, z, 0) ∈ sprayDomain g) :
    ∃ γ : ℝ → E n, IsGeodesic g γ (Ioo a b) ∧ γ 0 = z.1 ∧ deriv γ 0 = z.2 := by
  obtain ⟨X, -, hX, hrep⟩ := exists_sprayFlow hg
  set h : ℝ → E n × E n := fun t => X (t, 0, z, 0) with hh
  have side : ∀ c, c ≠ 0 → (c, 0, z, 0) ∈ sprayDomain g → h 0 = z ∧ ∀ t ∈ uIcc c 0,
      (t, 0, z, 0) ∈ sprayDomain g ∧ HasDerivWithinAt h (geodesicSpray g (h t)) (uIcc c 0) t := by
    rintro c - ⟨-, x, I, hx, hcI, h0I, hx0⟩
    have hsub : uIcc c 0 ⊆ I := hx.interval.uIcc_subset hcI h0I
    have heq : EqOn h x (uIcc c 0) := fun s hs => by
      simpa [hh, hx0] using hrep 0 x I hx 0 h0I s (hsub hs)
    refine ⟨by simpa [hx0] using heq right_mem_uIcc, fun t ht => ⟨⟨mem_univ _, x, I, hx, hsub ht,
      h0I, hx0⟩, ?_⟩⟩
    have := ((hx.deriv t (hsub ht)).mono hsub).congr_of_mem heq ht
    rwa [← heq ht] at this
  obtain ⟨h0, ha'⟩ := side a ha.ne hza
  have hb' := (side b hb.ne' hzb).2
  have hmem : ∀ t ∈ Ioo a b, (t, 0, z, 0) ∈ sprayDomain g := fun t ht => by
    rcases le_total t 0 with ht0 | ht0
    · exact (ha' t ⟨by simp [ht.1.le], by simp [ht0]⟩).1
    · exact (hb' t ⟨by simp [ht0], by simp [ht.2.le]⟩).1
  have hsmooth : ContDiffOn ℝ ∞ h (Ioo a b) :=
    hX.comp (contDiff_id.prodMk contDiff_const).contDiffOn fun t ht => hmem t ht
  have hderiv : ∀ t ∈ Ioo a b, HasDerivAt h (geodesicSpray g (h t)) t := fun t ht => by
    have hd : DifferentiableAt ℝ h t :=
      (hsmooth.differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds ht)
    rcases le_total t 0 with ht0 | ht0
    · have ht' : t ∈ uIcc a 0 := ⟨by simp [ht.1.le], by simp [ht0]⟩
      exact hasDerivAt_of_hasDerivWithinAt_uIcc ha.ne ht' hd (ha' t ht').2
    · have ht' : t ∈ uIcc b 0 := ⟨by simp [ht0], by simp [ht.2.le]⟩
      exact hasDerivAt_of_hasDerivWithinAt_uIcc hb.ne' ht' hd (hb' t ht').2
  have hd1 : ∀ t ∈ Ioo a b, HasDerivAt (fun s => (h s).1) (h t).2 t := fun t ht =>
    (hderiv t ht).fst
  have hd2 : ∀ t ∈ Ioo a b, deriv (fun s => (h s).1) =ᶠ[𝓝 t] fun s => (h s).2 := fun t ht =>
    eventually_of_mem (isOpen_Ioo.mem_nhds ht) fun s hs => (hd1 s hs).deriv
  have h0ab : (0 : ℝ) ∈ Ioo a b := ⟨ha, hb⟩
  refine ⟨fun s => (h s).1, ⟨isOpen_Ioo, contDiff_fst.comp_contDiffOn hsmooth, fun t ht k => ?_⟩,
    by simp [h0], by rw [(hd1 0 h0ab).deriv, h0]⟩
  have h2 : HasDerivAt (fun s => (h s).2) (geodesicSpray g (h t)).2 t := (hderiv t ht).snd
  rw [(hd2 t ht).deriv_eq, h2.deriv, (hd1 t ht).deriv]
  simp [geodesicSpray, christoffelQuad_apply]

theorem exists_Icc_subset_of_isOpen {a b : ℝ} (hI : IsOpen I) (hab : a ≤ b)
    (h : Icc a b ⊆ I) : ∃ ε > 0, Icc (a - ε) (b + ε) ⊆ I := by
  obtain ⟨δ₁, hδ₁, h₁⟩ := Metric.isOpen_iff.1 hI a (h (left_mem_Icc.2 hab))
  obtain ⟨δ₂, hδ₂, h₂⟩ := Metric.isOpen_iff.1 hI b (h (right_mem_Icc.2 hab))
  refine ⟨min δ₁ δ₂ / 2, by positivity, fun t ht => ?_⟩
  have hm₁ := min_le_left δ₁ δ₂
  have hm₂ := min_le_right δ₁ δ₂
  have hm := lt_min hδ₁ hδ₂
  rcases lt_or_ge t a with hta | hta
  · exact h₁ (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1])
  rcases le_or_gt t b with htb | htb
  · exact h ⟨hta, htb⟩
  · exact h₂ (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [ht.2])

theorem isGeodesic_const (x : E n) : IsGeodesic g (fun _ => x) univ := by
  have h : deriv (fun _ : ℝ => x) = fun _ => 0 := funext fun _ => deriv_const _ _
  refine ⟨isOpen_univ, contDiffOn_const, fun t _ k => ?_⟩
  simp [h]

theorem IsGeodesic.mono (hγ : IsGeodesic g γ I) (hJ : J ⊆ I) (hJo : IsOpen J) :
    IsGeodesic g γ J :=
  ⟨hJo, hγ.smooth.mono hJ, fun t ht => hγ.equation t (hJ ht)⟩

theorem IsGeodesic.congr (hγ : IsGeodesic g γ I) (h : EqOn γ₁ γ I) : IsGeodesic g γ₁ I := by
  have hev : ∀ t ∈ I, γ₁ =ᶠ[𝓝 t] γ := fun t ht => eventually_of_mem (hγ.isOpen.mem_nhds ht) h
  have hev' : ∀ t ∈ I, deriv γ₁ =ᶠ[𝓝 t] deriv γ := fun t ht =>
    eventually_of_mem (hγ.isOpen.mem_nhds ht) fun s hs => (hev s hs).deriv_eq
  refine ⟨hγ.isOpen, hγ.smooth.congr h, fun t ht k => ?_⟩
  rw [(hev' t ht).deriv_eq, (hev t ht).deriv_eq, h ht]
  exact hγ.equation t ht k

theorem IsGeodesic.hasDerivAt_comp_affine (hγ : IsGeodesic g γ I) {c d s : ℝ}
    (hs : c * s + d ∈ I) :
    HasDerivAt (fun s => γ (c * s + d)) (c • deriv γ (c * s + d)) s := by
  have ha : HasDerivAt (fun s => c * s + d) c s := by
    simpa using ((hasDerivAt_id s).const_mul c).add_const d
  exact (hγ.hasDerivAt hs).scomp s ha

/-- Affine reparametrizations of geodesics are geodesics. -/
theorem IsGeodesic.comp_affine (hγ : IsGeodesic g γ I) (c d : ℝ) :
    IsGeodesic g (fun s => γ (c * s + d)) ((fun s => c * s + d) ⁻¹' I) := by
  have hcont : Continuous fun s : ℝ => c * s + d := by fun_prop
  have hO : IsOpen ((fun s => c * s + d) ⁻¹' I) := hγ.isOpen.preimage hcont
  refine ⟨hO, hγ.smooth.comp (by fun_prop : ContDiff ℝ ∞ fun s : ℝ => c * s + d).contDiffOn
    fun s hs => hs, fun t ht k => ?_⟩
  have hev : deriv (fun s => γ (c * s + d)) =ᶠ[𝓝 t] fun s => c • deriv γ (c * s + d) :=
    eventually_of_mem (hO.mem_nhds ht) fun s hs => (hγ.hasDerivAt_comp_affine hs).deriv
  have ha : HasDerivAt (fun s => c * s + d) c t := by
    simpa using ((hasDerivAt_id t).const_mul c).add_const d
  have h2 : HasDerivAt (fun s => c • deriv γ (c * s + d))
      (c • c • deriv (deriv γ) (c * t + d)) t :=
    ((hγ.hasDerivAt_deriv ht).scomp t ha).const_smul c
  rw [hev.deriv_eq, h2.deriv, (hγ.hasDerivAt_comp_affine ht).deriv]
  have heq := hγ.equation _ ht k
  simp only [PiLp.smul_apply, smul_eq_mul]
  have hsum : ∑ i, ∑ j, christoffel g (γ (c * t + d)) k i j * (c * deriv γ (c * t + d) i) *
      (c * deriv γ (c * t + d) j) = c * c * ∑ i, ∑ j, christoffel g (γ (c * t + d)) k i j *
        deriv γ (c * t + d) i * deriv γ (c * t + d) j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsum]
  linear_combination c * c * heq

theorem IsGeodesic.deriv_comp_affine (hγ : IsGeodesic g γ I) {c d s : ℝ}
    (hs : c * s + d ∈ I) :
    deriv (fun s => γ (c * s + d)) s = c • deriv γ (c * s + d) :=
  (hγ.hasDerivAt_comp_affine hs).deriv

/-! ### The exponential map -/

theorem IsGeodesic.inExpDomain (hγ : IsGeodesic g γ I) (hI : Icc 0 1 ⊆ I) :
    InExpDomain g (γ 0) (deriv γ 0) :=
  inExpDomain_iff.2 ⟨γ, I, hγ, hI, rfl, rfl⟩

/-- `exp_y w = γ(1)` for every geodesic `γ` with `γ(0) = y`, `γ̇(0) = w`, defined on `[0, 1]`. -/
theorem IsGeodesic.expMap_eq (hg : IsSpacetime g Y) (hγ : IsGeodesic g γ I) (hI : Icc 0 1 ⊆ I) :
    expMap g (γ 0) (deriv γ 0) = γ 1 := by
  have hd := hγ.inExpDomain hI
  simp only [expMap_def, hd, ↓reduceDIte]
  obtain ⟨hγ', hI', h0, h0'⟩ := (inExpDomain_iff.1 hd).choose_spec.choose_spec
  exact (IsGeodesic.eqOn hg hγ' hγ hI' hI ordConnected_Icc (left_mem_Icc.2 zero_le_one) h0
    h0').1 (right_mem_Icc.2 zero_le_one)

lemma mul_mem_uIcc {t s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : t * s ∈ uIcc 0 t := by
  rcases le_total 0 t with h | h
  · exact mem_uIcc.2 (Or.inl ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩)
  · exact mem_uIcc.2 (Or.inr ⟨by nlinarith [hs.2], by nlinarith [hs.1]⟩)

/-- `exp_y (t w) = γ(t)` for the geodesic `γ` with `γ(0) = y`, `γ̇(0) = w`, as long as `γ` is
defined between `0` and `t`. -/
theorem IsGeodesic.expMap_smul_eq (hg : IsSpacetime g Y) (hγ : IsGeodesic g γ I)
    (ht : uIcc 0 t ⊆ I) :
    InExpDomain g (γ 0) (t • deriv γ 0) ∧ expMap g (γ 0) (t • deriv γ 0) = γ t := by
  have h := hγ.comp_affine t 0
  have hsub : Icc 0 1 ⊆ (fun s => t * s + 0) ⁻¹' I := fun s hs => by
    simpa using ht (mul_mem_uIcc (t := t) hs)
  have h0 : t * 0 + 0 ∈ I := hsub (left_mem_Icc.2 zero_le_one)
  have hd := h.inExpDomain hsub
  have he := h.expMap_eq hg hsub
  rw [hγ.deriv_comp_affine h0] at hd he
  simp only [mul_zero, add_zero, mul_one] at hd he
  exact ⟨hd, he⟩

/-- The domain of the exponential map is open. -/
theorem isOpen_expDomain (hg : IsSpacetime g Y) :
    IsOpen { p : E n × E n | InExpDomain g p.1 p.2 } := by
  obtain ⟨X, hS, -, -⟩ := exists_sprayFlow hg
  refine isOpen_iff_mem_nhds.2 ?_
  rintro ⟨y, w⟩ h
  obtain ⟨γ, I, hγ, hI, rfl, rfl⟩ := inExpDomain_iff.1 h
  obtain ⟨ε, hε, hεI⟩ := exists_Icc_subset_of_isOpen hγ.isOpen zero_le_one hI
  have hsol := hγ.isODESolution hεI ordConnected_Icc 0
  have h0 : (0 : ℝ) ∈ Icc (0 - ε) (1 + ε) := ⟨by linarith, by linarith⟩
  have ha := mem_sprayDomain hsol (t := 0 - ε) ⟨le_rfl, by linarith⟩ h0
  have hb := mem_sprayDomain hsol (t := 1 + ε) ⟨by linarith, le_rfl⟩ h0
  have hN : IsOpen { p : E n × E n | ((0 - ε : ℝ), (0 : ℝ), p, (0 : ℝ)) ∈ sprayDomain g ∧
      ((1 + ε : ℝ), (0 : ℝ), p, (0 : ℝ)) ∈ sprayDomain g } :=
    (hS.preimage (by fun_prop)).inter (hS.preimage (by fun_prop))
  refine mem_of_superset (hN.mem_nhds ⟨ha, hb⟩) fun p hp => ?_
  obtain ⟨γ', hγ', h0', h0''⟩ :=
    exists_isGeodesic_of_mem_sprayDomain hg (by linarith) (by linarith) hp.1 hp.2
  exact inExpDomain_iff.2 ⟨γ', _, hγ', fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩, h0',
    h0''⟩

/-- The exponential map is smooth on its domain. -/
theorem contDiffOn_expMap (hg : IsSpacetime g Y) :
    ContDiffOn ℝ ∞ (fun p : E n × E n => expMap g p.1 p.2)
      { p : E n × E n | InExpDomain g p.1 p.2 } := by
  obtain ⟨X, -, hX, hrep⟩ := exists_sprayFlow hg
  have key : ∀ p : E n × E n, InExpDomain g p.1 p.2 →
      (1, 0, p, 0) ∈ sprayDomain g ∧ expMap g p.1 p.2 = (X (1, 0, p, 0)).1 := by
    rintro ⟨y, w⟩ h
    obtain ⟨γ, I, hγ, hI, rfl, rfl⟩ := inExpDomain_iff.1 h
    have hsol := hγ.isODESolution hI ordConnected_Icc 0
    have h0 : (0 : ℝ) ∈ Icc 0 1 := left_mem_Icc.2 zero_le_one
    have h1 : (1 : ℝ) ∈ Icc 0 1 := right_mem_Icc.2 zero_le_one
    refine ⟨mem_sprayDomain hsol h1 h0, ?_⟩
    rw [hrep 0 _ _ hsol 0 h0 1 h1, hγ.expMap_eq hg hI]
  refine (contDiff_fst.comp_contDiffOn (hX.comp (by fun_prop : ContDiff ℝ ∞
    fun p : E n × E n => ((1 : ℝ), (0 : ℝ), p, (0 : ℝ))).contDiffOn
      fun p hp => (key p hp).1)).congr fun p hp => (key p hp).2

/-- `t ↦ exp_y (t w)` is the geodesic with initial data `(y, w)`, on an open interval containing
`[0, 1]`. -/
theorem InExpDomain.isGeodesic_expMap_smul (hg : IsSpacetime g Y) {y w : E n}
    (h : InExpDomain g y w) : ∃ ε > 0,
      IsGeodesic g (fun t => expMap g y (t • w)) (Ioo (-ε) (1 + ε)) ∧
      (∀ t ∈ Ioo (-ε) (1 + ε), InExpDomain g y (t • w)) ∧
      expMap g y ((0 : ℝ) • w) = y ∧ deriv (fun t : ℝ => expMap g y (t • w)) 0 = w := by
  obtain ⟨γ, I, hγ, hI, rfl, rfl⟩ := inExpDomain_iff.1 h
  obtain ⟨ε, hε, hεI⟩ := exists_Icc_subset_of_isOpen hγ.isOpen zero_le_one hI
  have hsub : ∀ t ∈ Ioo (-ε) (1 + ε), uIcc 0 t ⊆ I := fun t ht =>
    (uIcc_subset_Icc ⟨by linarith, by linarith⟩ ⟨by linarith [ht.1], by linarith [ht.2]⟩).trans
      hεI
  have heq : EqOn (fun t => expMap g (γ 0) (t • deriv γ 0)) γ (Ioo (-ε) (1 + ε)) :=
    fun t ht => (hγ.expMap_smul_eq hg (hsub t ht)).2
  have h0 : (0 : ℝ) ∈ Ioo (-ε) (1 + ε) := ⟨by linarith, by linarith⟩
  refine ⟨ε, hε, ?_, fun t ht => (hγ.expMap_smul_eq hg (hsub t ht)).1, heq h0, ?_⟩
  · exact (hγ.mono (Ioo_subset_Icc_self.trans (by simpa using hεI)) isOpen_Ioo).congr heq
  · have hev : (fun t : ℝ => expMap g (γ 0) (t • deriv γ 0)) =ᶠ[𝓝 0] γ :=
      eventually_of_mem (isOpen_Ioo.mem_nhds h0) heq
    exact hev.deriv_eq

theorem expMap_zero (hg : IsSpacetime g Y) (y : E n) : expMap g y 0 = y := by
  simpa using (isGeodesic_const (g := g) y).expMap_eq hg (subset_univ _)

theorem InExpDomain.smul (hg : IsSpacetime g Y) {y w : E n} (h : InExpDomain g y w) {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ) 1) : InExpDomain g y (r • w) := by
  obtain ⟨ε, hε, -, h', -⟩ := h.isGeodesic_expMap_smul hg
  exact h' r ⟨by linarith [hr.1], by linarith [hr.2]⟩

/-- A geodesic segment with admissible velocities is a path. -/
theorem IsGeodesic.isPathOn (hγ : IsGeodesic g γ I) {P : E n → E n → Prop} {a b : ℝ}
    (hab : a < b) (hI : Icc a b ⊆ I) (hP : ∀ t ∈ Icc a b, P (γ t) (deriv γ t)) :
    IsPathOn P a b γ := by
  refine isPathOn_iff.2 ⟨hab, ∅, fun x y hax hxy hyb _ =>
    isPathPiece_iff.2 ⟨hγ.smooth.mono ?_, fun t ht => ?_⟩⟩
  · exact (Icc_subset_Icc hax hyb).trans hI
  · have ht' : t ∈ Icc a b := ⟨hax.trans ht.1, ht.2.trans hyb⟩
    rw [(hγ.hasDerivAt (hI ht')).hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hxy t ht)]
    exact hP t ht'

theorem IsGeodesic.causalLE (hγ : IsGeodesic g γ I) {a b : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ I)
    (hP : ∀ t ∈ Icc a b, IsFutureCausal g Y (γ t) (deriv γ t)) : CausalLE g Y (γ a) (γ b) := by
  rcases hab.lt_or_eq with hab | rfl
  · exact causalLE_of_isPathOn (hγ.isPathOn hab hI hP)
  · exact CausalLE.refl _

theorem IsGeodesic.chronLT (hγ : IsGeodesic g γ I) {a b : ℝ} (hab : a < b) (hI : Icc a b ⊆ I)
    (hP : ∀ t ∈ Icc a b, IsFutureTimelike g Y (γ t) (deriv γ t)) : ChronLT g Y (γ a) (γ b) :=
  chronLT_of_isPathOn (hγ.isPathOn hab hI hP)

/-! ### Constant causal character -/

lemma sum_sum_sum_eq_of_equiv {m : ℕ} {F G : Fin m → Fin m → Fin m → ℝ}
    (e : Fin m × Fin m × Fin m ≃ Fin m × Fin m × Fin m)
    (h : ∀ p, F p.1 p.2.1 p.2.2 = G (e p).1 (e p).2.1 (e p).2.2) :
    ∑ a, ∑ b, ∑ c, F a b c = ∑ a, ∑ b, ∑ c, G a b c := by
  simp only [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv e _ _ h

/-- The Christoffel term paired with the velocity: `g(Γ(v, v), v) = ½ ∂ₐg_bl vᵃ vᵇ vˡ`. -/
theorem form_christoffelQuad (hg : IsSpacetime g Y) (x v : E n) :
    form (g x) (christoffelQuad g x v) v =
      (1 / 2) * ∑ a, ∑ b, ∑ l, d (fun y => g y b l) x a * v a * v b * v l := by
  set P : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → ℝ := fun i j a => d (fun y => g y i j) x a
  set u : Fin (n + 1) → ℝ := fun l =>
    (1 / 2) * ∑ a, ∑ b, (P b l a + P a l b - P a b l) * v a * v b with hu
  have hΓ : (christoffelQuad g x v).ofLp = (g x)⁻¹ *ᵥ u := by
    funext k
    simp only [christoffelQuad_apply, christoffel_def, Matrix.mulVec, dotProduct, hu, P,
      Finset.mul_sum, Finset.sum_mul]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun l _ => by ring
  have hsymm : (g x)ᵀ = g x := (hg.lorentzian x).symm
  have hunit : IsUnit (g x).det := (hg.det_ne_zero x).isUnit
  have hform : form (g x) (christoffelQuad g x v) v = u ⬝ᵥ v.ofLp := by
    rw [form_eq_dotProduct, hΓ, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose,
      Matrix.vecMul_vecMul, Matrix.transpose_nonsing_inv, hsymm,
      Matrix.nonsing_inv_mul _ hunit, Matrix.vecMul_one]
  have e : u ⬝ᵥ v.ofLp = ∑ l, ∑ a, ∑ b, (1 / 2 * (P b l a * v a * v b * v l) +
      1 / 2 * (P a l b * v a * v b * v l) - 1 / 2 * (P a b l * v a * v b * v l)) := by
    simp only [dotProduct, hu]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [hform, e]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have h1 : ∑ l, ∑ a, ∑ b, 1 / 2 * (P b l a * v a * v b * v l) =
      ∑ a, ∑ b, ∑ l, 1 / 2 * (P b l a * v a * v b * v l) :=
    sum_sum_sum_eq_of_equiv ⟨fun p => (p.2.1, p.2.2, p.1), fun p => (p.2.2, p.1, p.2.1),
      fun _ => rfl, fun _ => rfl⟩ fun _ => rfl
  have h2 : ∑ l, ∑ a, ∑ b, 1 / 2 * (P a l b * v a * v b * v l) =
      ∑ a, ∑ b, ∑ l, 1 / 2 * (P b l a * v a * v b * v l) :=
    sum_sum_sum_eq_of_equiv ⟨fun p => (p.2.2, p.2.1, p.1), fun p => (p.2.2, p.2.1, p.1),
      fun _ => rfl, fun _ => rfl⟩ fun _ => by simp only [Equiv.coe_fn_mk]; ring
  have h3 : ∑ l, ∑ a, ∑ b, 1 / 2 * (P a b l * v a * v b * v l) =
      ∑ a, ∑ b, ∑ l, 1 / 2 * (P b l a * v a * v b * v l) :=
    sum_sum_sum_eq_of_equiv ⟨fun p => (p.1, p.2.1, p.2.2), fun p => (p.1, p.2.1, p.2.2),
      fun _ => rfl, fun _ => rfl⟩ fun _ => by simp only [Equiv.coe_fn_mk]; ring
  rw [h1, h2, h3]
  simp only [Finset.mul_sum, P]
  ring

/-- `g(γ̇, γ̇)` has zero derivative along a geodesic. -/
theorem IsGeodesic.hasDerivAt_form (hg : IsSpacetime g Y) (hγ : IsGeodesic g γ I) (ht : t ∈ I) :
    HasDerivAt (fun s => form (g (γ s)) (deriv γ s) (deriv γ s)) 0 t := by
  set v := deriv γ t
  set acc := deriv (deriv γ) t
  set x := γ t
  have hv : ∀ i, HasDerivAt (fun s => deriv γ s i) (acc i) t := fun i =>
    (EuclideanSpace.proj i : E n →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t (hγ.hasDerivAt_deriv ht)
  have hG : ∀ i j, HasDerivAt (fun s => g (γ s) i j) (fderiv ℝ (fun y => g y i j) x v) t :=
    fun i j => ((hg.smooth i j).differentiable (by simp) x).hasFDerivAt.comp_hasDerivAt t
      (hγ.hasDerivAt ht)
  have hq := HasDerivAt.sum (u := Finset.univ) fun i _ => HasDerivAt.sum (u := Finset.univ)
    fun j _ => ((hv i).mul (hG i j)).mul (hv j)
  simp only [form_def]
  convert hq using 1
  · funext s
    simp only [Finset.sum_apply, Pi.mul_apply]
  simp only [Pi.mul_apply]
  set P : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → ℝ := fun i j a => d (fun y => g y i j) x a
  have hD : ∀ i j, fderiv ℝ (fun y => g y i j) x v = ∑ a, P i j a * v a := fun i j => by
    simp only [P, d_def]
    exact apply_eq_sum_d _ v
  have hsplit : ∑ i, ∑ j, ((acc i * g x i j + v i * fderiv ℝ (fun y => g y i j) x v) * v j +
      v i * g x i j * acc j) = form (g x) acc v + form (g x) v acc +
        ∑ i, ∑ j, ∑ a, v i * (P i j a * v a) * v j := by
    simp only [form_def, hD, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [add_mul, Finset.sum_mul]
    ring
  have hM : ∑ i, ∑ j, ∑ a, v i * (P i j a * v a) * v j =
      ∑ a, ∑ b, ∑ l, P b l a * v a * v b * v l :=
    sum_sum_sum_eq_of_equiv ⟨fun p => (p.2.2, p.1, p.2.1), fun p => (p.2.1, p.2.2, p.1),
      fun _ => rfl, fun _ => rfl⟩ fun _ => by simp only [Equiv.coe_fn_mk]; ring
  have hacc : acc = -christoffelQuad g x v := hγ.deriv_deriv ht
  rw [hsplit, hM, form_comm (hg.lorentzian x).symm v acc, hacc, form_neg_left,
    form_christoffelQuad hg]
  ring

/-- `g(γ̇, γ̇)` is constant along a geodesic, on every interval of its domain. -/
theorem IsGeodesic.form_deriv_eq (hg : IsSpacetime g Y) (hγ : IsGeodesic g γ I) (hJ : J ⊆ I)
    (hJc : J.OrdConnected) {s : ℝ} (hs : s ∈ J) (ht : t ∈ J) :
    form (g (γ s)) (deriv γ s) (deriv γ s) = form (g (γ t)) (deriv γ t) (deriv γ t) := by
  have key : ∀ a ∈ J, ∀ b ∈ J, a ≤ b → form (g (γ b)) (deriv γ b) (deriv γ b) =
      form (g (γ a)) (deriv γ a) (deriv γ a) := by
    intro a ha b hb hab
    have hsub : Icc a b ⊆ I := (hJc.out ha hb).trans hJ
    refine constant_of_has_deriv_right_zero (fun r hr =>
      (hγ.hasDerivAt_form hg (hsub hr)).continuousAt.continuousWithinAt)
      (fun r hr => (hγ.hasDerivAt_form hg (hsub (Ico_subset_Icc_self hr))).hasDerivWithinAt)
      b ⟨hab, le_rfl⟩
  rcases le_total s t with h | h
  · exact (key s hs t ht h).symm
  · exact key t ht s hs h

/-- A geodesic with nonzero velocity at one time has nonzero velocity at all times. -/
theorem IsGeodesic.deriv_ne_zero (hg : IsSpacetime g Y) (hγ : IsGeodesic g γ I) (hJ : J ⊆ I)
    (hJc : J.OrdConnected) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (h : deriv γ t₀ ≠ 0) (ht : t ∈ J) :
    deriv γ t ≠ 0 := by
  intro h0
  refine h ?_
  have := (IsGeodesic.eqOn hg hγ (isGeodesic_const (γ t)) hJ (subset_univ J) hJc ht rfl
    (by rw [h0, deriv_const])).2 ht₀
  rwa [deriv_const] at this

theorem IsGeodesic.continuousOn_form_timeOrientation (hg : IsSpacetime g Y)
    (hγ : IsGeodesic g γ I) :
    ContinuousOn (fun t => form (g (γ t)) (deriv γ t) (Y (γ t))) I := by
  have hγc : ContinuousOn γ I := hγ.smooth.continuousOn
  have hdc : ContinuousOn (deriv γ) I := hγ.contDiffOn_deriv.continuousOn
  have hY : Continuous Y := hg.globallyHyperbolic.timeOrientation.continuous
  simp only [form_def]
  refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
  exact (((EuclideanSpace.proj i : E n →L[ℝ] ℝ).continuous.comp_continuousOn hdc).mul
    ((hg.smooth i j).continuous.comp_continuousOn hγc)).mul
    ((EuclideanSpace.proj j : E n →L[ℝ] ℝ).continuous.comp_continuousOn (hY.comp_continuousOn hγc))

/-- A geodesic that is future-directed causal at one time is so at all times. -/
theorem IsGeodesic.isFutureCausal (hg : IsSpacetime g Y) (hγ : IsGeodesic g γ I) (hJ : J ⊆ I)
    (hJc : J.OrdConnected) {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    (h : IsFutureCausal g Y (γ t₀) (deriv γ t₀)) (ht : t ∈ J) :
    IsFutureCausal g Y (γ t) (deriv γ t) := by
  have hne : ∀ s ∈ J, deriv γ s ≠ 0 := fun s hs => hγ.deriv_ne_zero hg hJ hJc ht₀ h.ne_zero hs
  have hc : ∀ s ∈ J, form (g (γ s)) (deriv γ s) (deriv γ s) ≤ 0 := fun s hs =>
    (hγ.form_deriv_eq hg hJ hJc hs ht₀).le.trans h.causal
  refine ⟨hne t ht, hc t ht, ?_⟩
  by_contra hf
  push Not at hf
  obtain ⟨s, hs, hs0⟩ := hJc.isPreconnected.intermediate_value ht₀ ht
    ((hγ.continuousOn_form_timeOrientation hg).mono hJ) ⟨h.future.le, hf⟩
  exact (hg.lorentzian (γ s)).form_ne_zero (hc s hs) (hne s hs)
    (hg.globallyHyperbolic.timeOrientation.timelike (γ s)) hs0

/-- A geodesic that is future-directed timelike at one time is so at all times. -/
theorem IsGeodesic.isFutureTimelike (hg : IsSpacetime g Y) (hγ : IsGeodesic g γ I) (hJ : J ⊆ I)
    (hJc : J.OrdConnected) {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    (h : IsFutureTimelike g Y (γ t₀) (deriv γ t₀)) (ht : t ∈ J) :
    IsFutureTimelike g Y (γ t) (deriv γ t) :=
  ⟨(hγ.form_deriv_eq hg hJ hJc ht ht₀).trans_lt h.timelike,
    (hγ.isFutureCausal hg hJ hJc ht₀ h.isFutureCausal ht).future⟩

end Geodesic

end

end LorentzianCalderon
