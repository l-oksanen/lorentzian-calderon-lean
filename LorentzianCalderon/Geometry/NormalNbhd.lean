module

public import LorentzianCalderon.Geometry.ExpDeriv
public import LorentzianCalderon.Geometry.InverseFunction

public section

/-!
# Totally normal neighbourhoods

An open set `W` is totally normal (with radius `ρ` and inverse `L`) if for each `a ∈ W`, `exp_a`
maps the ball `B(0, ρ)` diffeomorphically onto a normal neighbourhood of `a` that contains `W`,
with inverse `b ↦ L (a, b)` on `W`, and `L` is smooth on `W × W`. Every point has totally normal
neighbourhoods (`exists_isTotallyNormal`): this is the first step in the proof of O'Neill,
Semi-Riemannian geometry, Proposition 5.7, p. 130, after Lemma 5.6.

Along a curve `γ` in `W`, the function `Q(t) = g_a(L(a, γ t), L(a, γ t))` has derivative
`2 g(P, γ̇)`, where `P = d(exp_a)_w w`, `w = L(a, γ t)`, is the radial velocity at `γ t`
(`IsTotallyNormal.hasDerivWithinAt_form`): `grad Q = 2 P` by the Gauss lemma (O'Neill, p. 146).
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Set Filter Metric

variable {n : ℕ} {g : MatrixField n} {Y : E n → E n}

/-- The product rule for `s ↦ A(u(s), v(s))`. -/
theorem HasDerivWithinAt.form (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) {u v : ℝ → E n}
    {u' v' : E n} {s : Set ℝ} {t : ℝ} (hu : HasDerivWithinAt u u' s t)
    (hv : HasDerivWithinAt v v' s t) :
    HasDerivWithinAt (fun r => LorentzianCalderon.form A (u r) (v r))
      (LorentzianCalderon.form A u' (v t) + LorentzianCalderon.form A (u t) v') s t := by
  have hu' : ∀ i, HasDerivWithinAt (fun r => u r i) (u' i) s t := fun i =>
    (EuclideanSpace.proj i : E n →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt t hu
  have hv' : ∀ i, HasDerivWithinAt (fun r => v r i) (v' i) s t := fun i =>
    (EuclideanSpace.proj i : E n →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt t hv
  have hq := HasDerivWithinAt.fun_sum (u := Finset.univ) fun i _ =>
    HasDerivWithinAt.fun_sum (u := Finset.univ) fun j _ => ((hu' i).mul_const (A i j)).mul (hv' j)
  convert hq using 1
  · funext r
    simp only [LorentzianCalderon.form_def, Pi.mul_apply]
  · simp only [LorentzianCalderon.form_def, ← Finset.sum_add_distrib]

/-- The product rule for `s ↦ A(u(s), u(s))`, `A` symmetric. -/
theorem HasDerivWithinAt.form_self {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hA : Aᵀ = A)
    {u : ℝ → E n} {u' : E n} {s : Set ℝ} {t : ℝ} (hu : HasDerivWithinAt u u' s t) :
    HasDerivWithinAt (fun r => LorentzianCalderon.form A (u r) (u r))
      (2 * LorentzianCalderon.form A (u t) u') s t := by
  convert HasDerivWithinAt.form A hu hu using 1
  rw [form_comm hA u' (u t)]
  ring

/-- `W` is totally normal with radius `ρ` and inverse `L`: for `a ∈ W`, `exp_a` is defined,
nonsingular and injective on the ball `B(0, ρ)`, and `b ↦ L (a, b)` is a smooth inverse of it on
`W`. -/
structure IsTotallyNormal (g : MatrixField n) (W : Set (E n)) (ρ : ℝ) (L : E n × E n → E n) :
    Prop where
  isOpen : IsOpen W
  inExpDomain : ∀ a ∈ W, ∀ w ∈ ball (0 : E n) ρ, InExpDomain g a w
  bijective : ∀ a ∈ W, ∀ w ∈ ball (0 : E n) ρ, Function.Bijective (fderiv ℝ (expMap g a) w)
  injOn : ∀ a ∈ W, InjOn (expMap g a) (ball 0 ρ)
  mem_ball : ∀ a ∈ W, ∀ b ∈ W, L (a, b) ∈ ball (0 : E n) ρ
  expMap_inv : ∀ a ∈ W, ∀ b ∈ W, expMap g a (L (a, b)) = b
  smooth : ContDiffOn ℝ ∞ L (W ×ˢ W)

namespace IsTotallyNormal

variable {W : Set (E n)} {ρ : ℝ} {L : E n × E n → E n}

/-- An open subset of a totally normal set is totally normal. -/
theorem mono (hW : IsTotallyNormal g W ρ L) {W' : Set (E n)} (hW' : W' ⊆ W) (ho : IsOpen W') :
    IsTotallyNormal g W' ρ L where
  isOpen := ho
  inExpDomain a ha := hW.inExpDomain a (hW' ha)
  bijective a ha := hW.bijective a (hW' ha)
  injOn a ha := hW.injOn a (hW' ha)
  mem_ball a ha b hb := hW.mem_ball a (hW' ha) b (hW' hb)
  expMap_inv a ha b hb := hW.expMap_inv a (hW' ha) b (hW' hb)
  smooth := hW.smooth.mono (prod_mono hW' hW')

/-- The radius of a nonempty totally normal set is positive. -/
theorem pos (hW : IsTotallyNormal g W ρ L) {a : E n} (ha : a ∈ W) : 0 < ρ := by
  have := hW.mem_ball a ha a ha
  rw [Metric.mem_ball] at this
  exact dist_nonneg.trans_lt this

theorem zero_mem_ball (hW : IsTotallyNormal g W ρ L) {a : E n} (ha : a ∈ W) :
    (0 : E n) ∈ ball (0 : E n) ρ :=
  mem_ball_self (hW.pos ha)

/-- The ball `B(0, ρ)` is star-shaped (and symmetric) about `0`. -/
theorem smul_mem_ball {w : E n} (hw : w ∈ ball (0 : E n) ρ) {r : ℝ} (hr : |r| ≤ 1) :
    r • w ∈ ball (0 : E n) ρ := by
  rw [mem_ball_zero_iff] at hw ⊢
  rw [norm_smul, Real.norm_eq_abs]
  calc |r| * ‖w‖ ≤ 1 * ‖w‖ := by gcongr
    _ < ρ := by rwa [one_mul]

/-- `L (a, exp_a w) = w` for `w ∈ B(0, ρ)` with `exp_a w ∈ W`. -/
theorem inv_expMap (hW : IsTotallyNormal g W ρ L) {a : E n} (ha : a ∈ W) {w : E n}
    (hw : w ∈ ball (0 : E n) ρ) (hb : expMap g a w ∈ W) : L (a, expMap g a w) = w :=
  hW.injOn a ha (hW.mem_ball a ha _ hb) hw (hW.expMap_inv a ha _ hb)

/-- `L (a, a) = 0`. -/
theorem inv_self (hg : IsSpacetime g Y) (hW : IsTotallyNormal g W ρ L) {a : E n} (ha : a ∈ W) :
    L (a, a) = 0 := by
  have := hW.inv_expMap ha (hW.zero_mem_ball ha) (by rwa [expMap_zero hg])
  rwa [expMap_zero hg] at this

theorem continuousAt (hW : IsTotallyNormal g W ρ L) {a b : E n} (ha : a ∈ W) (hb : b ∈ W) :
    ContinuousAt L (a, b) :=
  hW.smooth.continuousOn.continuousAt ((hW.isOpen.prod hW.isOpen).mem_nhds ⟨ha, hb⟩)

/-- `t ↦ L (a, γ t)` is continuous on `s` if `γ` is and maps `s` into `W`. -/
theorem continuousOn_comp (hW : IsTotallyNormal g W ρ L) {a : E n} (ha : a ∈ W) {γ : ℝ → E n}
    {s : Set ℝ} (hγ : ContinuousOn γ s) (hγW : ∀ t ∈ s, γ t ∈ W) :
    ContinuousOn (fun t => L (a, γ t)) s :=
  hW.smooth.continuousOn.comp (continuousOn_const.prodMk hγ) fun t ht => ⟨ha, hγW t ht⟩

/-- Along a curve in `W`, `w(t) = L (a, γ t)` is differentiable with `d(exp_a)_w ẇ = γ̇`. -/
theorem hasDerivWithinAt_inv (hg : IsSpacetime g Y) (hW : IsTotallyNormal g W ρ L) {a : E n}
    (ha : a ∈ W) {γ : ℝ → E n} {v : E n} {s : Set ℝ} {t : ℝ} (hγ : HasDerivWithinAt γ v s t)
    (ht : γ t ∈ W) :
    ∃ w', HasDerivWithinAt (fun r => L (a, γ r)) w' s t ∧
      fderiv ℝ (expMap g a) (L (a, γ t)) w' = v := by
  have hL : HasFDerivAt L (fderiv ℝ L (a, γ t)) (a, γ t) :=
    ((hW.smooth.differentiableOn (by simp)).differentiableAt
      ((hW.isOpen.prod hW.isOpen).mem_nhds ⟨ha, ht⟩)).hasFDerivAt
  have hℓ : HasFDerivAt (fun y => L (a, y))
      ((fderiv ℝ L (a, γ t)).comp (ContinuousLinearMap.inr ℝ (E n) (E n))) (γ t) :=
    hL.comp (γ t) (hasFDerivAt_prodMk_right a (γ t))
  refine ⟨_, hℓ.comp_hasDerivWithinAt t hγ, ?_⟩
  have hdom := hW.inExpDomain a ha _ (hW.mem_ball a ha _ ht)
  have hE : HasFDerivAt (expMap g a) (fderiv ℝ (expMap g a) (L (a, γ t))) (L (a, γ t)) :=
    (hasFDerivAt_expMap hg (p := (a, L (a, γ t))) hdom).differentiableAt.hasFDerivAt
  have h1 := hE.comp (γ t) hℓ
  have h2 : HasFDerivAt (fun y => expMap g a (L (a, y))) (ContinuousLinearMap.id ℝ (E n))
      (γ t) :=
    (hasFDerivAt_id (γ t)).congr_of_eventuallyEq
      (eventually_of_mem (hW.isOpen.mem_nhds ht) fun y hy => hW.expMap_inv a ha y hy)
  have := h1.unique h2
  exact DFunLike.congr_fun this v

/-- `Q(t) = g_a(L(a, γ t), L(a, γ t))` has derivative `2 g(P, γ̇)`, `P` the radial velocity. -/
theorem hasDerivWithinAt_form (hg : IsSpacetime g Y) (hW : IsTotallyNormal g W ρ L) {a : E n}
    (ha : a ∈ W) {γ : ℝ → E n} {v : E n} {s : Set ℝ} {t : ℝ} (hγ : HasDerivWithinAt γ v s t)
    (ht : γ t ∈ W) :
    HasDerivWithinAt (fun r => form (g a) (L (a, γ r)) (L (a, γ r)))
      (2 * form (g (γ t)) (fderiv ℝ (expMap g a) (L (a, γ t)) (L (a, γ t))) v) s t := by
  obtain ⟨w', hw', hv⟩ := hW.hasDerivWithinAt_inv hg ha hγ ht
  have hdom := hW.inExpDomain a ha _ (hW.mem_ball a ha _ ht)
  convert HasDerivWithinAt.form_self (hg.symm a) hw' using 2
  rw [← hv, ← form_fderiv_expMap_radial hg hdom, hW.expMap_inv a ha _ ht]

end IsTotallyNormal

/-- Every point has a totally normal neighbourhood. O'Neill, Semi-Riemannian geometry, Lemma 5.6
and the proof of Proposition 5.7, p. 130. -/
theorem exists_isTotallyNormal (hg : IsSpacetime g Y) (x : E n) :
    ∃ W ρ L, x ∈ W ∧ IsTotallyNormal g W ρ L := by
  have hD := isOpen_expDomain hg
  have hx0 : InExpDomain g x 0 := inExpDomain_zero x
  have hbij0 : Function.Bijective (fderiv ℝ (expMap g x) 0) := by
    rw [fderiv_expMap_zero hg]
    exact Function.bijective_id
  obtain ⟨f', hf'⟩ := exists_hasFDerivAt_expPair hg (p := (x, 0)) hx0 hbij0
  obtain ⟨U, hU, hxU, hUD, hinj, -, hder, -⟩ := exists_injOn_contDiffOn_inverse hD
    (contDiffOn_expPair hg) isCompact_singleton (singleton_subset_iff.2 hx0)
    (injOn_singleton _ _) (by rintro p rfl; exact ⟨f', hf'⟩)
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU (x, 0) (hxU rfl)
  have hVU : ball x r ×ˢ ball (0 : E n) r ⊆ U := by rwa [ball_prod_same]
  have hx0V : ((x, 0) : E n × E n) ∈ ball x r ×ˢ ball (0 : E n) r :=
    ⟨mem_ball_self hr, mem_ball_self hr⟩
  obtain ⟨U₂, -, hxU₂, hU₂V, -, himg, -, h, hh, hhinv⟩ := exists_injOn_contDiffOn_inverse
    (isOpen_ball.prod isOpen_ball) ((contDiffOn_expPair hg).mono (hVU.trans hUD))
    isCompact_singleton (singleton_subset_iff.2 hx0V) (injOn_singleton _ _)
    (by rintro p rfl; exact ⟨f', hf'⟩)
  have hxx : ((x, x) : E n × E n) ∈ expPair g '' U₂ := by
    refine ⟨(x, 0), hxU₂ rfl, ?_⟩
    rw [expPair_def]
    rw [expMap_zero hg]
  obtain ⟨r₂, hr₂, hr₂U⟩ := Metric.isOpen_iff.1 himg (x, x) hxx
  have key : ∀ a ∈ ball x r₂, ∀ b ∈ ball x r₂, ∃ p ∈ U₂, p.1 = a ∧ expMap g a p.2 = b ∧
      h (a, b) = p := by
    intro a ha b hb
    have hab : ((a, b) : E n × E n) ∈ ball (x, x) r₂ := by
      rw [← ball_prod_same]
      exact ⟨ha, hb⟩
    obtain ⟨p, hp, hpab⟩ := hr₂U hab
    have h1 : p.1 = a := by simpa only [expPair_def] using congrArg Prod.fst hpab
    refine ⟨p, hp, h1, ?_, ?_⟩
    · have := congrArg Prod.snd hpab
      simpa [expPair_def, h1] using this
    · rw [← hpab]
      exact hhinv p hp
  have hW0 : ∀ a ∈ ball x r₂, a ∈ ball x r := fun a ha => by
    obtain ⟨p, hp, h1, -⟩ := key a ha a ha
    exact h1 ▸ (hU₂V hp).1
  have hV : ∀ a ∈ ball x r₂, ∀ w ∈ ball (0 : E n) r, ((a, w) : E n × E n) ∈ U :=
    fun a ha w hw => hVU (mk_mem_prod (hW0 a ha) hw)
  have hVD : ∀ a ∈ ball x r₂, ∀ w ∈ ball (0 : E n) r, InExpDomain g a w :=
    fun a ha w hw => hUD (hV a ha w hw)
  refine ⟨ball x r₂, r, fun q => (h q).2, mem_ball_self hr₂, ⟨isOpen_ball, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact hVD
  · intro a ha w hw
    obtain ⟨e, he⟩ := hder (a, w) (hV a ha w hw)
    exact bijective_fderiv_expMap hg (p := (a, w)) (hVD a ha w hw) he
  · intro a ha w₁ hw₁ w₂ hw₂ heq
    have := hinj (hV a ha w₁ hw₁) (hV a ha w₂ hw₂)
      (by simp only [expPair_def, heq])
    exact congrArg Prod.snd this
  · intro a ha b hb
    obtain ⟨p, hp, -, -, hhp⟩ := key a ha b hb
    simpa [hhp] using (hU₂V hp).2
  · intro a ha b hb
    obtain ⟨p, -, -, hpb, hhp⟩ := key a ha b hb
    simpa [hhp] using hpb
  · refine contDiff_snd.comp_contDiffOn (hh.mono ?_)
    rw [ball_prod_same]
    exact hr₂U

end

end LorentzianCalderon
