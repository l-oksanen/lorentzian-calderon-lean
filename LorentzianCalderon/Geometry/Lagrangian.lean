module

public import LorentzianCalderon.Geometry.Exp

public section

/-!
# The Lagrangian of the geodesic equation

The Lagrangian `L(x, ξ) = g_x(ξ, ξ)` on `ℝ^{1+n} × ℝ^{1+n}`. Its derivatives in the
direction of `ξ` are `∂_ξ L(x, ξ) η = 2 g_x(ξ, η)` and `∂_ξ² L(x, ξ)(η, ζ) = 2 g_x(η, ζ)`, and
geodesics satisfy the Euler–Lagrange equation
`d/dt (∂_ξ L(γ, γ̇) X) = dL(γ, γ̇)(X, Ẋ)` for every vector field `X` along `γ`
(`IsGeodesic.hasDerivAt_momentum`).
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Set Filter

variable {n : ℕ} {g : MatrixField n} {Y : E n → E n}

theorem contDiff_form (hg : IsSpacetime g Y) :
    ContDiff ℝ ∞ fun q : E n × E n × E n => form (g q.1) q.2.1 q.2.2 := by
  simp only [form_def]
  refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
  have hij : ContDiff ℝ ∞ fun q : E n × E n × E n => g q.1 i j :=
    (hg.smooth i j).comp contDiff_fst
  have h1 : ContDiff ℝ ∞ fun q : E n × E n × E n => q.2.1 i :=
    (EuclideanSpace.proj i : E n →L[ℝ] ℝ).contDiff.comp (contDiff_fst.comp contDiff_snd)
  have h2 : ContDiff ℝ ∞ fun q : E n × E n × E n => q.2.2 j :=
    (EuclideanSpace.proj j : E n →L[ℝ] ℝ).contDiff.comp (contDiff_snd.comp contDiff_snd)
  exact (h1.mul hij).mul h2

/-- The product rule for `s ↦ A(u(s), u(s))`, `A` symmetric. -/
theorem hasDerivAt_form_self {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hA : Aᵀ = A)
    {u : ℝ → E n} {u' : E n} {s : ℝ} (hu : HasDerivAt u u' s) :
    HasDerivAt (fun t => form A (u t) (u t)) (2 * form A (u s) u') s := by
  have hv : ∀ i, HasDerivAt (fun t => u t i) (u' i) s := fun i =>
    (EuclideanSpace.proj i : E n →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt s hu
  have hq := HasDerivAt.sum (u := Finset.univ) fun i _ => HasDerivAt.sum (u := Finset.univ)
    fun j _ => ((hv i).mul_const (A i j)).mul (hv j)
  have key : 2 * form A (u s) u' =
      ∑ i, ∑ j, (u' i * A i j * u s j + u s i * A i j * u' j) := by
    rw [two_mul]
    nth_rewrite 1 [form_comm hA]
    simp only [form_def, ← Finset.sum_add_distrib]
  rw [key]
  simp only [form_def]
  convert hq using 1
  funext t
  simp only [Finset.sum_apply, Pi.mul_apply]

/-- The derivative of `f` at `x` in the direction `v`, as the derivative along a line. -/
theorem hasDerivAt_line {G F : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : G → F}
    {x : G} (hf : DifferentiableAt ℝ f x) (v : G) :
    HasDerivAt (fun s : ℝ => f (x + s • v)) (fderiv ℝ f x v) 0 := by
  have hl : HasDerivAt (fun s : ℝ => x + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hf' : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • v) := by
    simpa using hf.hasFDerivAt
  exact hf'.comp_hasDerivAt 0 hl

/-- Nondegeneracy of the metric. -/
theorem exists_form_ne_zero (hg : IsSpacetime g Y) (x : E n) {w : E n} (hw : w ≠ 0) :
    ∃ z, form (g x) w z ≠ 0 := by
  by_contra! h
  refine hw ?_
  have hunit : IsUnit (g x).det := (hg.det_ne_zero x).isUnit
  have := h (WithLp.toLp 2 ((g x)⁻¹ *ᵥ w.ofLp))
  rw [form_eq_dotProduct] at this
  simp only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec] at this
  have h0 : w.ofLp = 0 := dotProduct_self_eq_zero.1 this
  exact WithLp.ofLp_injective 2 (by simpa using h0)

/-- The product rule for `t ↦ g_{x(t)}(v(t), w(t))`. -/
theorem hasDerivAt_form_apply (hg : IsSpacetime g Y) {x v w : ℝ → E n} {x' v' w' : E n}
    {t : ℝ} (hx : HasDerivAt x x' t) (hv : HasDerivAt v v' t) (hw : HasDerivAt w w' t) :
    HasDerivAt (fun t => form (g (x t)) (v t) (w t))
      (form (g (x t)) v' (w t) + form (g (x t)) (v t) w' +
        ∑ i, ∑ j, v t i * fderiv ℝ (fun y => g y i j) (x t) x' * w t j) t := by
  have hv' : ∀ i, HasDerivAt (fun s => v s i) (v' i) t := fun i =>
    (EuclideanSpace.proj i : E n →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t hv
  have hw' : ∀ i, HasDerivAt (fun s => w s i) (w' i) t := fun i =>
    (EuclideanSpace.proj i : E n →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t hw
  have hG : ∀ i j, HasDerivAt (fun s => g (x s) i j) (fderiv ℝ (fun y => g y i j) (x t) x') t :=
    fun i j => ((hg.smooth i j).differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t hx
  have hq := HasDerivAt.sum (u := Finset.univ) fun i _ => HasDerivAt.sum (u := Finset.univ)
    fun j _ => ((hv' i).mul (hG i j)).mul (hw' j)
  simp only [form_def]
  convert hq using 1
  · funext s
    simp only [Finset.sum_apply, Pi.mul_apply]
  · simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.mul_apply]
    ring

/-- The derivative of `x ↦ g_x(v, w)`. -/
theorem fderiv_form_apply (hg : IsSpacetime g Y) (x v w z : E n) :
    fderiv ℝ (fun y => form (g y) v w) x z =
      ∑ i, ∑ j, v i * fderiv ℝ (fun y => g y i j) x z * w j := by
  have hc : ContDiff ℝ ∞ (fun y => form (g y) v w) :=
    (contDiff_form hg).comp (contDiff_id.prodMk (contDiff_const (c := (v, w))))
  have hd : DifferentiableAt ℝ (fun y => form (g y) v w) x := hc.differentiable (by simp) x
  have hl : HasDerivAt (fun s : ℝ => x + s • z) z 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const z).const_add x
  have h := hasDerivAt_form_apply hg (v := fun _ => v) (w := fun _ => w) hl
    (hasDerivAt_const 0 v) (hasDerivAt_const 0 w)
  simp only [form_zero_left, form_zero_right, zero_add, zero_smul, add_zero] at h
  exact (hasDerivAt_line hd z).unique h

/-- The Christoffel term paired with a vector:
`g(Γ(v, v), w) = ½ (∂ₐg_bl + ∂_b g_al - ∂_l g_ab) vᵃ vᵇ wˡ`. -/
theorem form_christoffelQuad_left_sum (hg : IsSpacetime g Y) (x v w : E n) :
    form (g x) (christoffelQuad g x v) w =
      ∑ l, ∑ a, ∑ b, (1 / 2) * ((d (fun y => g y b l) x a + d (fun y => g y a l) x b -
        d (fun y => g y a b) x l) * v a * v b * w l) := by
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
  have hform : form (g x) (christoffelQuad g x v) w = u ⬝ᵥ w.ofLp := by
    rw [form_eq_dotProduct, hΓ, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose,
      Matrix.vecMul_vecMul, Matrix.transpose_nonsing_inv, hsymm,
      Matrix.nonsing_inv_mul _ hunit, Matrix.vecMul_one]
  rw [hform]
  simp only [dotProduct, hu, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun b _ => ?_
  simp only [P]
  ring

/-! ### The Lagrangian -/

/-- The Lagrangian `L(x, ξ) = g_x(ξ, ξ)` of the geodesic equation. -/
def lagrangian (g : MatrixField n) (z : E n × E n) : ℝ := form (g z.1) z.2 z.2

theorem lagrangian_def (g : MatrixField n) (z : E n × E n) :
    lagrangian g z =
      form (g z.1) z.2 z.2 := by rfl

theorem contDiff_lagrangian (hg : IsSpacetime g Y) : ContDiff ℝ ∞ (lagrangian g) :=
  (contDiff_form hg).comp (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_snd))

/-- The chain rule for `t ↦ df_{p(t)}(q(t))`. -/
theorem hasDerivAt_fderiv_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : F → ℝ} (hf : ContDiff ℝ ∞ f) {p q : ℝ → F} {p' q' : F} {t : ℝ}
    (hp : HasDerivAt p p' t) (hq : HasDerivAt q q' t) :
    HasDerivAt (fun t => fderiv ℝ f (p t) (q t))
      (fderiv ℝ (fderiv ℝ f) (p t) p' (q t) + fderiv ℝ f (p t) q') t := by
  have h1 : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) (p t)) (p t) :=
    ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) (p t)).hasFDerivAt
  exact (h1.comp_hasDerivAt t hp).clm_apply hq

/-- `∂_ξ L(x, ξ) w = 2 g_x(ξ, w)`. -/
theorem fderiv_lagrangian_inr (hg : IsSpacetime g Y) (z : E n × E n) (w : E n) :
    fderiv ℝ (lagrangian g) z (0, w) = 2 * form (g z.1) z.2 w := by
  have h1 := hasDerivAt_line (((contDiff_lagrangian hg).differentiable (by simp)) z)
    ((0 : E n), w)
  have hu : HasDerivAt (fun s : ℝ => z.2 + s • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add z.2
  have h2 := hasDerivAt_form_self (hg.symm z.1) hu
  simp only [zero_smul, add_zero] at h2
  refine h1.unique ?_
  simpa [lagrangian] using h2

/-- `∂_x L(x, ξ) w = d_x(g(ξ, ξ)) w`. -/
theorem fderiv_lagrangian_inl (hg : IsSpacetime g Y) (z : E n × E n) (w : E n) :
    fderiv ℝ (lagrangian g) z (w, 0) = fderiv ℝ (fun x => form (g x) z.2 z.2) z.1 w := by
  have hL : HasFDerivAt (lagrangian g) (fderiv ℝ (lagrangian g) z) (z.1, z.2) :=
    ((contDiff_lagrangian hg).differentiable (by simp) z).hasFDerivAt
  have h := hL.comp z.1 (hasFDerivAt_prodMk_left (𝕜 := ℝ) z.1 z.2)
  rw [show (fun x => form (g x) z.2 z.2) = lagrangian g ∘ fun x => (x, z.2) from rfl,
    h.fderiv]
  simp

/-- `∂_ξ² L(x, ξ)(a, b) = 2 g_x(a, b)`. -/
theorem fderiv_fderiv_lagrangian_inr (hg : IsSpacetime g Y) (z : E n × E n) (a b : E n) :
    fderiv ℝ (fderiv ℝ (lagrangian g)) z (0, a) (0, b) = 2 * form (g z.1) a b := by
  have hd : DifferentiableAt ℝ (fderiv ℝ (lagrangian g)) z :=
    ((contDiff_lagrangian hg).fderiv_right (m := ∞) (by simp)).differentiable (by simp) z
  have h1 := (hasDerivAt_line hd ((0 : E n), a)).clm_apply (hasDerivAt_const (0 : ℝ) ((0 : E n), b))
  simp only [map_zero, add_zero] at h1
  have h2 : HasDerivAt (fun s : ℝ => fderiv ℝ (lagrangian g) (z + s • ((0 : E n), a)) (0, b))
      (2 * form (g z.1) a b) 0 := by
    have : (fun s : ℝ => fderiv ℝ (lagrangian g) (z + s • ((0 : E n), a)) (0, b)) =
        fun s => 2 * form (g z.1) z.2 b + s * (2 * form (g z.1) a b) := by
      funext s
      rw [fderiv_lagrangian_inr hg]
      simp only [Prod.fst_add, Prod.smul_fst, smul_zero, add_zero, Prod.snd_add, Prod.smul_snd,
        form_add_left, form_smul_left]
      ring
    rw [this]
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (2 * form (g z.1) a b)).const_add
      (2 * form (g z.1) z.2 b)
  exact h1.unique h2

lemma sum_christoffel_algebra {m : ℕ} (P : Fin m → Fin m → Fin m → ℝ) (v w : Fin m → ℝ) :
    ∑ l, ∑ a, ∑ b, 1 / 2 * ((P b l a + P a l b - P a b l) * v a * v b * w l) =
      ∑ i, ∑ j, ∑ a, v i * (v a * P i j a) * w j -
        1 / 2 * ∑ i, ∑ j, ∑ a, v i * (w a * P i j a) * v j := by
  have T1 : ∑ l, ∑ a, ∑ b, P b l a * v a * v b * w l =
      ∑ i, ∑ j, ∑ a, v i * (v a * P i j a) * w j :=
    sum_sum_sum_eq_of_equiv ⟨fun p => (p.2.2, p.1, p.2.1), fun p => (p.2.1, p.2.2, p.1),
      fun _ => rfl, fun _ => rfl⟩ fun _ => by simp only [Equiv.coe_fn_mk]; ring
  have T2 : ∑ l, ∑ a, ∑ b, P a l b * v a * v b * w l =
      ∑ i, ∑ j, ∑ a, v i * (v a * P i j a) * w j :=
    sum_sum_sum_eq_of_equiv ⟨fun p => (p.2.1, p.1, p.2.2), fun p => (p.2.1, p.1, p.2.2),
      fun _ => rfl, fun _ => rfl⟩ fun _ => by simp only [Equiv.coe_fn_mk]; ring
  have T3 : ∑ l, ∑ a, ∑ b, P a b l * v a * v b * w l =
      ∑ i, ∑ j, ∑ a, v i * (w a * P i j a) * v j :=
    sum_sum_sum_eq_of_equiv ⟨fun p => (p.2.1, p.2.2, p.1), fun p => (p.2.2, p.1, p.2.1),
      fun _ => rfl, fun _ => rfl⟩ fun _ => by simp only [Equiv.coe_fn_mk]; ring
  have e : ∑ l, ∑ a, ∑ b, 1 / 2 * ((P b l a + P a l b - P a b l) * v a * v b * w l) =
      1 / 2 * (∑ l, ∑ a, ∑ b, P b l a * v a * v b * w l +
        ∑ l, ∑ a, ∑ b, P a l b * v a * v b * w l - ∑ l, ∑ a, ∑ b, P a b l * v a * v b * w l) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [e, T1, T2, T3]
  ring

/-- The Euler–Lagrange form of the geodesic equation: along a geodesic `γ`,
`d/dt (∂_ξ L(γ, γ̇) X) = dL(γ, γ̇)(X, Ẋ)` for every vector field `X`. -/
theorem IsGeodesic.hasDerivAt_momentum (hg : IsSpacetime g Y) {γ : ℝ → E n} {I : Set ℝ}
    (hγ : IsGeodesic g γ I) {t : ℝ} (ht : t ∈ I) {X : ℝ → E n} {X' : E n}
    (hX : HasDerivAt X X' t) :
    HasDerivAt (fun t => fderiv ℝ (lagrangian g) (γ t, deriv γ t) (0, X t))
      (fderiv ℝ (lagrangian g) (γ t, deriv γ t) (X t, X')) t := by
  have e1 : (fun t => fderiv ℝ (lagrangian g) (γ t, deriv γ t) (0, X t)) =
      fun t => 2 * form (g (γ t)) (deriv γ t) (X t) :=
    funext fun t => fderiv_lagrangian_inr hg _ _
  have e2 : fderiv ℝ (lagrangian g) (γ t, deriv γ t) (X t, X') =
      fderiv ℝ (fun x => form (g x) (deriv γ t) (deriv γ t)) (γ t) (X t) +
        2 * form (g (γ t)) (deriv γ t) X' := by
    rw [show (X t, X') = (X t, (0 : E n)) + ((0 : E n), X') by simp, map_add,
      fderiv_lagrangian_inl hg, fderiv_lagrangian_inr hg]
  rw [e1, e2]
  have h := (hasDerivAt_form_apply hg (hγ.hasDerivAt ht) (hγ.hasDerivAt_deriv ht) hX).const_mul 2
  convert h using 1
  rw [hγ.deriv_deriv ht, form_neg_left, form_christoffelQuad_left_sum hg, fderiv_form_apply hg]
  simp only [fderiv_apply_eq_sum_d, Finset.mul_sum, Finset.sum_mul]
  have := sum_christoffel_algebra (fun i j a => d (fun y => g y i j) (γ t) a) (deriv γ t).ofLp
    (X t).ofLp
  simp only at this
  rw [this]
  ring

end

end LorentzianCalderon
