module

public import LorentzianCalderon.Local.Naturality
public import LorentzianCalderon.Facts.Vocabulary

public section

/-!
# Rigidity of local isometries

If `F` and `F'` pull `g₂` back to `g₁` on a connected open set `U` and agree on a nonempty open
subset, they agree on `U` (Lemma `lem_rigidity` of the blueprint).

The proof uses the formula for the second derivatives of a local isometry,
`∂ᵢ∂ⱼFᵏ = Γ(g₁)ˡᵢⱼ ∂ₗFᵏ - Γ(g₂)ᵏₚ_q(F) ∂ᵢFᵖ ∂ⱼF^q`. Along a line `t ↦ x₀ + t v` the value and the
Jacobian matrix of `F` thus solve a first order system, whose solutions are unique. So the set
where `F = F'` and `DF = DF'` is open in `U`; it is also closed in `U` and nonempty.
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Matrix Finset

variable {n : ℕ}

section Algebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem sum_comm_rot (f : ι → ι → ι → ℝ) :
    ∑ a, ∑ b, ∑ c, f a b c = ∑ b, ∑ c, ∑ a, f a b c := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- The algebra behind `d_D_eq_christoffel`: `H a m i` stands for `∂ₘ∂ᵢFᵃ`, `dG c a b` for
`∂_c g₂_{ab}` and `dg m i j` for `∂ₘ g₁_{ij}`, where `g₁ = Jᵀ G J`. -/
theorem christoffel_pullback_algebra (J G : Matrix ι ι ℝ) (H dG dg : ι → ι → ι → ℝ)
    (hG : Gᵀ = G) (hdet : (Jᵀ * G * J).det ≠ 0) (hH : ∀ a i j, H a i j = H a j i)
    (hdg : ∀ m i j, dg m i j = ∑ a, ∑ b, (H a m i * G a b * J b j +
      J a i * (∑ c, dG c a b * J c m) * J b j + J a i * G a b * H b m j)) (k i j : ι) :
    H k i j = ∑ l, ((1 / 2) * ∑ r, (Jᵀ * G * J)⁻¹ l r * (dg i j r + dg j i r - dg r i j)) *
        J k l -
      ∑ p, ∑ q, ((1 / 2) * ∑ r, G⁻¹ k r * (dG p q r + dG q p r - dG r p q)) * J p i * J q j := by
  have hJ : J.det ≠ 0 := LorentzianCalderon.det_ne_zero_of_pullback rfl hdet
  set L : ι → ι → ι → ℝ := fun m i j => ∑ a, ∑ b, H a m i * G a b * J b j with hL
  set T : ι → ι → ι → ℝ := fun m i j => ∑ a, ∑ b, ∑ c, J c m * J a i * J b j * dG c a b
    with hT
  have hGs : ∀ a b, G a b = G b a := fun a b =>
    congrFun (congrFun hG b) a
  have hdg' : ∀ m i j, dg m i j = L m i j + T m i j + L m j i := by
    intro m i j
    rw [hdg]
    simp only [hL, hT, Finset.sum_add_distrib]
    congr 1
    · congr 1
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun c _ => by ring
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
        rw [hGs]; ring
  have hLs : ∀ m i j, L m i j = L i m j := fun m i j => by
    simp only [hL, hH _ m i]
  set K₂ : ι → ι → ι → ℝ := fun p q r => (1 / 2) * (dG p q r + dG q p r - dG r p q) with hK₂
  set W : ι → ℝ := fun r => ∑ a, H a i j * G a r + ∑ p, ∑ q, J p i * J q j * K₂ p q r
    with hW
  have h1 : ∀ s, dg i j s + dg j i s - dg s i j = 2 * ∑ r, J r s * W r := by
    intro s
    have hTT : T i j s + T j i s - T s i j =
        2 * ∑ r, J r s * ∑ p, ∑ q, J p i * J q j * K₂ p q r := by
      have e1 : T i j s = ∑ r, ∑ p, ∑ q, J p i * J q j * J r s * dG p q r := by
        simp only [hT]
        rw [sum_comm_rot]
      have e2 : T j i s = ∑ r, ∑ p, ∑ q, J p i * J q j * J r s * dG q p r := by
        simp only [hT]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
          Finset.sum_congr rfl fun _ _ => by ring
      have e3 : T s i j = ∑ r, ∑ p, ∑ q, J p i * J q j * J r s * dG r p q := by
        simp only [hT]
        rw [sum_comm_rot, sum_comm_rot]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
          Finset.sum_congr rfl fun _ _ => by ring
      rw [e1, e2, e3, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      simp only [hK₂]
      ring
    have hLL : L i j s = ∑ r, J r s * ∑ a, H a i j * G a r := by
      simp only [hL, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [hdg', hdg', hdg', hLs j i s, hLs s i j, hLs s j i]
    simp only [hW, mul_add, Finset.sum_add_distrib]
    rw [← hLL]
    linarith
  have hGdet : G.det ≠ 0 := by
    intro h
    apply hdet
    rw [det_mul, det_mul, h]
    ring
  have key : ∑ l, ((1 / 2) * ∑ r, (Jᵀ * G * J)⁻¹ l r * (2 * ∑ r', J r' r * W r')) * J k l =
      (G⁻¹ *ᵥ W) k := by
    have : ∑ l, ((1 / 2) * ∑ r, (Jᵀ * G * J)⁻¹ l r * (2 * ∑ r', J r' r * W r')) * J k l =
        (J *ᵥ ((Jᵀ * G * J)⁻¹ *ᵥ (Jᵀ *ᵥ W))) k := by
      simp only [mulVec, dotProduct, transpose_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [mul_comm (J k l), Finset.mul_sum]
      refine congrArg (· * J k l) (Finset.sum_congr rfl fun r _ => ?_)
      ring
    rw [this, mulVec_mulVec, mulVec_mulVec, mul_inv_pullback_mul_transpose hJ]
  have hinv : ∀ a, ∑ r, G⁻¹ k r * G a r = if k = a then 1 else 0 := fun a => by
    have := congrFun (congrFun (nonsing_inv_mul G hGdet.isUnit) k) a
    rw [mul_apply, one_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl fun r _ => by rw [hGs]
  simp only [h1]
  rw [key]
  simp only [mulVec, dotProduct, hW, mul_add, Finset.sum_add_distrib]
  have e4 : ∑ r, G⁻¹ k r * ∑ a, H a i j * G a r = H k i j := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [show ∀ a r, G⁻¹ k r * (H a i j * G a r) = H a i j * (G⁻¹ k r * G a r) from
      fun _ _ => by ring, ← Finset.mul_sum, hinv, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have e5 : ∑ r, G⁻¹ k r * ∑ p, ∑ q, J p i * J q j * K₂ p q r =
      ∑ p, ∑ q, ((1 / 2) * ∑ r, G⁻¹ k r * (dG p q r + dG q p r - dG r p q)) * J p i * J q j := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [sum_comm_rot]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by simp only [hK₂]; ring
  rw [e4, e5]
  ring

end Algebra

variable {g₁ g₂ : MatrixField n} {F : E n → E n} {x : E n}

/-- The second derivatives of a local isometry `F` with `g₁ = F^* g₂`:
`∂ᵢ∂ⱼFᵏ = Γ(g₁)ˡᵢⱼ ∂ₗFᵏ - Γ(g₂)ᵏₚ_q(F) ∂ᵢFᵖ ∂ⱼF^q`. -/
theorem d_D_eq_christoffel (hF : ContDiffAt ℝ 2 F x)
    (hg₂ : ∀ a b, DifferentiableAt ℝ (fun z => g₂ z a b) (F x))
    (hsymm : (g₂ (F x))ᵀ = g₂ (F x)) (hdet : (g₁ x).det ≠ 0)
    (hpull : ∀ᶠ y in 𝓝 x, g₁ y = (D F y)ᵀ * g₂ (F y) * D F y) (k i j : Fin (n + 1)) :
    d (fun y => D F y k j) x i =
      ∑ l, christoffel g₁ x l i j * D F x k l -
        ∑ p, ∑ q, christoffel g₂ (F x) k p q * D F x p i * D F x q j := by
  have hD := differentiableAt_D hF
  have hFd : DifferentiableAt ℝ F x := hF.differentiableAt (by simp)
  have hgF : ∀ a b, DifferentiableAt ℝ (fun y => g₂ (F y) a b) x := fun a b =>
    (hg₂ a b).comp x hFd
  have hx := hpull.self_of_nhds
  simp only [christoffel_def]
  rw [hx] at hdet ⊢
  refine christoffel_pullback_algebra (D F x) (g₂ (F x)) (fun a m i => d (fun y => D F y a i) x m)
    (fun c a b => d (fun z => g₂ z a b) (F x) c) (fun m a b => d (fun y => g₁ y a b) x m)
    hsymm hdet (fun a i j => (d_D_comm hF a i j).symm) (fun m i j => ?_) k i j
  have he : (fun y => g₁ y i j) =ᶠ[𝓝 x]
      fun y => ∑ a, ∑ b, D F y a i * g₂ (F y) a b * D F y b j := by
    filter_upwards [hpull] with y hy
    rw [hy]
    simp only [mul_apply, transpose_apply, Finset.sum_mul]
    exact Finset.sum_comm
  have hP : ∀ a b, DifferentiableAt ℝ (fun y => D F y a i * g₂ (F y) a b * D F y b j) x :=
    fun a b => ((hD a i).mul (hgF a b)).mul (hD b j)
  rw [d_congr he, d_sum (u := fun a y => ∑ b, D F y a i * g₂ (F y) a b * D F y b j)
    fun a _ => DifferentiableAt.fun_sum fun b _ => hP a b]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [d_sum (u := fun b y => D F y a i * g₂ (F y) a b * D F y b j) fun b _ => hP a b]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hab : DifferentiableAt ℝ (fun y => D F y a i * g₂ (F y) a b) x := (hD a i).mul (hgF a b)
  rw [d_mul hab (hD b j), d_mul (u := fun y => D F y a i) (hD a i) (hgF a b),
    d_comp (v := fun z => g₂ z a b) (hg₂ a b) hFd]
  simp only [d_coord_comp hFd]
  ring

/-- The Christoffel symbols of a `C²` metric are `C¹`. -/
theorem contDiffAt_christoffel {g : MatrixField n} (hg : ∀ i j, ContDiffAt ℝ 2 (fun y => g y i j) x)
    (hdet : (g x).det ≠ 0) (k i j : Fin (n + 1)) :
    ContDiffAt ℝ 1 (fun y => christoffel g y k i j) x := by
  have hg1 : ∀ i j, ContDiffAt ℝ 1 (fun y => g y i j) x := fun i j =>
    (hg i j).of_le (by norm_num)
  have hd : ∀ a b c, ContDiffAt ℝ 1 (fun y => d (fun z => g z a b) y c) x := fun a b c =>
    contDiffAt_d (m := 1) (hg a b) c
  simp only [christoffel_def]
  exact contDiffAt_const.mul (ContDiffAt.sum fun l _ =>
    (contDiffAt_inv hg1 hdet k l).mul (((hd j l i).add (hd i l j)).sub (hd i j l)))

/-- The state of the first order system along a line: the parameter, a point and a matrix. -/
abbrev JetState (n : ℕ) := ℝ × (Fin (n + 1) → ℝ) × (Fin (n + 1) → Fin (n + 1) → ℝ)

/-- The first order system satisfied by `t ↦ (t, F(x₀ + t v), DF(x₀ + t v))` for a local
isometry `F` with `g₁ = F^* g₂`. -/
def jetField (g₁ g₂ : MatrixField n) (x₀ v : E n) (w : JetState n) : JetState n :=
  (1, fun k => ∑ i, v i * w.2.2 k i, fun k j => ∑ i, v i *
    (∑ l, christoffel g₁ (x₀ + w.1 • v) l i j * w.2.2 k l -
      ∑ p, ∑ q, christoffel g₂ ((EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm w.2.1) k p q *
        w.2.2 p i * w.2.2 q j))

/-- The value and the Jacobian matrix of `F` along the line `t ↦ x₀ + t v`. -/
def jet (F : E n → E n) (x₀ v : E n) (t : ℝ) : JetState n :=
  (t, fun k => F (x₀ + t • v) k, fun k j => D F (x₀ + t • v) k j)

theorem hasDerivAt_comp_line {u : E n → ℝ} {x₀ v : E n} {t : ℝ}
    (hu : DifferentiableAt ℝ u (x₀ + t • v)) :
    HasDerivAt (fun s => u (x₀ + s • v)) (∑ i, v i * d u (x₀ + t • v) i) t := by
  have hγ : HasDerivAt (fun s : ℝ => x₀ + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x₀
  rw [← fderiv_apply_eq_sum_d]
  exact hu.hasFDerivAt.comp_hasDerivAt t hγ

theorem hasDerivAt_jet {x₀ v : E n} {t : ℝ} (hF : ContDiffAt ℝ 2 F (x₀ + t • v))
    (hg₂ : ∀ a b, DifferentiableAt ℝ (fun z => g₂ z a b) (F (x₀ + t • v)))
    (hsymm : (g₂ (F (x₀ + t • v)))ᵀ = g₂ (F (x₀ + t • v))) (hdet : (g₁ (x₀ + t • v)).det ≠ 0)
    (hpull : ∀ᶠ y in 𝓝 (x₀ + t • v), g₁ y = (D F y)ᵀ * g₂ (F y) * D F y) :
    HasDerivAt (jet F x₀ v) (jetField g₁ g₂ x₀ v (jet F x₀ v t)) t := by
  have hFd : DifferentiableAt ℝ F (x₀ + t • v) := hF.differentiableAt (by simp)
  refine (hasDerivAt_id t).prodMk ((hasDerivAt_pi.2 fun k => ?_).prodMk
    (hasDerivAt_pi.2 fun k => hasDerivAt_pi.2 fun j => ?_))
  · have := hasDerivAt_comp_line (u := fun y => F y k)
      ((contDiffAt_coord hF k).differentiableAt (by simp))
    simp only [d_coord_comp hFd] at this
    exact this
  · have := hasDerivAt_comp_line (differentiableAt_D hF k j)
    rw [show jet F x₀ v t = (t, fun k => F (x₀ + t • v) k, fun k j => D F (x₀ + t • v) k j)
      from rfl]
    convert this using 2 with i
    rw [d_D_eq_christoffel hF hg₂ hsymm hdet hpull]
    rfl

/-- Local uniqueness for the first order system. -/
theorem jet_eventuallyEq {F F' : E n → E n} {x₀ v : E n} {t₀ : ℝ}
    (hjF : ∀ᶠ t in 𝓝 t₀, HasDerivAt (jet F x₀ v) (jetField g₁ g₂ x₀ v (jet F x₀ v t)) t)
    (hjF' : ∀ᶠ t in 𝓝 t₀, HasDerivAt (jet F' x₀ v) (jetField g₁ g₂ x₀ v (jet F' x₀ v t)) t)
    (hc : ContDiffAt ℝ 1 (jetField g₁ g₂ x₀ v) (jet F x₀ v t₀))
    (h₀ : jet F x₀ v t₀ = jet F' x₀ v t₀) : jet F x₀ v =ᶠ[𝓝 t₀] jet F' x₀ v := by
  obtain ⟨K, N, hN, hK⟩ := hc.exists_lipschitzOnWith
  have mF := hjF.self_of_nhds.continuousAt.eventually_mem hN
  have mF' := hjF'.self_of_nhds.continuousAt.eventually_mem (h₀ ▸ hN)
  exact ODE_solution_unique_of_eventually (v := fun _ => jetField g₁ g₂ x₀ v) (s := fun _ => N)
    (Filter.Eventually.of_forall fun _ => hK) (hjF.and mF) (hjF'.and mF') h₀

/-- Two functions continuous on a preconnected set, which agree near each point where they
agree, agree everywhere on it once they agree at one point. -/
theorem eqOn_of_isPreconnected {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] {s : Set X} (hs : IsPreconnected s) {f g : X → Y}
    (hf : ∀ x ∈ s, ContinuousAt f x) (hg : ∀ x ∈ s, ContinuousAt g x)
    (hloc : ∀ x ∈ s, f x = g x → f =ᶠ[𝓝 x] g) {x₀ : X} (hx₀ : x₀ ∈ s) (h₀ : f x₀ = g x₀) :
    Set.EqOn f g s := by
  have hsub := hs.subset_of_closure_inter_subset (u := {x | f =ᶠ[𝓝 x] g})
    isOpen_setOfPred_eventually_nhds ⟨x₀, hx₀, hloc x₀ hx₀ h₀⟩ ?_
  · exact fun x hx => (hsub hx).self_of_nhds
  rintro x ⟨hxc, hxs⟩
  refine hloc x hxs (by_contra fun hne => ?_)
  have hev : ∀ᶠ z in 𝓝 x, (f z, g z) ∈ (Set.diagonal Y)ᶜ :=
    ((hf x hxs).prodMk_nhds (hg x hxs)).eventually
      (isClosed_diagonal.isOpen_compl.mem_nhds hne)
  obtain ⟨z, hzu, hz⟩ := ((mem_closure_iff_frequently.mp hxc).and_eventually hev).exists
  exact hz hzu.self_of_nhds

theorem contDiffAt_jetField {x₀ v : E n} {w : JetState n}
    (hg₁ : ∀ i j, ContDiffAt ℝ 2 (fun y => g₁ y i j) (x₀ + w.1 • v))
    (hdet₁ : (g₁ (x₀ + w.1 • v)).det ≠ 0)
    (hg₂ : ∀ i j, ContDiffAt ℝ 2 (fun y => g₂ y i j)
      ((EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm w.2.1))
    (hdet₂ : (g₂ ((EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm w.2.1)).det ≠ 0) :
    ContDiffAt ℝ 1 (jetField g₁ g₂ x₀ v) w := by
  have h₁ : ∀ l i j, ContDiffAt ℝ 1
      (fun w : JetState n => christoffel g₁ (x₀ + w.1 • v) l i j) w :=
    fun l i j => (contDiffAt_christoffel hg₁ hdet₁ l i j).comp
      (g := fun y => christoffel g₁ y l i j)
      (f := fun w : JetState n => x₀ + w.1 • v) w (by fun_prop)
  have h₂ : ∀ k p q, ContDiffAt ℝ 1 (fun w : JetState n =>
      christoffel g₂ ((EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm w.2.1) k p q) w :=
    fun k p q => (contDiffAt_christoffel hg₂ hdet₂ k p q).comp
      (g := fun y => christoffel g₂ y k p q)
      (f := fun w : JetState n => (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm w.2.1) w
      (by fun_prop)
  have hM : ∀ a b, ContDiffAt ℝ 1 (fun w : JetState n => w.2.2 a b) w := fun a b => by
    fun_prop
  refine contDiffAt_const.prodMk ((contDiffAt_pi.2 fun k => ?_).prodMk
    (contDiffAt_pi.2 fun k => contDiffAt_pi.2 fun j => ?_))
  · exact ContDiffAt.sum fun i _ => contDiffAt_const.mul (hM k i)
  · exact ContDiffAt.sum fun i _ => contDiffAt_const.mul
      ((ContDiffAt.sum fun l _ => (h₁ l i j).mul (hM k l)).sub
        (ContDiffAt.sum fun p _ => ContDiffAt.sum fun q _ =>
          ((h₂ k p q).mul (hM p i)).mul (hM q j)))

/-- Rigidity of local isometries: two local isometries `F, F'` from `(U, g₁)` to
`(ℝ^{1+n}, g₂)` that agree on a nonempty open subset of the connected open set `U` agree on
`U`. -/
theorem eqOn_of_pullback_eq {g₁ g₂ : MatrixField n} {F F' : E n → E n} {U V : Set (E n)}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    (hg₁ : ∀ i j, ContDiffOn ℝ ∞ (fun x => g₁ x i j) U) (hdet₁ : ∀ x ∈ U, (g₁ x).det ≠ 0)
    (hg₂ : ∀ i j, ContDiff ℝ ∞ (fun x => g₂ x i j)) (hsymm₂ : ∀ x, (g₂ x)ᵀ = g₂ x)
    (hdet₂ : ∀ x, (g₂ x).det ≠ 0) (hF : ContDiffOn ℝ ∞ F U) (hF' : ContDiffOn ℝ ∞ F' U)
    (hpull : ∀ x ∈ U, g₁ x = (D F x)ᵀ * g₂ (F x) * D F x)
    (hpull' : ∀ x ∈ U, g₁ x = (D F' x)ᵀ * g₂ (F' x) * D F' x)
    (hV : IsOpen V) (hVU : V ⊆ U) (hVne : V.Nonempty) (hFV : Set.EqOn F F' V) :
    Set.EqOn F F' U := by
  have h2 : ∀ {G : E n → E n}, ContDiffOn ℝ ∞ G U → ∀ x ∈ U, ContDiffAt ℝ 2 G x :=
    fun hG x hx => (hG.contDiffAt (hU.mem_nhds hx)).of_le (by simp)
  have hder : ∀ G : E n → E n, ContDiffOn ℝ ∞ G U →
      (∀ x ∈ U, g₁ x = (D G x)ᵀ * g₂ (G x) * D G x) → ∀ x₀ v : E n, ∀ t, x₀ + t • v ∈ U →
      ∀ᶠ s in 𝓝 t, HasDerivAt (jet G x₀ v) (jetField g₁ g₂ x₀ v (jet G x₀ v s)) s := by
    intro G hG hGp x₀ v t ht
    have hγ : ∀ᶠ s in 𝓝 t, x₀ + s • v ∈ U :=
      (by fun_prop : Continuous fun s : ℝ => x₀ + s • v).continuousAt.eventually_mem
        (hU.mem_nhds ht)
    filter_upwards [hγ] with s hs
    exact hasDerivAt_jet (h2 hG _ hs)
      (fun a b => ((hg₂ a b).differentiable (by simp)).differentiableAt) (hsymm₂ _)
      (hdet₁ _ hs) (Filter.eventually_of_mem (hU.mem_nhds hs) hGp)
  have hloc : ∀ x₀ ∈ U, F x₀ = F' x₀ → D F x₀ = D F' x₀ → F =ᶠ[𝓝 x₀] F' := by
    intro x₀ hx₀ h₀ hD₀
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU x₀ hx₀
    filter_upwards [Metric.ball_mem_nhds x₀ hr] with x hx
    set v := x - x₀ with hv
    set I : Set ℝ := {t | x₀ + t • v ∈ Metric.ball x₀ r} with hI
    have hIc : IsPreconnected I := by
      refine Convex.isPreconnected ?_
      have : I = (AffineMap.lineMap x₀ x : ℝ →ᵃ[ℝ] E n) ⁻¹' Metric.ball x₀ r := by
        ext t
        simp [hI, hv, AffineMap.lineMap_apply_module', add_comm]
      rw [this]
      exact (convex_ball x₀ r).affine_preimage _
    have hIU : ∀ t ∈ I, x₀ + t • v ∈ U := fun t ht => hball ht
    have hcd : ∀ t ∈ I, ContDiffAt ℝ 1 (jetField g₁ g₂ x₀ v) (jet F x₀ v t) := by
      intro t ht
      have ht' := hIU t ht
      exact contDiffAt_jetField
        (fun i j => ((hg₁ i j).contDiffAt (hU.mem_nhds ht')).of_le (by simp)) (hdet₁ _ ht')
        (fun i j => (hg₂ i j).contDiffAt.of_le (by simp)) (hdet₂ _)
    have heq := eqOn_of_isPreconnected hIc
      (fun t ht => (hder F hF hpull x₀ v t (hIU t ht)).self_of_nhds.continuousAt)
      (fun t ht => (hder F' hF' hpull' x₀ v t (hIU t ht)).self_of_nhds.continuousAt)
      (fun t ht h => jet_eventuallyEq (hder F hF hpull x₀ v t (hIU t ht))
        (hder F' hF' hpull' x₀ v t (hIU t ht)) (hcd t ht) h)
      (x₀ := 0) (by simp [hI, hr]) (by simp [jet, h₀, hD₀])
    have h1I : (1 : ℝ) ∈ I := by simpa [hI, hv, dist_eq_norm] using hx
    have h1 := congrArg (fun w => w.2.1) (heq h1I)
    have hx1 : x₀ + (1 : ℝ) • v = x := by simp [hv]
    simp only [jet, hx1] at h1
    exact PiLp.ext (congrFun h1)
  have hDeq : ∀ y, F =ᶠ[𝓝 y] F' → D F y = D F' y := fun y h => by
    ext i j
    simp only [D_def, h.fderiv_eq]
  have hcont : ∀ G : E n → E n, ContDiffOn ℝ ∞ G U →
      ∀ x ∈ U, ContinuousAt (fun x => (G x, fun k j => D G x k j)) x := by
    intro G hG x hx
    exact (h2 hG x hx).continuousAt.prodMk (continuousAt_pi.2 fun k => continuousAt_pi.2
      fun j => (differentiableAt_D (h2 hG x hx) k j).continuousAt)
  obtain ⟨x₀, hx₀⟩ := hVne
  have hFF : F =ᶠ[𝓝 x₀] F' := Filter.eventually_of_mem (hV.mem_nhds hx₀) hFV
  have heq := eqOn_of_isPreconnected hUc (hcont F hF) (hcont F' hF') ?_ (hVU hx₀)
    (by simp only [hFV hx₀, hDeq x₀ hFF])
  · exact fun x hx => congrArg Prod.fst (heq hx)
  intro x hx h
  have hFx := hloc x hx (congrArg Prod.fst h) (by
    ext k j
    exact congrFun (congrFun (congrArg Prod.snd h) k) j)
  filter_upwards [hFx.eventuallyEq_nhds] with y hy
  simp only [hy.self_of_nhds, hDeq y hy]

end

end LorentzianCalderon
