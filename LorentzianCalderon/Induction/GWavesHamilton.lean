module

public import LorentzianCalderon.Waves.OneSided
public import LorentzianCalderon.Local.Energy.Coform
public import LorentzianCalderon.ODE.Dependence
public import LorentzianCalderon.Induction.Lift

public section

/-!
# Hamiltonian flows and the method of characteristics

Tools for `lem_g_waves`, Step 1. Covectors are represented by their components, as points of
`E n`, paired with vectors by the Euclidean inner product.

* `hamField 𝓗 = (∂_ξ 𝓗, -∂_x 𝓗)` is the Hamiltonian vector field of `𝓗 : E n × E n → ℝ`.
* Along a family `Γ(r, y)` of integral curves of `hamField 𝓗`, `𝓗 ∘ Γ` is constant in `r`
  (`fderiv_comp_hamFlow_eq_zero`), and if `𝓗` is quadratic in `ξ`, the pairing of `ξ` with the
  variation `∂_w x` satisfies `∂_r ⟪ξ, ∂_w x⟫ = ∂_w (𝓗 ∘ Γ)` (`fderiv_inner_hamFlow`). This is
  the computation behind the solution of the eikonal equation by characteristics.
* `hamG g (x, ξ) = ½ g^{-1}(ξ, ξ)`, whose `∂_ξ` is `g^{-1} ξ` (`hamGradξ_hamG`).
-/

namespace LorentzianCalderon

noncomputable section
open Set Filter Function
open scoped ContDiff Topology RealInnerProductSpace Matrix

variable {n : ℕ}

/-! ### Vectors of linear forms -/

/-- The vector representing a linear form by the Euclidean inner product. -/
def vecOf (f : E n →L[ℝ] ℝ) : E n :=
  (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm fun i => f (EuclideanSpace.single i 1)

theorem vecOf_def (f : E n →L[ℝ] ℝ) :
    vecOf f =
      (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm fun i => f (EuclideanSpace.single i 1) := by rfl

lemma inner_vecOf (f : E n →L[ℝ] ℝ) (v : E n) : ⟪vecOf f, v⟫ = f v := by
  rw [clm_apply_eq_sum f v, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [vecOf]

/-- `vecOf` as a continuous linear map. -/
def vecOfL : (E n →L[ℝ] ℝ) →L[ℝ] E n :=
  (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i =>
      ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ)))

lemma vecOfL_apply (f : E n →L[ℝ] ℝ) : vecOfL f = vecOf f := by rfl

/-! ### The Hamiltonian field -/

section Hamilton

variable (𝓗 : E n × E n → ℝ)

/-- `∂_x 𝓗` as a vector. -/
def hamGradX (z : E n × E n) : E n :=
  vecOf ((fderiv ℝ 𝓗 z).comp (ContinuousLinearMap.inl ℝ (E n) (E n)))

/-- `∂_ξ 𝓗` as a vector. -/
def hamGradξ (z : E n × E n) : E n :=
  vecOf ((fderiv ℝ 𝓗 z).comp (ContinuousLinearMap.inr ℝ (E n) (E n)))

/-- The Hamiltonian vector field `(∂_ξ 𝓗, -∂_x 𝓗)`. -/
def hamField (z : E n × E n) : E n × E n :=
  (hamGradξ 𝓗 z, -hamGradX 𝓗 z)

theorem hamField_def (z : E n × E n) :
    hamField 𝓗 z =
      (hamGradξ 𝓗 z, -hamGradX 𝓗 z) := by rfl

theorem hamField_fst (z : E n × E n) : (hamField 𝓗 z).1 = hamGradξ 𝓗 z := by rfl

variable {𝓗}

lemma inner_hamGradX (z : E n × E n) (v : E n) : ⟪hamGradX 𝓗 z, v⟫ = fderiv ℝ 𝓗 z (v, 0) := by
  simp [hamGradX, inner_vecOf]

lemma inner_hamGradξ (z : E n × E n) (v : E n) : ⟪hamGradξ 𝓗 z, v⟫ = fderiv ℝ 𝓗 z (0, v) := by
  simp [hamGradξ, inner_vecOf]

lemma fderiv_apply_eq_inner (z : E n × E n) (v : E n × E n) :
    fderiv ℝ 𝓗 z v = ⟪hamGradX 𝓗 z, v.1⟫ + ⟪hamGradξ 𝓗 z, v.2⟫ := by
  rw [inner_hamGradX, inner_hamGradξ, ← map_add]
  simp

theorem contDiff_hamGradX (h : ContDiff ℝ ∞ 𝓗) : ContDiff ℝ ∞ (hamGradX 𝓗) :=
  vecOfL.contDiff.comp ((h.fderiv_right (m := ∞) le_rfl).clm_comp contDiff_const)

theorem contDiff_hamGradξ (h : ContDiff ℝ ∞ 𝓗) : ContDiff ℝ ∞ (hamGradξ 𝓗) :=
  vecOfL.contDiff.comp ((h.fderiv_right (m := ∞) le_rfl).clm_comp contDiff_const)

theorem contDiff_hamField (h : ContDiff ℝ ∞ 𝓗) : ContDiff ℝ ∞ (hamField 𝓗) :=
  (contDiff_hamGradξ h).prodMk (contDiff_hamGradX h).neg

/-- `𝓗` is constant along the integral curves of its Hamiltonian field. -/
theorem fderiv_hamField_eq_zero (z : E n × E n) : fderiv ℝ 𝓗 z (hamField 𝓗 z) = 0 := by
  rw [fderiv_apply_eq_inner]
  simp [hamField, inner_neg_right, real_inner_comm]

variable {Γ : ℝ × E n → E n × E n} {D : Set (ℝ × E n)}

/-- **Conservation of `𝓗`** along a family of integral curves `r ↦ Γ(r, y)` of `hamField 𝓗`. -/
theorem fderiv_comp_hamFlow_eq_zero (h : ContDiff ℝ ∞ 𝓗) (hD : IsOpen D)
    (hΓ : ContDiffOn ℝ ∞ Γ D) (hflow : ∀ p ∈ D, fderiv ℝ Γ p (1, 0) = hamField 𝓗 (Γ p))
    {p : ℝ × E n} (hp : p ∈ D) : fderiv ℝ (𝓗 ∘ Γ) p (1, 0) = 0 := by
  have hΓd : DifferentiableAt ℝ Γ p :=
    (hΓ.contDiffAt (hD.mem_nhds hp)).differentiableAt (by simp)
  rw [fderiv_comp p (h.differentiable (by simp) _) hΓd, ContinuousLinearMap.comp_apply,
    hflow p hp, fderiv_hamField_eq_zero]

/-- **The characteristic identity**: if `𝓗` satisfies Euler's identity `⟪ξ, ∂_ξ 𝓗⟫ = 2 𝓗`
(quadratic in `ξ`), then along a family `Γ(r, y) = (x, ξ)` of integral curves of
`hamField 𝓗`, `∂_r ⟪ξ, ∂_w x⟫ = ∂_w (𝓗 ∘ Γ)`. -/
theorem fderiv_inner_hamFlow (h : ContDiff ℝ ∞ 𝓗)
    (heuler : ∀ z : E n × E n, ⟪z.2, hamGradξ 𝓗 z⟫ = 2 * 𝓗 z) (hD : IsOpen D)
    (hΓ : ContDiffOn ℝ ∞ Γ D) (hflow : ∀ p ∈ D, fderiv ℝ Γ p (1, 0) = hamField 𝓗 (Γ p))
    {p : ℝ × E n} (hp : p ∈ D) (w : E n) :
    fderiv ℝ (fun q => ⟪(Γ q).2, (fderiv ℝ Γ q (0, w)).1⟫) p (1, 0) =
      fderiv ℝ (𝓗 ∘ Γ) p (0, w) := by
  have hΓa : ContDiffAt ℝ ∞ Γ p := hΓ.contDiffAt (hD.mem_nhds hp)
  have hΓd : DifferentiableAt ℝ Γ p := hΓa.differentiableAt (by simp)
  have hdΓ : ContDiffOn ℝ ∞ (fderiv ℝ Γ) D := hΓ.fderiv_of_isOpen hD le_rfl
  have hdΓd : DifferentiableAt ℝ (fderiv ℝ Γ) p :=
    (hdΓ.contDiffAt (hD.mem_nhds hp)).differentiableAt (by simp)
  have hsymm := hΓa.isSymmSndFDerivAt (n := ∞) (by simp)
  set z := Γ p
  set V := fderiv ℝ Γ p (0, w)
  -- derivative of `q ↦ ∂_w Γ(q)` in the direction `∂_r`
  have hV : fderiv ℝ (fun q => fderiv ℝ Γ q (0, w)) p (1, 0) = fderiv ℝ (hamField 𝓗) z V := by
    rw [fderiv_clm_apply hdΓd (differentiableAt_const _), fderiv_const_apply]
    simp only [ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply]
    rw [hsymm]
    have hev : (fun q => fderiv ℝ Γ q (1, 0)) =ᶠ[𝓝 p] hamField 𝓗 ∘ Γ :=
      eventually_of_mem (hD.mem_nhds hp) hflow
    have := hev.fderiv_eq (𝕜 := ℝ)
    rw [fderiv_clm_apply hdΓd (differentiableAt_const _), fderiv_const_apply] at this
    simp only [ContinuousLinearMap.comp_zero, zero_add] at this
    have h2 := congrArg (fun L => L (0, w)) this
    simp only [ContinuousLinearMap.flip_apply] at h2
    rw [h2, fderiv_comp p ((contDiff_hamField h).differentiable (by simp) _) hΓd]
    rfl
  have hξd : DifferentiableAt ℝ (hamGradξ 𝓗) z :=
    (contDiff_hamGradξ h).differentiable (by simp) _
  -- Euler's identity, differentiated
  have he : ⟪V.2, hamGradξ 𝓗 z⟫ + ⟪z.2, fderiv ℝ (hamGradξ 𝓗) z V⟫ = 2 * fderiv ℝ 𝓗 z V := by
    have hfun : (fun z : E n × E n => ⟪z.2, hamGradξ 𝓗 z⟫) = fun z => 2 * 𝓗 z := funext heuler
    have := congrArg (fun F => fderiv ℝ F z V) hfun
    rw [fderiv_inner_apply ℝ differentiableAt_snd hξd, fderiv_snd, fderiv_const_mul
      (h.differentiable (by simp) _)] at this
    simpa [real_inner_comm, add_comm] using this
  have hcd : DifferentiableAt ℝ (fun q => fderiv ℝ Γ q (0, w)) p :=
    hdΓd.clm_apply (differentiableAt_const _)
  have ha : HasFDerivAt (fun q => (Γ q).2) ((ContinuousLinearMap.snd ℝ _ _).comp
      (fderiv ℝ Γ p)) p := hΓd.hasFDerivAt.snd
  have hb : HasFDerivAt (fun q => (fderiv ℝ Γ q (0, w)).1) ((ContinuousLinearMap.fst ℝ _ _).comp
      (fderiv ℝ (fun q => fderiv ℝ Γ q (0, w)) p)) p := hcd.hasFDerivAt.fst
  rw [fderiv_inner_apply ℝ ha.differentiableAt hb.differentiableAt, ha.fderiv, hb.fderiv,
    fderiv_comp p (h.differentiable (by simp) _) hΓd]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd']
  rw [hV, hflow p hp]
  have hfst : (fderiv ℝ (hamField 𝓗) z V).1 = fderiv ℝ (hamGradξ 𝓗) z V := by
    have : hamField 𝓗 = fun z => (hamGradξ 𝓗 z, (-hamGradX 𝓗) z) := rfl
    have hX := ((contDiff_hamGradX h).differentiable (by simp) z).hasFDerivAt.neg
    rw [this, (hξd.hasFDerivAt.prodMk hX).fderiv]
    rfl
  rw [hfst, fderiv_apply_eq_inner z V]
  simp only [hamField, inner_neg_left]
  rw [fderiv_apply_eq_inner z V] at he
  rw [real_inner_comm (hamGradξ 𝓗 z) V.2] at he
  linarith

end Hamilton

/-! ### The Hamiltonian of a metric -/

section Metric

open WithLp

variable {g : MatrixField n} {Y : E n → E n}

lemma inner_eq_dotProduct (a v : E n) : ⟪a, v⟫ = ofLp a ⬝ᵥ ofLp v := by
  simp [PiLp.inner_apply, dotProduct, mul_comm]

lemma fderiv_apply_eq_deriv_line {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : F → ℝ} {z : F} (hf : DifferentiableAt ℝ f z) (u : F) :
    fderiv ℝ f z u = deriv (fun t : ℝ => f (z + t • u)) 0 := by
  have hl : HasDerivAt (fun t : ℝ => z + t • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add z
  exact ((hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 hl (by simp)).deriv).symm

variable (g) in
/-- The Hamiltonian `𝓗(x, ξ) = ½ g^{-1}_x(ξ, ξ)` of the geodesic flow, on covectors. -/
def hamG (z : E n × E n) : ℝ :=
  (1 / 2) * coform g z.1 (ofLp z.2) (ofLp z.2)

theorem hamG_def (z : E n × E n) :
    hamG g z =
      (1 / 2) * coform g z.1 (ofLp z.2) (ofLp z.2) := by rfl

variable (g) in
/-- The vector `g^{-1} ξ` of the covector `ξ`. -/
def raise (x ξ : E n) : E n :=
  toLp 2 ((g x)⁻¹ *ᵥ ofLp ξ)

theorem contDiff_hamG (hg : IsSpacetime g Y) : ContDiff ℝ ∞ (hamG g) := by
  show ContDiff ℝ ∞ fun z => hamG g z
  have hc : ∀ i, ContDiff ℝ ∞ fun z : E n × E n => z.2 i := fun i => by fun_prop
  simp only [hamG_def, coform_def]
  refine contDiff_const.mul (ContDiff.sum fun j _ => ContDiff.sum fun k _ => ?_)
  exact (((contDiff_inv_apply hg.smooth hg.det_ne_zero j k).comp contDiff_fst).mul (hc j)).mul
    (hc k)

theorem inner_raise (hg : IsSpacetime g Y) (x ξ v : E n) :
    ⟪raise g x ξ, v⟫ = coform g x (ofLp ξ) (ofLp v) := by
  rw [inner_eq_dotProduct, coform_eq_bil, bil_symm (hg.lorentzian x).inv_symm, bil_apply,
    dotProduct_comm]
  rfl

theorem hamGradξ_hamG (hg : IsSpacetime g Y) (z : E n × E n) :
    hamGradξ (hamG g) z = raise g z.1 z.2 := by
  refine ext_inner_right ℝ fun v => ?_
  rw [inner_hamGradξ, inner_raise hg,
    fderiv_apply_eq_deriv_line ((contDiff_hamG hg).differentiable (by simp) z)]
  have hsymm := bil_symm (hg.lorentzian z.1).inv_symm
  have hfun : (fun t : ℝ => hamG g (z + t • ((0 : E n), v))) = fun t =>
      (1 / 2) * coform g z.1 (ofLp z.2) (ofLp z.2) + t * coform g z.1 (ofLp z.2) (ofLp v) +
        t ^ 2 * ((1 / 2) * coform g z.1 (ofLp v) (ofLp v)) := by
    funext t
    simp only [hamG, coform_eq_bil, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_zero, add_zero, ofLp_add, ofLp_smul, map_add, map_smul, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul]
    rw [hsymm (ofLp v) (ofLp z.2)]
    ring
  rw [hfun]
  have hd : HasDerivAt (fun t : ℝ =>
      (1 / 2) * coform g z.1 (ofLp z.2) (ofLp z.2) + t * coform g z.1 (ofLp z.2) (ofLp v) +
        t ^ 2 * ((1 / 2) * coform g z.1 (ofLp v) (ofLp v))) (coform g z.1 (ofLp z.2) (ofLp v))
      0 := by
    have := (((hasDerivAt_id (0 : ℝ)).mul_const (coform g z.1 (ofLp z.2) (ofLp v))).const_add
      ((1 / 2) * coform g z.1 (ofLp z.2) (ofLp z.2))).add
      ((hasDerivAt_pow 2 (0 : ℝ)).mul_const ((1 / 2) * coform g z.1 (ofLp v) (ofLp v)))
    convert this using 1
    · rfl
    · norm_num
  exact hd.deriv

/-- Euler's identity `⟪ξ, ∂_ξ 𝓗⟫ = 2 𝓗` for the Hamiltonian of a metric. -/
theorem inner_hamGradξ_hamG (hg : IsSpacetime g Y) (z : E n × E n) :
    ⟪z.2, hamGradξ (hamG g) z⟫ = 2 * hamG g z := by
  rw [real_inner_comm, hamGradξ_hamG hg, inner_raise hg, hamG]
  ring

theorem raise_d (x : E n) (φ : E n → ℝ) : raise g x (toLp 2 (d φ x)) = grad g φ x := by
  ext j
  simp [raise, grad_def, Matrix.mulVec, dotProduct]

end Metric

/-! ### Flows of smooth vector fields -/

section Flow

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The flow `(t, z) ↦ Fl(t, z)` of a smooth vector field `F`, on its open domain `𝒟`: smooth,
`Fl(0, z) = z`, `∂_t Fl = F ∘ Fl`, the domain is star-shaped in `t` around `0`, and every
integral curve through `z` at time `0` is `Fl(·, z)`. -/
theorem exists_flow {U : Set V} (hU : IsOpen U) {F : V → V} (hF : ContDiffOn ℝ ∞ F U) :
    ∃ (𝒟 : Set (ℝ × V)) (Fl : ℝ × V → V), IsOpen 𝒟 ∧ ContDiffOn ℝ ∞ Fl 𝒟 ∧
      (∀ p ∈ 𝒟, Fl p ∈ U) ∧ (∀ z ∈ U, (0, z) ∈ 𝒟 ∧ Fl (0, z) = z) ∧
      (∀ p ∈ 𝒟, HasDerivAt (fun s => Fl (s, p.2)) (F (Fl p)) p.1) ∧
      (∀ p ∈ 𝒟, ∀ s ∈ uIcc 0 p.1, (s, p.2) ∈ 𝒟) ∧
      ∀ (c : ℝ → V) (I : Set ℝ), I.OrdConnected → (0 : ℝ) ∈ I → (∀ s ∈ I, c s ∈ U) →
        (∀ s ∈ I, HasDerivWithinAt c (F (c s)) I s) → ∀ t ∈ I, (t, c 0) ∈ 𝒟 ∧ Fl (t, c 0) = c t := by
  obtain ⟨X, hD', hX', hrep'⟩ := Facts.ode_smooth_dependence (P := ℝ) hU hF
  set dom := { q : ℝ × ℝ × V × ℝ | q.2.2.2 ∈ (univ : Set ℝ) ∧ ∃ (x : ℝ → V) (I : Set ℝ),
    Facts.IsODESolution (fun (_ : ℝ) (y : V) (_ : ℝ) => F y) U q.2.2.2 x I ∧ q.1 ∈ I ∧
      q.2.1 ∈ I ∧ x q.2.1 = q.2.2.1 } with hdom
  have hdomeq : dom = { q : ℝ × ℝ × V × ℝ | ∃ (x : ℝ → V) (I : Set ℝ),
      Facts.IsODESolution (fun (_ : ℝ) (y : V) (_ : ℝ) => F y) U q.2.2.2 x I ∧ q.1 ∈ I ∧
        q.2.1 ∈ I ∧ x q.2.1 = q.2.2.1 } := by
    ext q
    simp [dom]
  have hD : IsOpen dom := hdomeq ▸ hD'
  have hX : ContDiffOn ℝ ∞ X dom := hdomeq ▸ hX'
  have hrep : ∀ (p : ℝ) (x : ℝ → V) (I : Set ℝ), p ∈ (univ : Set ℝ) →
      Facts.IsODESolution (fun (_ : ℝ) (y : V) (_ : ℝ) => F y) U p x I → ∀ t₀ ∈ I, ∀ t ∈ I,
        X (t, t₀, x t₀, p) = x t := fun p x I _ => hrep' p x I
  have hι : Continuous fun p : ℝ × V => (p.1, (0 : ℝ), p.2, (0 : ℝ)) := by fun_prop
  set 𝒟 := (fun p : ℝ × V => (p.1, (0 : ℝ), p.2, (0 : ℝ))) ⁻¹' dom
  have h𝒟 : IsOpen 𝒟 := hD.preimage hι
  have hsm : ContDiffOn ℝ ∞ (fun p : ℝ × V => X (p.1, 0, p.2, 0)) 𝒟 :=
    hX.comp (by fun_prop : ContDiff ℝ ∞ fun p : ℝ × V => (p.1, (0 : ℝ), p.2, (0 : ℝ))).contDiffOn
      fun p hp => hp
  have hsol : ∀ (c : ℝ → V) (I : Set ℝ), I.OrdConnected → (0 : ℝ) ∈ I → (∀ s ∈ I, c s ∈ U) →
      (∀ s ∈ I, HasDerivWithinAt c (F (c s)) I s) → ∀ t ∈ I,
        (t, c 0) ∈ 𝒟 ∧ X (t, 0, c 0, 0) = c t := fun c I hI h0 hcU hc t ht =>
    ⟨⟨mem_univ _, c, I, ⟨hI, hcU, hc⟩, ht, h0, rfl⟩,
      hrep 0 c I (mem_univ _) ⟨hI, hcU, hc⟩ 0 h0 t ht⟩
  have h0 : ∀ z ∈ U, ((0 : ℝ), z) ∈ 𝒟 ∧ X (0, 0, z, 0) = z := fun z hz => by
    have := hsol (fun _ => z) {0} ordConnected_singleton rfl (fun _ _ => hz) (fun s hs => by
      rw [mem_singleton_iff.1 hs]
      exact HasFDerivWithinAt.of_not_accPt (by
        rw [accPt_iff_clusterPt, inf_principal]; simp [ClusterPt])) 0 rfl
    exact this
  -- from a point of the domain, a solution through it reaching beyond it
  have hseg : ∀ p ∈ 𝒟, ∀ t' : ℝ, (t', p.2) ∈ 𝒟 → ∀ s ∈ uIcc 0 t',
      (s, p.2) ∈ 𝒟 ∧ HasDerivWithinAt (fun s => X (s, 0, p.2, 0))
        (F (X (s, 0, p.2, 0))) (uIcc 0 t') s := by
    rintro p - t' ⟨-, x, I, hx, ht'I, h0I, hx0⟩ s hs
    simp only at ht'I h0I hx0
    have hsub : uIcc 0 t' ⊆ I := hx.interval.uIcc_subset h0I ht'I
    have heq : ∀ u ∈ I, X (u, 0, p.2, 0) = x u := fun u hu => by
      simpa [hx0] using hrep 0 x I (mem_univ _) hx 0 h0I u hu
    refine ⟨⟨mem_univ _, x, I, hx, hsub hs, h0I, hx0⟩, ?_⟩
    have := ((hx.deriv s (hsub hs)).mono hsub).congr (fun u hu => heq u (hsub hu)) (heq s (hsub hs))
    rwa [← heq s (hsub hs)] at this
  have hmapsU : ∀ p ∈ 𝒟, X (p.1, 0, p.2, 0) ∈ U := by
    rintro p ⟨-, x, I, hx, h1, h0I, hx0⟩
    simp only at h1 h0I hx0
    rw [← hx0, hrep 0 x I (mem_univ _) hx 0 h0I p.1 h1]
    exact hx.mem _ h1
  refine ⟨𝒟, fun p => X (p.1, 0, p.2, 0), h𝒟, hsm, hmapsU, h0, fun p hp => ?_,
    fun p hp s hs => ?_, fun c I hI h0I hcU hc t ht => hsol c I hI h0I hcU hc t ht⟩
  · obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 h𝒟 p hp
    set t' := if 0 ≤ p.1 then p.1 + ε / 2 else p.1 - ε / 2
    have ht'D : (t', p.2) ∈ 𝒟 := hball (by
      rw [Metric.mem_ball, Prod.dist_eq, dist_self, Real.dist_eq]
      simp only [t']
      split_ifs <;> simp [abs_of_pos (half_pos hε), hε, max_lt_iff, half_lt_self hε])
    have ht0 : t' ≠ 0 := by simp only [t']; split_ifs with h <;> intro h' <;> linarith
    have hmem : p.1 ∈ uIcc 0 t' := by
      rw [mem_uIcc]
      simp only [t']
      split_ifs with h
      · left; constructor <;> linarith
      · right; constructor <;> linarith
    have hdiff : DifferentiableAt ℝ (fun s => X (s, 0, p.2, 0)) p.1 := by
      have : (fun s => X (s, 0, p.2, 0)) = (fun q : ℝ × V => X (q.1, 0, q.2, 0)) ∘
        fun s => (s, p.2) := rfl
      rw [this]
      exact ((hsm.contDiffAt (h𝒟.mem_nhds hp)).differentiableAt (by simp)).comp _
        (by fun_prop)
    exact hasDerivAt_of_hasDerivWithinAt_uIcc ht0.symm hmem hdiff (hseg p hp t' ht'D _ hmem).2
  · rcases eq_or_ne p.1 0 with h | h
    · rw [h, uIcc_self, mem_singleton_iff] at hs
      have hpU : p.2 ∈ U := by
        obtain ⟨-, x, I, hx, -, h0I, hx0⟩ := hp
        simp only at h0I hx0
        rw [← hx0]
        exact hx.mem 0 h0I
      rw [hs]; exact (h0 _ hpU).1
    · exact (hseg p hp p.1 hp s hs).1

end Flow

/-! ### Calculus helpers -/

section Helpers

lemma eq_of_hasDerivAt_zero_uIcc {f : ℝ → ℝ} {t : ℝ} (h : ∀ s ∈ uIcc 0 t, HasDerivAt f 0 s) :
    f t = f 0 := by
  have hc : ContinuousOn f (uIcc 0 t) := fun s hs => (h s hs).continuousAt.continuousWithinAt
  have key := constant_of_has_deriv_right_zero (a := min 0 t) (b := max 0 t) hc
    (fun s hs => (h s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
  rw [key t ⟨min_le_right _ _, le_max_right _ _⟩, key 0 ⟨min_le_left _ _, le_max_left _ _⟩]

lemma fderiv_apply_one_zero {W V : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {f : ℝ × V → W} {p : ℝ × V}
    (hf : DifferentiableAt ℝ f p) {w : W} (h : HasDerivAt (fun s => f (s, p.2)) w p.1) :
    fderiv ℝ f p (1, 0) = w := by
  have hl : HasDerivAt (fun s : ℝ => (s, p.2)) ((1 : ℝ), (0 : V)) p.1 :=
    (hasDerivAt_id _).prodMk (hasDerivAt_const _ _)
  exact (hf.hasFDerivAt.comp_hasDerivAt_of_eq p.1 hl (by simp)).unique h

lemma fderiv_apply_zero_left {W V : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {f : ℝ × V → W} {p : ℝ × V}
    (hf : DifferentiableAt ℝ f p) (v : V) :
    fderiv ℝ f p (0, v) = fderiv ℝ (fun y => f (p.1, y)) p.2 v := by
  obtain ⟨a, b⟩ := p
  have hl : HasFDerivAt (fun y : V => (a, y)) ((0 : V →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ V))
      b := (hasFDerivAt_const _ _).prodMk (hasFDerivAt_id _)
  have := (hf.hasFDerivAt.comp b hl).fderiv
  change fderiv ℝ (fun y => f (a, y)) b = _ at this
  simp only
  rw [this]
  simp

/-- Inverse function theorem at a point where the differential is the identity. -/
theorem exists_localInverse_of_fderiv_eq_id {Ψ : E n → E n} {U : Set (E n)} (hU : IsOpen U)
    (hΨ : ContDiffOn ℝ ∞ Ψ U) {z : E n} (hz : z ∈ U)
    (hid : fderiv ℝ Ψ z = ContinuousLinearMap.id ℝ (E n)) :
    ∃ φ : OpenPartialHomeomorph (E n) (E n), ⇑φ = Ψ ∧ z ∈ φ.source ∧ φ.source ⊆ U ∧
      ContDiffOn ℝ ∞ φ.symm φ.target ∧
      ∀ y ∈ φ.target, ∀ v, fderiv ℝ Ψ (φ.symm y) (fderiv ℝ φ.symm y v) = v := by
  set U' := U ∩ (fun x => fderiv ℝ Ψ x) ⁻¹' Metric.ball (ContinuousLinearMap.id ℝ (E n)) 1
  have hU' : IsOpen U' := (hΨ.continuousOn_fderiv_of_isOpen hU (by simp)).isOpen_inter_preimage
    hU Metric.isOpen_ball
  have hinj : ∀ x ∈ U', Function.Injective (fderiv ℝ Ψ x) := by
    intro x hx
    refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
    have hlt : ‖fderiv ℝ Ψ x - ContinuousLinearMap.id ℝ (E n)‖ < 1 := by
      simpa [dist_eq_norm] using hx.2
    by_contra hv0
    have hle := (fderiv ℝ Ψ x - ContinuousLinearMap.id ℝ (E n)).le_opNorm v
    simp only [sub_apply, hv, ContinuousLinearMap.id_apply, zero_sub,
      norm_neg] at hle
    have hpos : 0 < ‖v‖ := norm_pos_iff.2 hv0
    nlinarith
  obtain ⟨φ, h1, h2, h3, h4, h5⟩ := exists_localInverse hU' (hΨ.mono inter_subset_left) hinj
    ⟨hz, by simp [hid]⟩
  exact ⟨φ, h1, h2, h3.trans inter_subset_left, h4, h5⟩

end Helpers

end

end LorentzianCalderon
