module

public import LorentzianCalderon.Geometry.WorldFunctionDeriv

public section

/-!
# Symmetry of conjugate points

The reversal `Ψ(y, w) = (exp_y w, -d(exp_y)_w w)` is an involution of the domain of the
exponential map, and `𝐞 ∘ Ψ = swap ∘ 𝐞` for `𝐞(y, w) = (y, exp_y w)`. Since `𝐞` has invertible
derivative exactly where `exp_y` does, `exp_y` is singular at `w` if and only if `exp_{exp_y w}` is
singular at `-d(exp_y)_w w`.
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Set Filter

variable {n : ℕ} {g : MatrixField n} {Y : E n → E n}

/-- The reversal `(y, w) ↦ (exp_y w, -d(exp_y)_w w)` of geodesic segments. -/
def expReverse (g : MatrixField n) (z : E n × E n) : E n × E n :=
  (expMap g z.1 z.2, -fderiv ℝ (expMap g z.1) z.2 z.2)

theorem contDiffOn_expReverse (hg : IsSpacetime g Y) :
    ContDiffOn ℝ ∞ (expReverse g) { z : E n × E n | InExpDomain g z.1 z.2 } := by
  have hL : ContDiffOn ℝ ∞ (fun z => fderiv ℝ (fun q : E n × E n => expMap g q.1 q.2) z)
      { z : E n × E n | InExpDomain g z.1 z.2 } :=
    (contDiffOn_expMap hg).fderiv_of_isOpen (isOpen_expDomain hg) (by simp)
  refine (contDiffOn_expMap hg).prodMk (ContDiffOn.neg ?_)
  have : ContDiffOn ℝ ∞ (fun z : E n × E n =>
      (fderiv ℝ (fun q : E n × E n => expMap g q.1 q.2) z) ((0 : E n), z.2))
      { z : E n × E n | InExpDomain g z.1 z.2 } :=
    hL.clm_apply (contDiffOn_const.prodMk contDiffOn_snd)
  refine this.congr fun z hz => ?_
  rw [(hasFDerivAt_expMap hg (p := z) hz).fderiv]
  rfl

theorem expReverse_spec (hg : IsSpacetime g Y) {z : E n × E n} (hz : InExpDomain g z.1 z.2) :
    InExpDomain g (expReverse g z).1 (expReverse g z).2 ∧
      expReverse g (expReverse g z) = z ∧
      expPair g (expReverse g z) = (expPair g z).swap := by
  obtain ⟨h1, h2, h3, -⟩ := hz.reverse hg
  refine ⟨h1, ?_, ?_⟩
  · simp only [expReverse]
    rw [h2, h3, neg_neg]
  · simp only [expPair_def, expReverse, Prod.swap_prod_mk]
    rw [h2]

/-- Symmetry of conjugate points: if `exp_y` is singular at `w`, then `exp_p`, `p = exp_y w`, is
singular at the initial velocity `-ċ(1)` of the reversed geodesic, `c(r) = exp_y (r w)`. -/
theorem IsConjugateAt.reverse (hg : IsSpacetime g Y) {y w : E n} (hdom : InExpDomain g y w)
    (h : IsConjugateAt g y w) :
    IsConjugateAt g (expMap g y w) (-(fderiv ℝ (expMap g y) w w)) := by
  set D := { z : E n × E n | InExpDomain g z.1 z.2 }
  have hD : IsOpen D := isOpen_expDomain hg
  set z : E n × E n := (y, w)
  have hz : z ∈ D := hdom
  obtain ⟨hΨz, -, -⟩ := expReverse_spec hg hz
  refine isConjugateAt_iff.2 fun hbij => ?_
  obtain ⟨A, hA⟩ := exists_hasFDerivAt_expPair hg (p := expReverse g z) hΨz hbij
  have hΨdiff : ∀ x ∈ D, HasFDerivAt (expReverse g) (fderiv ℝ (expReverse g) x) x := fun x hx =>
    (((contDiffOn_expReverse hg).differentiableOn (by simp)).differentiableAt
      (hD.mem_nhds hx)).hasFDerivAt
  set P := fderiv ℝ (expReverse g) z
  have hP : HasFDerivAt (expReverse g) P z := hΨdiff z hz
  have hPP : HasFDerivAt (expReverse g ∘ expReverse g)
      ((fderiv ℝ (expReverse g) (expReverse g z)).comp P) z :=
    (hΨdiff _ hΨz).comp z hP
  have hid : (fderiv ℝ (expReverse g) (expReverse g z)).comp P = ContinuousLinearMap.id ℝ _ := by
    refine hPP.unique ((hasFDerivAt_id z).congr_of_eventuallyEq ?_)
    exact eventually_of_mem (hD.mem_nhds hz) fun x hx => (expReverse_spec hg hx).2.1
  have hPinj : Function.Injective P := by
    intro a b hab
    have := congrArg (fderiv ℝ (expReverse g) (expReverse g z)) hab
    rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply, hid] at this
    exact this
  set Pe : (E n × E n) ≃L[ℝ] (E n × E n) :=
    (LinearEquiv.ofInjectiveEndo (P : (E n × E n) →ₗ[ℝ] (E n × E n)) hPinj).toContinuousLinearEquiv
  have hPe : (Pe : (E n × E n) →L[ℝ] (E n × E n)) = P := ContinuousLinearMap.ext fun _ => rfl
  have hE : HasFDerivAt (expPair g) (fderiv ℝ (expPair g) z) z :=
    (((contDiffOn_expPair hg).differentiableOn (by simp)).differentiableAt
      (hD.mem_nhds hz)).hasFDerivAt
  set S := ContinuousLinearEquiv.prodComm ℝ (E n) (E n)
  have h₁ : HasFDerivAt (expPair g ∘ expReverse g) ((A : (E n × E n) →L[ℝ] (E n × E n)).comp P)
      z := hA.comp z hP
  have h₂ : HasFDerivAt (fun x => S (expPair g x))
      ((S : (E n × E n) →L[ℝ] (E n × E n)).comp (fderiv ℝ (expPair g) z)) z :=
    S.hasFDerivAt.comp z hE
  have heq : (S : (E n × E n) →L[ℝ] (E n × E n)).comp (fderiv ℝ (expPair g) z) =
      (A : (E n × E n) →L[ℝ] (E n × E n)).comp P := by
    refine h₂.unique (h₁.congr_of_eventuallyEq ?_)
    exact eventually_of_mem (hD.mem_nhds hz) fun x hx => by
      simp only [Function.comp_apply, (expReverse_spec hg hx).2.2]
      rfl
  set e : (E n × E n) ≃L[ℝ] (E n × E n) := (Pe.trans A).trans S.symm
  have he : HasFDerivAt (expPair g) (e : (E n × E n) →L[ℝ] (E n × E n)) z := by
    convert hE using 1
    refine ContinuousLinearMap.ext fun v => ?_
    have := congrArg (fun L : (E n × E n) →L[ℝ] (E n × E n) => S.symm (L v)) heq
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply] at this
    rw [this]
    simp only [e, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.trans_apply]
    rw [← hPe]
    rfl
  exact (isConjugateAt_iff.1 h) (bijective_fderiv_expMap hg hdom he)

end

end LorentzianCalderon
