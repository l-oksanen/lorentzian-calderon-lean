module

public import LorentzianCalderon.PDE.Periodic
public import LorentzianCalderon.ODE.Linear

public section

/-!
# Galerkin solutions of the periodic core

The Galerkin approximation of order `N` of `∂ₜ²V = A V + F`: an unknown
`V(l, t, ·)` in the trigonometric polynomials `trigPoly ι n N` of degree `N`, solving
`∂ₜ²V = Π_N (A V + F)`, where `Π_N` is the `L²(cell)`-orthogonal projection onto `trigPoly ι n N`.

`trigPoly ι n N` is finite-dimensional; in a basis `b` of it (`trigBasis`) the projection is
`Π_N u = ∑ⱼ (G⁻¹ ĉ(u))ⱼ bⱼ`, where `ĉ(u)ᵢ = ∫_cell ⟪u, bᵢ⟫` (`trigCoeffs`) and `G` is the Gram
matrix of `b`, invertible since `∫_cell |w|² > 0` for a nonzero periodic continuous `w`
(`galerkinProj`). It is characterized by `galerkinProj_mem`, `cellIntegral_inner_sub_galerkinProj`
and `eq_galerkinProj`. The Galerkin system is a linear equation for the coefficients of `V` and
`∂ₜV` in the basis, solved for all times by `ODEFlow.exists_linear_ode` (`exists_galerkin`).
-/

namespace LorentzianCalderon.PDE

noncomputable section
open scoped ContDiff RealInnerProductSpace Topology
open Set MeasureTheory Function Real

variable {n p : ℕ} {ι : Type*} [Fintype ι]

/-! ## A basis of the trigonometric polynomials -/

instance (N : ℕ) : FiniteDimensional ℝ (trigPoly ι n N) := by
  classical
  set g : (Fin n → Icc (-(N : ℤ)) N) × ι × Bool → (Fin n → ℝ) → EuclideanSpace ℝ ι :=
    fun q y => (if q.2.2 then Real.cos (phase (fun i => (q.1 i : ℤ)) y)
      else Real.sin (phase (fun i => (q.1 i : ℤ)) y)) • EuclideanSpace.single q.2.1 1
  have hle : trigPoly ι n N ≤ Submodule.span ℝ (range g) := by
    rw [trigPoly_def]
    refine Submodule.span_le.2 ?_
    rintro f ⟨k, hk, v, hf⟩
    set k' : Fin n → Icc (-(N : ℤ)) N := fun i => ⟨k i, abs_le.1 (hk i)⟩
    have hdec : ∀ b : Bool, (fun y => (if b then Real.cos (phase k y) else Real.sin (phase k y))
        • v) = ∑ j, v j • g (k', j, b) := fun b => by
      ext y m
      cases b <;> simp [g, k'] <;>
        rw [Finset.sum_eq_single m (fun x _ hx => by simp [hx.symm]) (by simp)] <;> simp [mul_comm]
    have hmem : ∀ b : Bool, ∑ j, v j • g (k', j, b) ∈ Submodule.span ℝ (range g) := fun b =>
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    rcases hf with rfl | rfl
    · simpa using hdec true ▸ hmem true
    · simpa using hdec false ▸ hmem false
  have := FiniteDimensional.span_of_finite ℝ (Set.finite_range g)
  exact Submodule.finiteDimensional_of_le hle

/-- The dimension of `trigPoly ι n N`. -/
abbrev trigDim (ι : Type*) [Fintype ι] (n N : ℕ) : ℕ := Module.finrank ℝ (trigPoly ι n N)

/-- A basis of `trigPoly ι n N`, as functions. -/
def trigBasis (ι : Type*) [Fintype ι] (n N : ℕ) (j : Fin (trigDim ι n N)) :
    (Fin n → ℝ) → EuclideanSpace ℝ ι :=
  (Module.finBasis ℝ (trigPoly ι n N) j : (Fin n → ℝ) → EuclideanSpace ℝ ι)

theorem trigBasis_mem (N : ℕ) (j : Fin (trigDim ι n N)) : trigBasis ι n N j ∈ trigPoly ι n N :=
  (Module.finBasis ℝ (trigPoly ι n N) j).2

theorem contDiff_trigBasis (N : ℕ) (j : Fin (trigDim ι n N)) :
    ContDiff ℝ ∞ (trigBasis ι n N j) :=
  (contDiff_isPeriodic_of_mem_trigPoly (trigBasis_mem N j)).1

theorem isPeriodic_trigBasis (N : ℕ) (j : Fin (trigDim ι n N)) :
    IsPeriodic (trigBasis ι n N j) :=
  (contDiff_isPeriodic_of_mem_trigPoly (trigBasis_mem N j)).2

/-- The combination `∑ⱼ xⱼ bⱼ` of the basis. -/
def trigComb (N : ℕ) (x : Fin (trigDim ι n N) → ℝ) (y : Fin n → ℝ) : EuclideanSpace ℝ ι :=
  ∑ j, x j • trigBasis ι n N j y

theorem trigComb_eq (N : ℕ) (x : Fin (trigDim ι n N) → ℝ) :
    trigComb N x = ((∑ j, x j • Module.finBasis ℝ (trigPoly ι n N) j : trigPoly ι n N) :
      (Fin n → ℝ) → EuclideanSpace ℝ ι) := by
  ext1 y
  simp [trigComb, trigBasis, Finset.sum_apply]

theorem trigComb_mem (N : ℕ) (x : Fin (trigDim ι n N) → ℝ) : trigComb N x ∈ trigPoly ι n N := by
  rw [trigComb_eq]; exact Submodule.coe_mem _

theorem exists_trigComb_eq {N : ℕ} {w : (Fin n → ℝ) → EuclideanSpace ℝ ι}
    (hw : w ∈ trigPoly ι n N) : ∃ x, trigComb N x = w :=
  ⟨(Module.finBasis ℝ (trigPoly ι n N)).repr ⟨w, hw⟩, by
    rw [trigComb_eq, (Module.finBasis ℝ (trigPoly ι n N)).sum_repr]⟩

/-! ## Integrals of inner products over the cell -/

section Inner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem cellIntegral_inner_add_left {u v w : (Fin n → ℝ) → E} (hu : Continuous u)
    (hv : Continuous v) (hw : Continuous w) :
    cellIntegral (fun y => ⟪u y + v y, w y⟫) =
      cellIntegral (fun y => ⟪u y, w y⟫) + cellIntegral (fun y => ⟪v y, w y⟫) := by
  simp only [cellIntegral_def, inner_add_left]
  exact integral_add (integrableOn_cell (hu.inner hw)) (integrableOn_cell (hv.inner hw))

theorem cellIntegral_inner_sub_left {u v w : (Fin n → ℝ) → E} (hu : Continuous u)
    (hv : Continuous v) (hw : Continuous w) :
    cellIntegral (fun y => ⟪u y - v y, w y⟫) =
      cellIntegral (fun y => ⟪u y, w y⟫) - cellIntegral (fun y => ⟪v y, w y⟫) := by
  simp only [cellIntegral_def, inner_sub_left]
  exact integral_sub (integrableOn_cell (hu.inner hw)) (integrableOn_cell (hv.inner hw))

theorem cellIntegral_inner_sum_smul_left {m : ℕ} (c : Fin m → ℝ) {u : Fin m → (Fin n → ℝ) → E}
    {w : (Fin n → ℝ) → E} (hu : ∀ j, Continuous (u j)) (hw : Continuous w) :
    cellIntegral (fun y => ⟪∑ j, c j • u j y, w y⟫) =
      ∑ j, c j * cellIntegral (fun y => ⟪u j y, w y⟫) := by
  simp only [cellIntegral_def, sum_inner, real_inner_smul_left]
  rw [integral_finsetSum _ fun j _ => (integrableOn_cell
    ((hu j).inner hw)).integrable.const_mul (c j)]
  simp only [integral_const_mul]

theorem cellIntegral_inner_sum_smul_right {m : ℕ} (c : Fin m → ℝ) {u : Fin m → (Fin n → ℝ) → E}
    {w : (Fin n → ℝ) → E} (hu : ∀ j, Continuous (u j)) (hw : Continuous w) :
    cellIntegral (fun y => ⟪w y, ∑ j, c j • u j y⟫) =
      ∑ j, c j * cellIntegral (fun y => ⟪w y, u j y⟫) := by
  have hc : ∀ y a, ⟪w y, a⟫ = ⟪a, w y⟫ := fun y a => real_inner_comm _ _
  simp only [hc]
  exact cellIntegral_inner_sum_smul_left c hu hw

/-- A continuous periodic function with `∫_cell |f|² = 0` vanishes. -/
theorem eq_zero_of_cellIntegral_inner_self {f : (Fin n → ℝ) → E} (hf : Continuous f)
    (hp : IsPeriodic f) (h0 : cellIntegral (fun y => ⟪f y, f y⟫) = 0) : f = 0 := by
  set O : Set (Fin n → ℝ) := pi univ fun _ => Ioo 0 1
  have hO : ∀ y ∈ O, f y = 0 := by
    intro y₀ hy₀
    by_contra hne
    set g : (Fin n → ℝ) → ℝ := fun y => ⟪f y, f y⟫
    have hg : Continuous g := hf.inner hf
    have hpos : 0 < cellIntegral g := by
      rw [cellIntegral_def]
      refine (integral_pos_iff_support_of_nonneg (fun y => real_inner_self_nonneg)
        (integrableOn_cell hg)).2 ?_
      rw [Measure.restrict_apply' measurableSet_cell]
      have hU : IsOpen (support g ∩ O) :=
        (isOpen_ne_fun hg continuous_const).inter (isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo)
      refine lt_of_lt_of_le (hU.measure_pos volume ⟨y₀, ?_, hy₀⟩) (measure_mono ?_)
      · simpa [g] using hne
      · refine inter_subset_inter_right _ fun y hy => ?_
        exact mem_cell.2 ⟨fun i => (hy i (mem_univ i)).1.le, fun i => (hy i (mem_univ i)).2.le⟩
    exact hpos.ne' h0
  have hcell : ∀ y ∈ cell n, f y = 0 := by
    have hcl : closure O = cell n := by
      rw [closure_pi_set, cell_def, ← pi_univ_Icc]
      simp [closure_Ioo zero_ne_one]
    rw [← hcl]
    exact closure_minimal hO (isClosed_eq hf continuous_const)
  ext1 y
  rw [hp.apply_fract y, hcell _ (fract_mem_cell y)]
  rfl

end Inner

/-! ## The Galerkin projection -/

/-- The coefficients `∫_cell ⟪u, bᵢ⟫` of `u` against the basis of `trigPoly ι n N`. -/
def trigCoeffs (N : ℕ) (u : (Fin n → ℝ) → EuclideanSpace ℝ ι) : Fin (trigDim ι n N) → ℝ :=
  fun i => cellIntegral fun y => ⟪u y, trigBasis ι n N i y⟫

/-- The Gram matrix `Gᵢⱼ = ∫_cell ⟪bⱼ, bᵢ⟫` of the basis, so that
`trigCoeffs N (trigComb N x) = G x` (`trigCoeffs_trigComb`). -/
def trigGram (ι : Type*) [Fintype ι] (n N : ℕ) : Matrix (Fin (trigDim ι n N))
    (Fin (trigDim ι n N)) ℝ :=
  Matrix.of fun i j => cellIntegral fun y => ⟪trigBasis ι n N j y, trigBasis ι n N i y⟫

theorem continuous_trigComb (N : ℕ) (x : Fin (trigDim ι n N) → ℝ) : Continuous (trigComb N x) :=
  (contDiff_isPeriodic_of_mem_trigPoly (trigComb_mem N x)).1.continuous

theorem trigCoeffs_add (N : ℕ) {u v : (Fin n → ℝ) → EuclideanSpace ℝ ι} (hu : Continuous u)
    (hv : Continuous v) : trigCoeffs N (u + v) = trigCoeffs N u + trigCoeffs N v := by
  ext i
  exact cellIntegral_inner_add_left hu hv (contDiff_trigBasis N i).continuous

theorem trigCoeffs_sum_smul (N : ℕ) {m : ℕ} (c : Fin m → ℝ)
    {u : Fin m → (Fin n → ℝ) → EuclideanSpace ℝ ι} (hu : ∀ j, Continuous (u j)) :
    trigCoeffs N (fun y => ∑ j, c j • u j y) = ∑ j, c j • trigCoeffs N (u j) := by
  ext i
  simp only [trigCoeffs, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact cellIntegral_inner_sum_smul_left c hu (contDiff_trigBasis N i).continuous

theorem trigCoeffs_trigComb (N : ℕ) (x : Fin (trigDim ι n N) → ℝ) :
    trigCoeffs N (trigComb (ι := ι) (n := n) N x) = (trigGram ι n N).mulVec x := by
  unfold trigComb
  rw [trigCoeffs_sum_smul N x fun j => (contDiff_trigBasis N j).continuous]
  ext i
  simp [trigGram, Matrix.mulVec, dotProduct, trigCoeffs, mul_comm]

/-- `∫_cell ⟪u, w⟫ = 0` for every `w ∈ trigPoly ι n N` if it holds for the basis. -/
theorem cellIntegral_inner_eq_zero_of_trigCoeffs {N : ℕ} {u : (Fin n → ℝ) → EuclideanSpace ℝ ι}
    (hu : Continuous u) (h0 : trigCoeffs N u = 0) {w : (Fin n → ℝ) → EuclideanSpace ℝ ι}
    (hw : w ∈ trigPoly ι n N) : cellIntegral (fun y => ⟪u y, w y⟫) = 0 := by
  obtain ⟨x, rfl⟩ := exists_trigComb_eq hw
  unfold trigComb
  rw [cellIntegral_inner_sum_smul_right x
    (fun j => (contDiff_trigBasis N j).continuous) hu]
  exact Finset.sum_eq_zero fun j _ => by rw [show cellIntegral _ = trigCoeffs N u j from rfl,
    h0, Pi.zero_apply, mul_zero]

theorem injective_trigGram (N : ℕ) : Injective (trigGram ι n N).mulVecLin := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have h0 : trigCoeffs N (trigComb (ι := ι) N x) = 0 := by
    rw [trigCoeffs_trigComb]; exact hx
  have hz := eq_zero_of_cellIntegral_inner_self (continuous_trigComb N x)
    (contDiff_isPeriodic_of_mem_trigPoly (trigComb_mem N x)).2
    (cellIntegral_inner_eq_zero_of_trigCoeffs (continuous_trigComb N x) h0 (trigComb_mem N x))
  rw [trigComb_eq] at hz
  have hz' : ∑ j, x j • Module.finBasis ℝ (trigPoly ι n N) j = 0 :=
    Subtype.ext (by simpa using hz)
  funext j
  exact Fintype.linearIndependent_iff.1 (Module.finBasis ℝ (trigPoly ι n N)).linearIndependent
    x hz' j

/-- The inverse of the Gram matrix, as a linear map. -/
def trigGramInv (ι : Type*) [Fintype ι] (n N : ℕ) :
    (Fin (trigDim ι n N) → ℝ) →ₗ[ℝ] (Fin (trigDim ι n N) → ℝ) :=
  (LinearEquiv.ofInjectiveEndo _ (injective_trigGram (ι := ι) (n := n) N)).symm.toLinearMap

theorem trigGram_mulVec_trigGramInv (N : ℕ) (c : Fin (trigDim ι n N) → ℝ) :
    (trigGram ι n N).mulVec (trigGramInv ι n N c) = c :=
  (LinearEquiv.ofInjectiveEndo _ (injective_trigGram (ι := ι) (n := n) N)).apply_symm_apply c

/-- The Galerkin projection `Π_N`: the `L²(cell)`-orthogonal projection onto `trigPoly ι n N`,
characterized by `galerkinProj_mem`, `cellIntegral_inner_sub_galerkinProj` and
`eq_galerkinProj`. -/
def galerkinProj (N : ℕ) (u : (Fin n → ℝ) → EuclideanSpace ℝ ι) :
    (Fin n → ℝ) → EuclideanSpace ℝ ι :=
  trigComb N (trigGramInv ι n N (trigCoeffs N u))

theorem galerkinProj_mem (N : ℕ) (u : (Fin n → ℝ) → EuclideanSpace ℝ ι) :
    galerkinProj N u ∈ trigPoly ι n N :=
  trigComb_mem N _

theorem trigCoeffs_galerkinProj (N : ℕ) (u : (Fin n → ℝ) → EuclideanSpace ℝ ι) :
    trigCoeffs N (galerkinProj N u) = trigCoeffs N u := by
  rw [galerkinProj, trigCoeffs_trigComb, trigGram_mulVec_trigGramInv]

/-- `u - Π_N u` is `L²(cell)`-orthogonal to `trigPoly ι n N`. -/
theorem cellIntegral_inner_sub_galerkinProj {N : ℕ} {u : (Fin n → ℝ) → EuclideanSpace ℝ ι}
    (hu : Continuous u) {w : (Fin n → ℝ) → EuclideanSpace ℝ ι} (hw : w ∈ trigPoly ι n N) :
    cellIntegral (fun y => ⟪u y - galerkinProj N u y, w y⟫) = 0 := by
  have hc : Continuous (galerkinProj N u) := continuous_trigComb N _
  refine cellIntegral_inner_eq_zero_of_trigCoeffs (hu.sub hc) ?_ hw
  rw [sub_eq_add_neg, show (u + -galerkinProj N u) = u + (-1 : ℝ) • galerkinProj N u by simp,
    trigCoeffs_add N hu (hc.const_smul _)]
  ext i
  simp [trigCoeffs, ← trigCoeffs_galerkinProj N u, inner_neg_left, integral_neg, cellIntegral_def]

/-- `Π_N u` is the only element `v` of `trigPoly ι n N` with `u - v` orthogonal to
`trigPoly ι n N`. -/
theorem eq_galerkinProj {N : ℕ} {u v : (Fin n → ℝ) → EuclideanSpace ℝ ι} (hu : Continuous u)
    (hv : v ∈ trigPoly ι n N)
    (h : ∀ w ∈ trigPoly ι n N, cellIntegral (fun y => ⟪u y - v y, w y⟫) = 0) :
    v = galerkinProj N u := by
  have hd : v - galerkinProj N u ∈ trigPoly ι n N := sub_mem hv (galerkinProj_mem N u)
  have hcv := (contDiff_isPeriodic_of_mem_trigPoly hv).1.continuous
  have hcp : Continuous (galerkinProj N u) := continuous_trigComb N _
  obtain ⟨hdc, hdp⟩ := contDiff_isPeriodic_of_mem_trigPoly hd
  have h1 := h _ hd
  have h2 := cellIntegral_inner_sub_galerkinProj hu hd
  have h3 : cellIntegral (fun y => ⟪(v - galerkinProj N u) y, (v - galerkinProj N u) y⟫) = 0 := by
    have := cellIntegral_inner_sub_left (u := fun y => u y - galerkinProj N u y)
      (v := fun y => u y - v y) (hu.sub hcp) (hu.sub hcv) hdc.continuous
    rw [h1, h2, sub_zero] at this
    rw [← this]
    congr 1; ext y; congr 1; simp
  exact sub_eq_zero.1 (eq_zero_of_cellIntegral_inner_self hdc.continuous hdp h3)

theorem galerkinProj_eq_self {N : ℕ} {u : (Fin n → ℝ) → EuclideanSpace ℝ ι}
    (hu : u ∈ trigPoly ι n N) : galerkinProj N u = u :=
  (eq_galerkinProj (v := u) (contDiff_isPeriodic_of_mem_trigPoly hu).1.continuous hu fun w _ => by
    simp [cellIntegral_def]).symm

/-! ## The Galerkin system -/

section System

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `∂ᵢ` of a combination `∑ⱼ cⱼ(l, t) Wⱼ(l, t, ·)` with coefficients independent of `y`. -/
theorem dy_sum_smul {m : ℕ} (c : Fin m → (Fin p → ℝ) → ℝ → ℝ)
    {W : Fin m → (Fin p → ℝ) → ℝ → (Fin n → ℝ) → E} (hW : ∀ j l t, Differentiable ℝ (W j l t))
    (i : Fin n) :
    dy i (fun l t y => ∑ j, c j l t • W j l t y) = fun l t y => ∑ j, c j l t • dy i (W j) l t y := by
  funext l t y
  simp only [dy_def]
  rw [(HasFDerivAt.fun_sum (u := Finset.univ) (A := fun j y => c j l t • W j l t y) fun j _ =>
    ((hW j l t y).hasFDerivAt.const_smul (c j l t))).fderiv]
  simp

/-- The basis element `bⱼ` of `trigPoly ι n N` as a family constant in `(l, t)`. -/
def basisFamily (N : ℕ) (j : Fin (trigDim ι n N)) :
    (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι :=
  fun _ _ y => trigBasis ι n N j y

theorem isPeriodicSmooth_basisFamily (N : ℕ) (j : Fin (trigDim ι n N)) :
    IsPeriodicSmooth (basisFamily (p := p) N j) where
  smooth := (contDiff_trigBasis N j).comp (f := fun q : (Fin p → ℝ) × ℝ × (Fin n → ℝ) => q.2.2)
    (by fun_prop)
  periodic _ _ := isPeriodic_trigBasis N j

theorem dt_basisFamily (N : ℕ) (j : Fin (trigDim ι n N)) :
    dt (basisFamily (p := p) N j) = fun _ _ _ => 0 := by
  funext l t y
  simp [dt_def, basisFamily]

theorem contDiff_trigCoeffs (N : ℕ) {u : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι}
    (hu : ContDiff ℝ ∞ ↿u) :
    ContDiff ℝ ∞ fun q : (Fin p → ℝ) × ℝ => trigCoeffs N (u q.1 q.2) := by
  refine contDiff_pi.2 fun i => contDiff_cellIntegral
    (f := fun (q : (Fin p → ℝ) × ℝ) y => ⟪u q.1 q.2 y, trigBasis ι n N i y⟫) ?_
  exact (hu.comp (f := fun z : ((Fin p → ℝ) × ℝ) × (Fin n → ℝ) => (z.1.1, z.1.2, z.2))
    (by fun_prop)).inner ℝ ((contDiff_trigBasis N i).comp contDiff_snd)

variable (A : HypCoeffs p n ι) (N : ℕ)

/-- The linear part of the Galerkin system for the coefficients `(x, v)` of `V` and `∂ₜV`:
`ẋ = v`, `v̇ = G⁻¹ (∑ⱼ xⱼ ĉ(A bⱼ) + ∑ⱼ vⱼ ĉ(Bₜ bⱼ))`, where `ĉ = trigCoeffs N`. -/
def galerkinLin (l : Fin p → ℝ) (t : ℝ) :
    (Fin (trigDim ι n N) → ℝ) × (Fin (trigDim ι n N) → ℝ) →L[ℝ]
      (Fin (trigDim ι n N) → ℝ) × (Fin (trigDim ι n N) → ℝ) :=
  LinearMap.toContinuousLinearMap <| LinearMap.prod (LinearMap.snd ℝ _ _)
    (trigGramInv ι n N ∘ₗ
      (∑ j, (LinearMap.proj j ∘ₗ LinearMap.fst ℝ _ _).smulRight
          (trigCoeffs N (A.apply (basisFamily N j) l t)) +
        ∑ j, (LinearMap.proj j ∘ₗ LinearMap.snd ℝ _ _).smulRight
          (trigCoeffs N fun y => A.bt l t y (trigBasis ι n N j y))))

theorem galerkinLin_apply (l : Fin p → ℝ) (t : ℝ)
    (w : (Fin (trigDim ι n N) → ℝ) × (Fin (trigDim ι n N) → ℝ)) :
    galerkinLin A N l t w = (w.2, trigGramInv ι n N
      (∑ j, w.1 j • trigCoeffs N (A.apply (basisFamily N j) l t) +
        ∑ j, w.2 j • trigCoeffs N fun y => A.bt l t y (trigBasis ι n N j y))) := by
  simp [galerkinLin]

variable {A} {N}

theorem contDiff_galerkinLin (hA : A.IsGood) :
    ContDiff ℝ ∞ fun q : (Fin p → ℝ) × ℝ => galerkinLin A N q.1 q.2 := by
  refine contDiff_clm_apply_iff.2 fun w => ?_
  simp only [galerkinLin_apply]
  refine contDiff_const.prodMk ((LinearMap.toContinuousLinearMap (trigGramInv ι n N)).contDiff.comp
    ?_)
  refine (ContDiff.sum fun j _ => (contDiff_const (c := w.1 j)).smul
      (contDiff_trigCoeffs N (hA.apply (isPeriodicSmooth_basisFamily N j)).smooth)).add
    (ContDiff.sum fun j _ => (contDiff_const (c := w.2 j)).smul
      (contDiff_trigCoeffs N (u := fun l t y => A.bt l t y (trigBasis ι n N j y)) ?_))
  exact hA.smooth_bt.clm_apply ((contDiff_trigBasis N j).comp (by fun_prop))

/-- **Galerkin solutions**: for good coefficients and a smooth periodic source vanishing
for `t ≤ t₀`, the Galerkin system `∂ₜ²V = Π_N (A V + F)` has a smooth periodic solution with
values in `trigPoly ι n N`, vanishing for `t ≤ t₀`. Since `∂ₜV ∈ trigPoly ι n N`, the residual
`∂ₜ²V - A V - F` is orthogonal to `∂ₜV`, which is what the energy estimate uses. -/
theorem exists_galerkin (hA : A.IsGood)
    {F : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι} (hF : IsPeriodicSmooth F)
    {t₀ : ℝ} (hF0 : ∀ l t y, t ≤ t₀ → F l t y = 0) (N : ℕ) :
    ∃ V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι, IsPeriodicSmooth V ∧
      (∀ l t, V l t ∈ trigPoly ι n N) ∧ (∀ l t, dt V l t ∈ trigPoly ι n N) ∧
      (∀ l t y, t ≤ t₀ → V l t y = 0) ∧
      (∀ l t y, dt (dt V) l t y = galerkinProj N (A.apply V l t + F l t) y) ∧
      ∀ l t, cellIntegral (fun y => ⟪dt V l t y, dt (dt V) l t y - A.apply V l t y - F l t y⟫)
        = 0 := by
  set Ginv := trigGramInv ι n N
  set S := fun j => A.apply (basisFamily (p := p) N j)
  set R : Fin (trigDim ι n N) → (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι :=
    fun j l t y => A.bt l t y (trigBasis ι n N j y)
  have hS : ∀ j, IsPeriodicSmooth (S j) := fun j => hA.apply (isPeriodicSmooth_basisFamily N j)
  have hR : ∀ j, ContDiff ℝ ∞ ↿(R j) := fun j =>
    hA.smooth_bt.clm_apply ((contDiff_trigBasis N j).comp (by fun_prop))
  set f : (Fin p → ℝ) → ℝ → (Fin (trigDim ι n N) → ℝ) × (Fin (trigDim ι n N) → ℝ) :=
    fun l t => (0, Ginv (trigCoeffs N (F l t)))
  have hf : ContDiff ℝ ∞ fun q : (Fin p → ℝ) × ℝ => f q.1 q.2 :=
    contDiff_const.prodMk ((LinearMap.toContinuousLinearMap Ginv).contDiff.comp
      (contDiff_trigCoeffs N hF.smooth))
  have hf0 : ∀ l t, t ≤ t₀ → f l t = 0 := fun l t ht => by
    have : F l t = 0 := funext fun y => hF0 l t y ht
    have h0 : trigCoeffs N (0 : (Fin n → ℝ) → EuclideanSpace ℝ ι) = 0 := by
      ext i; simp [trigCoeffs, cellIntegral_def]
    simp [f, this, h0]
  obtain ⟨z, hz, hz0, hzd⟩ := ODEFlow.exists_linear_ode (contDiff_galerkinLin (N := N) hA) hf t₀
    hf0
  set V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι :=
    fun l t y => ∑ j, (z l t).1 j • basisFamily N j l t y
  set v' : (Fin p → ℝ) → ℝ → Fin (trigDim ι n N) → ℝ := fun l t =>
    Ginv (∑ j, (z l t).1 j • trigCoeffs N (S j l t) + ∑ j, (z l t).2 j • trigCoeffs N (R j l t)) +
      Ginv (trigCoeffs N (F l t))
  have hxd : ∀ l t j, HasDerivAt (fun s => (z l s).1 j) ((z l t).2 j) t := fun l t j => by
    have := hasDerivAt_pi.1 (hasFDerivAt_fst.comp_hasDerivAt t (hzd l t)) j
    simpa [galerkinLin_apply, f] using this
  have hvd : ∀ l t j, HasDerivAt (fun s => (z l s).2 j) (v' l t j) t := fun l t j => by
    have := hasDerivAt_pi.1 (hasFDerivAt_snd.comp_hasDerivAt t (hzd l t)) j
    simpa [galerkinLin_apply, f, v', S, R] using this
  have hdtV : dt V = fun l t y => ∑ j, (z l t).2 j • basisFamily N j l t y := by
    funext l t y
    rw [dt_apply]
    exact (HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
      (hxd l t j).smul_const (basisFamily N j l t y)).deriv
  have hdtdtV : dt (dt V) = fun l t y => trigComb N (v' l t) y := by
    rw [hdtV]
    funext l t y
    rw [dt_apply]
    exact (HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
      (hvd l t j).smul_const (basisFamily N j l t y)).deriv
  have hdiff : ∀ (j : Fin (trigDim ι n N)) l t, Differentiable ℝ (basisFamily (p := p) N j l t) := fun j l t =>
    ((isPeriodicSmooth_basisFamily N j).contDiff_slice l t).differentiable (by simp)
  have hdiff' : ∀ k (j : Fin (trigDim ι n N)) l t, Differentiable ℝ (dy k (basisFamily (p := p) N j) l t) :=
    fun k j l t =>
      (((isPeriodicSmooth_basisFamily N j).dy k).contDiff_slice l t).differentiable (by simp)
  have hdyV : ∀ k, dy k V = fun l t y => ∑ j, (z l t).1 j • dy k (basisFamily N j) l t y :=
    fun k => dy_sum_smul (fun j l t => (z l t).1 j) hdiff k
  have hdydyV : ∀ i k, dy i (dy k V) =
      fun l t y => ∑ j, (z l t).1 j • dy i (dy k (basisFamily N j)) l t y := fun i k => by
    rw [hdyV]; exact dy_sum_smul (fun j l t => (z l t).1 j) (hdiff' k) i
  have sc3 : ∀ G : Fin n → Fin n → Fin (trigDim ι n N) → EuclideanSpace ℝ ι,
      ∑ i, ∑ k, ∑ j, G i k j = ∑ j, ∑ i, ∑ k, G i k j := fun G =>
    (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans Finset.sum_comm
  have sc2 : ∀ G : Fin n → Fin (trigDim ι n N) → EuclideanSpace ℝ ι,
      ∑ i, ∑ j, G i j = ∑ j, ∑ i, G i j := fun G => Finset.sum_comm
  have happly : ∀ l t, A.apply V l t =
      fun y => ∑ j, (z l t).1 j • S j l t y + ∑ j, (z l t).2 j • R j l t y := by
    intro l t
    funext y
    simp only [S, R]
    simp only [HypCoeffs.apply_def, hdydyV]
    simp only [hdyV, hdtV, V, dt_basisFamily, map_sum, map_smul,
      map_zero, add_zero, Finset.smul_sum, smul_add, Finset.sum_add_distrib, smul_smul]
    conv_lhs => rw [sc3, sc2]
    simp only [basisFamily, mul_comm]
    abel
  have hSc : ∀ l t j, Continuous (S j l t) := fun l t j =>
    ((hS j).contDiff_slice l t).continuous
  have hRc : ∀ l t j, Continuous (R j l t) := fun l t j =>
    (hR j).continuous.comp (by fun_prop : Continuous fun y : Fin n → ℝ => (l, t, y))
  have hFc : ∀ l t, Continuous (F l t) := fun l t => (hF.contDiff_slice l t).continuous
  have hcoeffs : ∀ l t, trigCoeffs N (A.apply V l t + F l t) =
      ∑ j, (z l t).1 j • trigCoeffs N (S j l t) + ∑ j, (z l t).2 j • trigCoeffs N (R j l t) +
        trigCoeffs N (F l t) := fun l t => by
    have hc1 : Continuous fun y => ∑ j, (z l t).1 j • S j l t y :=
      continuous_finsetSum _ fun j _ => by have := hSc l t j; fun_prop
    have hc2 : Continuous fun y => ∑ j, (z l t).2 j • R j l t y :=
      continuous_finsetSum _ fun j _ => by have := hRc l t j; fun_prop
    have e : A.apply V l t + F l t = ((fun y => ∑ j, (z l t).1 j • S j l t y) +
        (fun y => ∑ j, (z l t).2 j • R j l t y)) + F l t := by
      rw [happly]; rfl
    rw [e, trigCoeffs_add N (hc1.add hc2) (hFc l t), trigCoeffs_add N hc1 hc2,
      trigCoeffs_sum_smul N _ (hSc l t), trigCoeffs_sum_smul N _ (hRc l t)]
  have hdtdt : ∀ l t, dt (dt V) l t = galerkinProj N (A.apply V l t + F l t) := fun l t => by
    rw [hdtdtV, galerkinProj, hcoeffs, map_add]
  have hV : IsPeriodicSmooth V := by
    refine ⟨?_, fun l t => (contDiff_isPeriodic_of_mem_trigPoly (trigComb_mem N (z l t).1)).2⟩
    change ContDiff ℝ ∞ fun q : (Fin p → ℝ) × ℝ × (Fin n → ℝ) =>
      ∑ j, (z q.1 q.2.1).1 j • trigBasis ι n N j q.2.2
    exact ContDiff.sum fun j _ => (((contDiff_apply ℝ ℝ j).comp contDiff_fst).comp
      (hz.comp (f := fun q : (Fin p → ℝ) × ℝ × (Fin n → ℝ) => (q.1, q.2.1)) (by fun_prop))).smul
      ((contDiff_trigBasis N j).comp (by fun_prop))
  have hdtVmem : ∀ l t, dt V l t ∈ trigPoly ι n N := fun l t => by
    rw [hdtV]; exact trigComb_mem N (z l t).2
  refine ⟨V, hV, fun l t => trigComb_mem N (z l t).1, hdtVmem, fun l t y ht => ?_,
    fun l t y => by rw [hdtdt], fun l t => ?_⟩
  · simp [V, hz0 l t ht]
  · have hu : Continuous (A.apply V l t + F l t) :=
      ((hA.apply hV).contDiff_slice l t).continuous.add (hFc l t)
    have h := cellIntegral_inner_sub_galerkinProj hu (hdtVmem l t)
    rw [hdtdt l t]
    have e : (fun y => ⟪dt V l t y, galerkinProj N (A.apply V l t + F l t) y - A.apply V l t y -
        F l t y⟫) = fun y => -⟪(A.apply V l t + F l t) y -
          galerkinProj N (A.apply V l t + F l t) y, dt V l t y⟫ := funext fun y => by
      rw [real_inner_comm, ← inner_neg_left]
      congr 1
      simp only [Pi.add_apply]
      abel
    rw [e, cellIntegral_def, integral_neg]
    rw [cellIntegral_def] at h
    exact neg_eq_zero.2 h

end System

end

end LorentzianCalderon.PDE
