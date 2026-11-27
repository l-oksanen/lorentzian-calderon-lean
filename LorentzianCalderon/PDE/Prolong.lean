module

public import LorentzianCalderon.PDE.Energy

public section

/-!
# Prolongation of the periodic core

If `V` solves `∂ₜ²V = a^{ij} ∂ᵢ∂ⱼV + Bₜ ∂ₜV + Bⁱ ∂ᵢV + C V + F`, then the prolongation
`W = (V, ∂_{y₁}V, …, ∂_{yₙ}V, ∂ₜV, ∂_{l₁}V, …, ∂_{l_p}V)` (`prol V`, with slots indexed by
`Dir n p`) solves a system of the same form with the same scalar principal part `a`
(`HypCoeffs.prolong`, `HypCoeffs.IsGood.prolong`). Differentiating the equation in direction
`s` gives, with `δ = ∂_s` applied to the coefficients only,

`∂ₜ²(∂_s V) = a^{ij} ∂ᵢ∂ⱼ(∂_s V) + Bₜ ∂ₜ(∂_s V) + Bⁱ ∂ᵢ(∂_s V) + C (∂_s V)`
`  + (δa^{ij}) ∂ᵢ(∂ⱼV) + (δBₜ) ∂ₜV + (δBⁱ) ∂ᵢV + (δC) V + ∂_s F`,

and `(δa^{ij}) ∂ᵢ(∂ⱼV)` is first order in the slot `∂ⱼV`, the others are of order zero. The
term `Bₜ ∂ₜ²V` of `∂ₜ(Bₜ ∂ₜV)` is `Bₜ ∂ₜ(∂ₜV)`, first order in the slot `∂ₜV`. Hence
`A.prolong.apply (prol V) = prol (A.apply V)` (`prolong_apply_prol`) and
`∂ₜ²(prol V) = prol (∂ₜ²V)`, so the residual of `W` is the prolongation of the residual of `V`
(`residual_prol`). No projection needs to be named: for a Galerkin solution
`∂ₜ²V = P (A V + F)` with `P` commuting with the derivatives, `dt_dt_prol_eq_blockwise` gives
`∂ₜ²W = P̃ (A.prolong W + prol F)` with `P̃` acting slotwise.

Iterating, every derivative `∂^α V` (`iterD α V`, `α : List (Dir n p)`) is a slot of an iterated
prolongation, and the energy estimate of the prolonged systems bounds
`‖∂ₜ∂^αV‖² + Σᵢ‖∂ᵢ∂^αV‖² + ‖∂^αV‖²` in `L²(cell)` on `K × [t₀, t₁]` by the data
(`HypCoeffs.IsGood.exists_iterD_bound`). The hypothesis is the orthogonality
`∫_cell ⟨∂^α ∂ₜV, ∂^α(∂ₜ²V - A V - F)⟩ = 0` for all `α`, which holds for exact solutions and for
Galerkin solutions (`∂^α ∂ₜV` is a trigonometric polynomial, and `∂^α` commutes with `P - 1`).
-/

namespace LorentzianCalderon.PDE

noncomputable section
open scoped ContDiff RealInnerProductSpace Topology
open Set MeasureTheory Function Real

variable {n p : ℕ} {ι : Type*} [Fintype ι]

/-! ## Slots of `EuclideanSpace ℝ (ι × Dir n p)` -/

/-- The slot `s` of a prolonged vector. -/
def block (s : Dir n p) : EuclideanSpace ℝ (ι × Dir n p) →L[ℝ] EuclideanSpace ℝ ι :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => WithLp.toLp 2 fun i => w.ofLp (i, s)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- The vector with `v` in the slot `s` and zeros elsewhere. -/
def embed (s : Dir n p) : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ (ι × Dir n p) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 fun q => if q.2 = s then v.ofLp q.1 else 0
      map_add' := fun v w => by ext q; by_cases h : q.2 = s <;> simp [h]
      map_smul' := fun c v => by ext q; by_cases h : q.2 = s <;> simp [h] }

@[simp] theorem block_apply (s : Dir n p) (w : EuclideanSpace ℝ (ι × Dir n p)) (i : ι) :
    (block s w).ofLp i = w.ofLp (i, s) := by rfl

@[simp] theorem embed_apply (s : Dir n p) (v : EuclideanSpace ℝ ι) (q : ι × Dir n p) :
    (embed s v).ofLp q = if q.2 = s then v.ofLp q.1 else 0 := by rfl

theorem block_embed (s s' : Dir n p) (v : EuclideanSpace ℝ ι) :
    block s (embed s' v) = if s' = s then v else 0 := by
  ext i
  by_cases h : s' = s
  · subst h; simp
  · simp [h, show s ≠ s' from fun e => h e.symm]

theorem block_sum_embed (s : Dir n p) (f : Dir n p → EuclideanSpace ℝ ι) :
    block s (∑ s', embed s' (f s')) = f s := by
  simp [map_sum, block_embed]

theorem ext_block {w w' : EuclideanSpace ℝ (ι × Dir n p)} (h : ∀ s, block s w = block s w') :
    w = w' := by
  ext q
  exact congrArg (fun v : EuclideanSpace ℝ ι => v.ofLp q.1) (h q.2)

theorem inner_eq_sum_block (w w' : EuclideanSpace ℝ (ι × Dir n p)) :
    ⟪w, w'⟫ = ∑ s, ⟪block s w, block s w'⟫ := by
  simp only [PiLp.inner_apply, block_apply]
  rw [Fintype.sum_prod_type, Finset.sum_comm]

theorem norm_sq_eq_sum_block (w : EuclideanSpace ℝ (ι × Dir n p)) :
    ‖w‖ ^ 2 = ∑ s, ‖block s w‖ ^ 2 := by
  simp only [← real_inner_self_eq_norm_sq, inner_eq_sum_block]

/-- The linear map whose slot `s` is `L s`. -/
def fromBlocks (L : Dir n p → EuclideanSpace ℝ (ι × Dir n p) →L[ℝ] EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ (ι × Dir n p) →L[ℝ] EuclideanSpace ℝ (ι × Dir n p) :=
  ∑ s, (embed s).comp (L s)

@[simp] theorem block_fromBlocks
    (L : Dir n p → EuclideanSpace ℝ (ι × Dir n p) →L[ℝ] EuclideanSpace ℝ ι) (s : Dir n p)
    (w : EuclideanSpace ℝ (ι × Dir n p)) : block s (fromBlocks L w) = L s w := by
  simp [fromBlocks, block_embed]

theorem contDiff_fromBlocks {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {L : Dir n p → Z → EuclideanSpace ℝ (ι × Dir n p) →L[ℝ] EuclideanSpace ℝ ι}
    (hL : ∀ s, ContDiff ℝ ∞ (L s)) : ContDiff ℝ ∞ fun z => fromBlocks fun s => L s z := by
  simp only [fromBlocks]
  exact ContDiff.sum fun s _ => contDiff_const.clm_comp (hL s)

/-! ## The prolonged system -/

/-- The prolonged coefficients: the same scalar principal part, block diagonal lower order
terms, plus the commutator terms `(∂ₛa^{ij}) ∂ᵢ(∂ⱼV)` (first order in the slot `space j`) and
`(∂ₛBₜ) ∂ₜV + (∂ₛBⁱ) ∂ᵢV + (∂ₛC) V` (order zero) in the slot `s`. -/
def HypCoeffs.prolong (A : HypCoeffs p n ι) : HypCoeffs p n (ι × Dir n p) where
  a := A.a
  bt l t y := fromBlocks fun s => (A.bt l t y).comp (block s)
  b i l t y := fromBlocks fun s => (A.b i l t y).comp (block s) +
    ∑ j, s.dc (A.a i j) l t y • block (Dir.space j)
  c l t y := fromBlocks fun s => (A.c l t y).comp (block s) +
    (s.dc A.bt l t y).comp (block Dir.time) +
    ∑ i, (s.dc (A.b i) l t y).comp (block (Dir.space i)) +
    (s.dc A.c l t y).comp (block Dir.self)

theorem HypCoeffs.IsGood.prolong {A : HypCoeffs p n ι} (hA : A.IsGood) : A.prolong.IsGood where
  smooth_a := hA.smooth_a
  smooth_bt := contDiff_fromBlocks (L := fun s z => (↿A.bt z).comp (block s))
    fun s => hA.smooth_bt.clm_comp contDiff_const
  smooth_b i := contDiff_fromBlocks (L := fun s z => (↿(A.b i) z).comp (block s) +
      ∑ j, ↿(s.dc (A.a i j)) z • block (Dir.space j))
    fun s => ((hA.smooth_b i).clm_comp contDiff_const).add (ContDiff.sum fun j _ =>
      ((hA.isPeriodicSmooth_a i j).dc s).smooth.smul contDiff_const)
  smooth_c := contDiff_fromBlocks (L := fun s z => (↿A.c z).comp (block s) +
      (↿(s.dc A.bt) z).comp (block Dir.time) +
      ∑ i, (↿(s.dc (A.b i)) z).comp (block (Dir.space i)) +
      (↿(s.dc A.c) z).comp (block Dir.self))
    fun s => (((hA.smooth_c.clm_comp contDiff_const).add
      ((hA.isPeriodicSmooth_bt.dc s).smooth.clm_comp contDiff_const)).add
      (ContDiff.sum fun i _ => ((hA.isPeriodicSmooth_b i).dc s).smooth.clm_comp
        contDiff_const)).add
      ((hA.isPeriodicSmooth_c.dc s).smooth.clm_comp contDiff_const)
  periodic_a := hA.periodic_a
  periodic_bt l t := isPeriodic_iff.2 fun k y => by
    simp only [HypCoeffs.prolong, (hA.periodic_bt l t).add_single k y]
  periodic_b i l t := isPeriodic_iff.2 fun k y => by
    have h : ∀ (s : Dir n p) j, s.dc (A.a i j) l t (y + Pi.single k 1) = s.dc (A.a i j) l t y :=
      fun s j => (((hA.isPeriodicSmooth_a i j).dc s).periodic l t).add_single k y
    simp only [HypCoeffs.prolong, (hA.periodic_b i l t).add_single k y, h]
  periodic_c l t := isPeriodic_iff.2 fun k y => by
    have h1 : ∀ s : Dir n p, s.dc A.bt l t (y + Pi.single k 1) = s.dc A.bt l t y :=
      fun s => ((hA.isPeriodicSmooth_bt.dc s).periodic l t).add_single k y
    have h2 : ∀ (s : Dir n p) i, s.dc (A.b i) l t (y + Pi.single k 1) = s.dc (A.b i) l t y :=
      fun s i => (((hA.isPeriodicSmooth_b i).dc s).periodic l t).add_single k y
    have h3 : ∀ s : Dir n p, s.dc A.c l t (y + Pi.single k 1) = s.dc A.c l t y :=
      fun s => ((hA.isPeriodicSmooth_c.dc s).periodic l t).add_single k y
    simp only [HypCoeffs.prolong, (hA.periodic_c l t).add_single k y, h1, h2, h3]
  symm := hA.symm
  pos := hA.pos

/-! ## Prolongation of families -/

/-- The prolongation `W = (V, ∂_{y₁}V, …, ∂_{yₙ}V, ∂ₜV, ∂_{l₁}V, …, ∂_{l_p}V)`: the slot `s` of
`W` is `s.d V`. -/
def prol (V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι) :
    (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ (ι × Dir n p) :=
  fun l t y => ∑ s, embed s (s.d V l t y)

@[simp] theorem block_prol (V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι)
    (s : Dir n p) (l : Fin p → ℝ) (t : ℝ) (y : Fin n → ℝ) : block s (prol V l t y) = s.d V l t y :=
  block_sum_embed _ _

theorem isPeriodicSmooth_clm {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] G)
    {U : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → E} (hU : IsPeriodicSmooth U) :
    IsPeriodicSmooth fun l t y => L (U l t y) where
  smooth := contDiff_const.clm_apply hU.smooth
  periodic l t := isPeriodic_iff.2 fun k y => by simp only [(hU.periodic l t).add_single k y]

theorem isPeriodicSmooth_prol {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι}
    (hV : IsPeriodicSmooth V) : IsPeriodicSmooth (prol V) where
  smooth := ContDiff.sum (s := Finset.univ) fun s _ => contDiff_const.clm_apply (hV.d s).smooth
  periodic l t := isPeriodic_iff.2 fun k y => by simp only [prol,
    fun s : Dir n p => ((hV.d s).periodic l t).add_single k y]

/-- Iterated partial derivatives: `iterD [s₁, …, s_m] U = ∂_{s_m} ⋯ ∂_{s₁} U`. -/
def iterD {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] :
    List (Dir n p) → ((Fin p → ℝ) → ℝ → (Fin n → ℝ) → X) → (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X
  | [], U => U
  | s :: α, U => iterD α (s.d U)

@[simp] theorem iterD_nil {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (U : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X) : iterD [] U = U := by rfl

@[simp] theorem iterD_cons {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (s : Dir n p)
    (α : List (Dir n p)) (U : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X) :
    iterD (s :: α) U = iterD α (s.d U) := by rfl

theorem IsPeriodicSmooth.iterD {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {U : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X} (hU : IsPeriodicSmooth U) (α : List (Dir n p)) :
    IsPeriodicSmooth (iterD α U) := by
  induction α generalizing U with
  | nil => exact hU
  | cons s α ih => exact ih (hU.d s)

/-- Derivatives commute with a constant linear map. -/
theorem d_clm_family {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] G)
    {U : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → E} (hU : Differentiable ℝ ↿U) (s : Dir n p) :
    s.d (fun l t y => L (U l t y)) = fun l t y => L (s.d U l t y) := by
  funext l t y
  exact Dir.d_clm_const L hU

theorem iterD_clm {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] G)
    {U : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → E} (hU : IsPeriodicSmooth U) (α : List (Dir n p)) :
    iterD α (fun l t y => L (U l t y)) = fun l t y => L (iterD α U l t y) := by
  induction α generalizing U with
  | nil => rfl
  | cons s α ih =>
    simp only [iterD_cons]
    rw [d_clm_family L hU.differentiable s]
    exact ih (hU.d s)

theorem block_iterD_prol {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι}
    (hV : IsPeriodicSmooth V) (s : Dir n p) (α : List (Dir n p)) (l : Fin p → ℝ) (t : ℝ)
    (y : Fin n → ℝ) : block s (iterD α (prol V) l t y) = iterD α (s.d V) l t y := by
  have h := congrFun (congrFun (congrFun (iterD_clm (block s) (isPeriodicSmooth_prol hV) α) l)
    t) y
  simp only [block_prol] at h
  exact h.symm

@[simp] theorem block_dy_prol {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι}
    (hV : IsPeriodicSmooth V) (s : Dir n p) (i : Fin n) (l : Fin p → ℝ) (t : ℝ)
    (y : Fin n → ℝ) : block s (dy i (prol V) l t y) = dy i (s.d V) l t y := by
  simpa only [iterD_cons, iterD_nil, Dir.d_space] using block_iterD_prol hV s [Dir.space i] l t y

@[simp] theorem block_dt_prol {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι}
    (hV : IsPeriodicSmooth V) (s : Dir n p) (l : Fin p → ℝ) (t : ℝ)
    (y : Fin n → ℝ) : block s (dt (prol V) l t y) = dt (s.d V) l t y := by
  simpa only [iterD_cons, iterD_nil, Dir.d_time] using block_iterD_prol hV s [Dir.time] l t y

@[simp] theorem block_dy_dy_prol {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι}
    (hV : IsPeriodicSmooth V) (s : Dir n p) (i j : Fin n) (l : Fin p → ℝ) (t : ℝ)
    (y : Fin n → ℝ) : block s (dy i (dy j (prol V)) l t y) = dy i (dy j (s.d V)) l t y := by
  simpa only [iterD_cons, iterD_nil, Dir.d_space] using
    block_iterD_prol hV s [Dir.space j, Dir.space i] l t y

@[simp] theorem block_dt_dt_prol {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι}
    (hV : IsPeriodicSmooth V) (s : Dir n p) (l : Fin p → ℝ) (t : ℝ)
    (y : Fin n → ℝ) : block s (dt (dt (prol V)) l t y) = dt (dt (s.d V)) l t y := by
  simpa only [iterD_cons, iterD_nil, Dir.d_time] using
    block_iterD_prol hV s [Dir.time, Dir.time] l t y

/-! ## The prolonged equation -/

/-- The Leibniz rule for the operator: `∂ₛ(A V)`, with the derivatives of the coefficients
(`Dir.dc`, zero for `self`) and of the unknown separated. -/
theorem d_apply {A : HypCoeffs p n ι} (hA : A.IsGood)
    {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι} (hV : IsPeriodicSmooth V)
    (s : Dir n p) (l : Fin p → ℝ) (t : ℝ) (y : Fin n → ℝ) :
    s.d (A.apply V) l t y =
      ∑ i, ∑ j, (A.a i j l t y • dy i (dy j (s.d V)) l t y +
        s.dc (A.a i j) l t y • dy i (dy j V) l t y) +
      (s.dc A.bt l t y (dt V l t y) + A.bt l t y (dt (s.d V) l t y)) +
      ∑ i, (s.dc (A.b i) l t y (dy i V l t y) + A.b i l t y (dy i (s.d V) l t y)) +
      (s.dc A.c l t y (V l t y) + A.c l t y (s.d V l t y)) := by
  by_cases hs : s = Dir.self
  · subst hs
    simp [HypCoeffs.apply_def]
  have h := (((HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
      HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
      (Dir.hasDerivAt_line hs (hA.isPeriodicSmooth_a i j).differentiable l t y).fun_smul
        (Dir.hasDerivAt_line hs ((hV.dy j).dy i).differentiable l t y)).fun_add
    ((Dir.hasDerivAt_line hs hA.isPeriodicSmooth_bt.differentiable l t y).clm_apply
      (Dir.hasDerivAt_line hs hV.dt.differentiable l t y))).fun_add
    (HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
      (Dir.hasDerivAt_line hs (hA.isPeriodicSmooth_b i).differentiable l t y).clm_apply
        (Dir.hasDerivAt_line hs (hV.dy i).differentiable l t y))).fun_add
    ((Dir.hasDerivAt_line hs hA.isPeriodicSmooth_c.differentiable l t y).clm_apply
      (Dir.hasDerivAt_line hs hV.differentiable l t y))
  simp only [zero_smul, add_zero, uncurry_apply_triple] at h
  rw [Dir.d_eq_of_hasDerivAt (l := l) (t := t) (y := y) hs (hA.apply hV).differentiable
    (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => by
      rw [HypCoeffs.apply_def]
      rfl))]
  simp only [Dir.dc_eq_d hs, Dir.d_dy hV.smooth, Dir.d_dy (hV.dy _).smooth, Dir.d_dt hV.smooth]

/-- **The prolonged operator.** `A.prolong (prol V) = prol (A V)`. -/
theorem prolong_apply_prol {A : HypCoeffs p n ι} (hA : A.IsGood)
    {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι} (hV : IsPeriodicSmooth V) :
    A.prolong.apply (prol V) = prol (A.apply V) := by
  funext l t y
  refine ext_block fun s => ?_
  rw [block_prol, d_apply hA hV]
  simp only [HypCoeffs.apply_def, HypCoeffs.prolong, map_add, map_sum, map_smul, block_fromBlocks,
    _root_.add_apply, ContinuousLinearMap.comp_apply, _root_.sum_apply,
    _root_.smul_apply, block_dy_dy_prol hV, block_dt_prol hV, block_dy_prol hV,
    block_prol, Dir.d_self, Dir.d_time, Dir.d_space, Finset.sum_add_distrib]
  abel

/-- The residual `∂ₜ²V - A V - F` of the equation. -/
def residual (A : HypCoeffs p n ι) (V F : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι) :
    (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι :=
  fun l t y => dt (dt V) l t y - A.apply V l t y - F l t y

theorem residual_def (A : HypCoeffs p n ι)
    (V F : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι) :
    residual A V F =
      fun l t y => dt (dt V) l t y - A.apply V l t y - F l t y := by rfl

theorem isPeriodicSmooth_residual {A : HypCoeffs p n ι} (hA : A.IsGood)
    {V F : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι} (hV : IsPeriodicSmooth V)
    (hF : IsPeriodicSmooth F) : IsPeriodicSmooth (residual A V F) where
  smooth := (hV.dt.dt.smooth.sub (hA.apply hV).smooth).sub hF.smooth
  periodic l t := isPeriodic_iff.2 fun k y => by
    simp only [residual, (hV.dt.dt.periodic l t).add_single k y,
      ((hA.apply hV).periodic l t).add_single k y,
      (hF.periodic l t).add_single k y]

/-- **The prolonged equation.** The residual of `prol V` for the prolonged system with source
`prol F` is the prolongation of the residual of `V`; in particular `prol V` solves the
prolonged system if `V` solves the original one. -/
theorem residual_prol {A : HypCoeffs p n ι} (hA : A.IsGood)
    {V F : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι} (hV : IsPeriodicSmooth V)
    (hF : IsPeriodicSmooth F) :
    residual A.prolong (prol V) (prol F) = prol (residual A V F) := by
  funext l t y
  refine ext_block fun s => ?_
  have hsub : s.d (residual A V F) l t y =
      s.d (dt (dt V)) l t y - s.d (A.apply V) l t y - s.d F l t y := by
    rw [show residual A V F = fun l t y => dt (dt V) l t y - A.apply V l t y - F l t y from rfl,
      Dir.d_sub ((hV.dt.dt.smooth.sub (hA.apply hV).smooth).differentiable (by simp))
      hF.differentiable]
    rw [Dir.d_sub hV.dt.dt.differentiable (hA.apply hV).differentiable]
  rw [block_prol, hsub]
  show block s (dt (dt (prol V)) l t y - A.prolong.apply (prol V) l t y - prol F l t y) = _
  rw [prolong_apply_prol hA hV, map_sub, map_sub, block_dt_dt_prol hV,
    block_prol, block_prol, Dir.d_dt hV.dt.smooth, Dir.d_dt hV.smooth]

/-- An operator on functions of `y` applied slot by slot. -/
def blockwise (P : ((Fin n → ℝ) → EuclideanSpace ℝ ι) → (Fin n → ℝ) → EuclideanSpace ℝ ι)
    (u : (Fin n → ℝ) → EuclideanSpace ℝ (ι × Dir n p)) :
    (Fin n → ℝ) → EuclideanSpace ℝ (ι × Dir n p) :=
  fun y => ∑ s, embed s (P (fun y => block s (u y)) y)

/-- **The prolonged Galerkin equation.** If `∂ₜ²V = P (A V + F)` for an operator `P` on
functions of `y` that commutes with the partial derivatives (such as a Fourier projection),
then `∂ₜ²(prol V) = P̃ (A.prolong (prol V) + prol F)` with `P̃ = blockwise P`. -/
theorem dt_dt_prol_eq_blockwise {A : HypCoeffs p n ι} (hA : A.IsGood)
    {V F : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι} (hV : IsPeriodicSmooth V)
    (hF : IsPeriodicSmooth F)
    (P : ((Fin n → ℝ) → EuclideanSpace ℝ ι) → (Fin n → ℝ) → EuclideanSpace ℝ ι)
    (hP : ∀ X : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι, IsPeriodicSmooth X →
      ∀ s : Dir n p, s.d (fun l t => P (X l t)) = fun l t => P (s.d X l t))
    (h : ∀ l t, dt (dt V) l t = P fun y => A.apply V l t y + F l t y) (l : Fin p → ℝ) (t : ℝ) :
    dt (dt (prol V)) l t =
      blockwise P (fun y => A.prolong.apply (prol V) l t y + prol F l t y) := by
  have hX : IsPeriodicSmooth fun l t y => A.apply V l t y + F l t y :=
    ⟨(hA.apply hV).smooth.add hF.smooth, fun l t => isPeriodic_iff.2 fun k y => by
      simp only [((hA.apply hV).periodic l t).add_single k y, (hF.periodic l t).add_single k y]⟩
  have hVtt : dt (dt V) = fun l t => P fun y => A.apply V l t y + F l t y := by
    funext l t; exact h l t
  funext y
  refine ext_block fun s => ?_
  rw [blockwise, block_sum_embed, block_dt_dt_prol hV, ← Dir.d_dt hV.smooth,
    ← Dir.d_dt hV.dt.smooth, hVtt, hP _ hX s]
  show P (s.d _ l t) y = _
  congr 1
  funext y'
  rw [map_add, prolong_apply_prol hA hV, block_prol, block_prol,
    Dir.d_add (hA.apply hV).differentiable hF.differentiable]

/-! ## Norms of prolonged families -/

theorem firstOrderNormSq_nonneg (V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι)
    (l : Fin p → ℝ) (t : ℝ) : 0 ≤ firstOrderNormSq V l t := by
  rw [firstOrderNormSq_def, cellIntegral_def]
  exact setIntegral_nonneg measurableSet_cell fun _ _ => by
    simp only [firstOrderDensity_def]; positivity

theorem firstOrderNormSq_eq_sum_block
    {U : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ (ι × Dir n p)}
    (hU : IsPeriodicSmooth U) (l : Fin p → ℝ) (t : ℝ) :
    firstOrderNormSq U l t = ∑ s, firstOrderNormSq (fun l t y => block s (U l t y)) l t := by
  have hpt : ∀ y, firstOrderDensity U l t y =
      ∑ s, firstOrderDensity (fun l t y => block s (U l t y)) l t y := fun y => by
    have h1 := fun s : Dir n p => Dir.d_clm_const (s := (Dir.time : Dir n p)) (l := l) (t := t)
      (y := y) (block (ι := ι) s) hU.differentiable
    have h2 := fun (s : Dir n p) (i : Fin n) => Dir.d_clm_const (s := (Dir.space i : Dir n p))
      (l := l) (t := t) (y := y) (block (ι := ι) s) hU.differentiable
    simp only [Dir.d_time, Dir.d_space] at h1 h2
    simp only [firstOrderDensity_def, h1, h2, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun s i => ‖block s (dy i U l t y)‖ ^ 2)]
    simp only [← norm_sq_eq_sum_block]
  simp only [firstOrderNormSq_def, cellIntegral_def]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_finsetSum _ fun s _ =>
    integrableOn_cell (continuous_firstOrderDensity (isPeriodicSmooth_clm (block s) hU) l t)]

theorem cellNormSq_eq_sum_block
    {U : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ (ι × Dir n p)}
    (hU : Continuous ↿U) (l : Fin p → ℝ) (t : ℝ) :
    cellNormSq U l t = ∑ s, cellNormSq (fun l t y => block s (U l t y)) l t := by
  have hc := continuous_slice hU l t
  simp only [cellNormSq_def, cellIntegral_def, norm_sq_eq_sum_block (U l t _)]
  exact integral_finsetSum _ fun s _ => integrableOn_cell (by fun_prop)

theorem slot_iterD_prol {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι}
    (hV : IsPeriodicSmooth V) (s : Dir n p) (β : List (Dir n p)) :
    (fun l t y => block s (iterD β (prol V) l t y)) = iterD (s :: β) V := by
  funext l t y
  exact block_iterD_prol hV s β l t y

theorem block_iterD_dt_prol {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι}
    (hV : IsPeriodicSmooth V) (s : Dir n p) (β : List (Dir n p)) (l : Fin p → ℝ) (t : ℝ)
    (y : Fin n → ℝ) : block s (iterD β (dt (prol V)) l t y) = iterD (s :: β) (dt V) l t y := by
  have h := block_iterD_prol hV s (Dir.time :: β) l t y
  simp only [iterD_cons, Dir.d_time] at h
  rw [h, iterD_cons, Dir.d_dt hV.smooth]

/-! ## Bounds of all derivatives -/

/-- The order-zero bound: the energy estimate in terms of `‖∂ₜV‖² + Σ‖∂ᵢV‖² + ‖V‖²`, with
data `D` bounding the initial value and `∫_{t₀}^{t₁} ‖F‖²`. -/
theorem HypCoeffs.IsGood.exists_firstOrder_bound {A : HypCoeffs p n ι} (hA : A.IsGood)
    {K : Set (Fin p → ℝ)} (hK : IsCompact K) (t₀ t₁ : ℝ) :
    ∃ C, ∀ l ∈ K, ∀ (V F : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι) (D : ℝ),
      IsPeriodicSmooth V → Continuous ↿F →
      (∀ t ∈ Icc t₀ t₁, cellIntegral (fun y => ⟪dt V l t y, residual A V F l t y⟫) = 0) →
      firstOrderNormSq V l t₀ ≤ D → ∫ s in t₀..t₁, cellNormSq F l s ≤ D →
      ∀ t ∈ Icc t₀ t₁, firstOrderNormSq V l t ≤ C * D := by
  obtain ⟨C, hC, hE⟩ := hA.energy_le hK t₀ t₁
  obtain ⟨c, hc, hlow⟩ := hA.energy_ge (hK.prod isCompact_Icc)
  obtain ⟨M, hM⟩ := hA.energy_le_mul (hK.prod isCompact_Icc)
  refine ⟨exp (C * (t₁ - t₀)) * (max M 0 + 1) / c,
    fun l hl V F D hV hF horth hD0 hD1 t ht => ?_⟩
  have ht₀ : t₀ ∈ Icc t₀ t₁ := ⟨le_rfl, ht.1.trans ht.2⟩
  have hFO := firstOrderNormSq_nonneg V l t₀
  have hD : 0 ≤ D := hFO.trans hD0
  have h1 := hE l hl V F hV hF horth t ht
  have h2 := hlow l t ⟨hl, ht⟩ V hV
  have h3 := hM l t₀ ⟨hl, ht₀⟩ V hV
  have h4 : ∫ s in t₀..t, cellNormSq F l s ≤ ∫ s in t₀..t₁, cellNormSq F l s :=
    intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
      (Filter.Eventually.of_forall fun s => cellNormSq_nonneg F l s)
      ((continuous_cellNormSq hF l).intervalIntegrable _ _)
  have h5 : energy A V l t₀ + ∫ s in t₀..t, cellNormSq F l s ≤ (max M 0 + 1) * D := by
    have : M * firstOrderNormSq V l t₀ ≤ max M 0 * D :=
      (mul_le_mul_of_nonneg_right (le_max_left M 0) hFO).trans
        (mul_le_mul_of_nonneg_left hD0 (le_max_right M 0))
    linarith
  have h6 : exp (C * (t - t₀)) ≤ exp (C * (t₁ - t₀)) :=
    exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith [ht.2]) hC)
  have h7 : c * firstOrderNormSq V l t ≤ exp (C * (t₁ - t₀)) * ((max M 0 + 1) * D) :=
    h2.trans (h1.trans ((mul_le_mul_of_nonneg_left h5 (exp_pos _).le).trans
      (mul_le_mul_of_nonneg_right h6 (by positivity))))
  rw [show exp (C * (t₁ - t₀)) * (max M 0 + 1) / c * D =
    exp (C * (t₁ - t₀)) * ((max M 0 + 1) * D) / c by ring, le_div_iff₀ hc]
  linarith

/-- **Bounds of all derivatives.** For every order `m`, the quantities
`‖∂ₜ∂^αV‖² + Σᵢ‖∂ᵢ∂^αV‖² + ‖∂^αV‖²` in `L²(cell)` with `|α| ≤ m` (`α` a list of directions
`yᵢ`, `t`, `lₖ`, or `self`) are bounded on `K × [t₀, t₁]` by `C D`, where `D` bounds the same
quantities at `t₀` and `∫_{t₀}^{t₁} ‖∂^αF‖²`. The hypothesis is the orthogonality
`∫_cell ⟨∂^α ∂ₜV, ∂^α(∂ₜ²V - A V - F)⟩ = 0` for `|α| ≤ m`. The proof is the energy estimate of
the `m`-fold prolonged system. -/
theorem HypCoeffs.IsGood.exists_iterD_bound {A : HypCoeffs p n ι} (hA : A.IsGood)
    {K : Set (Fin p → ℝ)} (hK : IsCompact K) (t₀ t₁ : ℝ) (m : ℕ) :
    ∃ C, ∀ l ∈ K, ∀ (V F : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → EuclideanSpace ℝ ι) (D : ℝ),
      IsPeriodicSmooth V → IsPeriodicSmooth F →
      (∀ α : List (Dir n p), α.length ≤ m → ∀ t ∈ Icc t₀ t₁,
        cellIntegral (fun y => ⟪iterD α (dt V) l t y, iterD α (residual A V F) l t y⟫) = 0) →
      (∀ α : List (Dir n p), α.length ≤ m →
        firstOrderNormSq (iterD α V) l t₀ ≤ D ∧ ∫ s in t₀..t₁, cellNormSq (iterD α F) l s ≤ D) →
      ∀ α : List (Dir n p), α.length ≤ m → ∀ t ∈ Icc t₀ t₁,
        firstOrderNormSq (iterD α V) l t ≤ C * D := by
  induction m generalizing ι with
  | zero =>
    obtain ⟨C, hC⟩ := hA.exists_firstOrder_bound hK t₀ t₁
    refine ⟨C, fun l hl V F D hV hF horth hD α hα t ht => ?_⟩
    obtain rfl : α = [] := List.length_eq_zero_iff.1 (Nat.le_zero.1 hα)
    exact hC l hl V F D hV hF.smooth.continuous (horth [] le_rfl) (hD [] le_rfl).1
      (hD [] le_rfl).2 t ht
  | succ m ih =>
    obtain ⟨C, hC⟩ := ih hA.prolong
    set N : ℝ := (Fintype.card (Dir n p) : ℝ)
    refine ⟨C * N, fun l hl V F D hV hF horth hD α hα t ht => ?_⟩
    have hW := isPeriodicSmooth_prol hV
    have hFW := isPeriodicSmooth_prol hF
    have hR := isPeriodicSmooth_residual hA hV hF
    have horthW : ∀ β : List (Dir n p), β.length ≤ m → ∀ t ∈ Icc t₀ t₁,
        cellIntegral (fun y => ⟪iterD β (dt (prol V)) l t y,
          iterD β (residual A.prolong (prol V) (prol F)) l t y⟫) = 0 := by
      intro β hβ t ht
      have hβ' : (∀ s : Dir n p, (s :: β).length ≤ m + 1) := fun s => by simpa using hβ
      simp only [residual_prol hA hV hF, inner_eq_sum_block, block_iterD_dt_prol hV,
        block_iterD_prol hR]
      rw [cellIntegral_def, integral_finsetSum _ fun s _ => integrableOn_cell
        ((continuous_slice ((hV.dt.iterD (s :: β)).smooth.continuous) l t).inner
          (continuous_slice ((hR.iterD (s :: β)).smooth.continuous) l t))]
      exact Finset.sum_eq_zero fun s _ => by
        simpa only [cellIntegral_def, iterD_cons] using horth (s :: β) (hβ' s) t ht
    have hDW : ∀ β : List (Dir n p), β.length ≤ m →
        firstOrderNormSq (iterD β (prol V)) l t₀ ≤ N * D ∧
          ∫ s in t₀..t₁, cellNormSq (iterD β (prol F)) l s ≤ N * D := by
      intro β hβ
      have hβ' : (∀ s : Dir n p, (s :: β).length ≤ m + 1) := fun s => by simpa using hβ
      constructor
      · rw [firstOrderNormSq_eq_sum_block (hW.iterD β)]
        simp only [slot_iterD_prol hV]
        refine (Finset.sum_le_sum fun s _ => (hD (s :: β) (hβ' s)).1).trans ?_
        simp [N]
      · simp only [cellNormSq_eq_sum_block (hFW.iterD β).smooth.continuous,
          slot_iterD_prol hF]
        rw [intervalIntegral.integral_finsetSum fun s _ =>
          (continuous_cellNormSq (hF.iterD (s :: β)).smooth.continuous l).intervalIntegrable _ _]
        refine (Finset.sum_le_sum fun s _ => (hD (s :: β) (hβ' s)).2).trans ?_
        simp [N]
    have key := hC l hl (prol V) (prol F) (N * D) hW hFW horthW hDW
    obtain ⟨s, β, hsβ, hβ⟩ : ∃ (s : Dir n p) (β : List (Dir n p)),
        iterD α V = iterD (s :: β) V ∧ β.length ≤ m := by
      cases α with
      | nil => exact ⟨Dir.self, [], by simp only [iterD_cons, iterD_nil, Dir.d_self], Nat.zero_le _⟩
      | cons s β => exact ⟨s, β, rfl, by simpa using hα⟩
    rw [hsβ, ← slot_iterD_prol hV]
    calc firstOrderNormSq (fun l t y => block s (iterD β (prol V) l t y)) l t
        ≤ ∑ s', firstOrderNormSq (fun l t y => block s' (iterD β (prol V) l t y)) l t :=
          Finset.single_le_sum (f := fun s' => firstOrderNormSq
            (fun l t y => block s' (iterD β (prol V) l t y)) l t)
            (fun _ _ => firstOrderNormSq_nonneg _ _ _) (Finset.mem_univ s)
      _ = firstOrderNormSq (iterD β (prol V)) l t :=
          (firstOrderNormSq_eq_sum_block (hW.iterD β) l t).symm
      _ ≤ C * (N * D) := key β hβ t ht
      _ = C * N * D := by ring

end

end LorentzianCalderon.PDE
