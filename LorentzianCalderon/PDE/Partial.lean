module

public import LorentzianCalderon.PDE.Periodic

public section

/-!
# Partial derivatives of families: directions, Leibniz rules, commutation

The partial derivatives `dt`, `dy i`, `dpar k` of `PDE/Periodic` are collected in one type
`Dir n p` of directions, with an extra direction `Dir.self` whose "derivative" is the identity.
`Dir n p` also indexes the slots of a prolonged unknown (`PDE/Prolong`):
`W = (V, ∂_{y₁}V, …, ∂_{yₙ}V, ∂ₜV, ∂_{l₁}V, …, ∂_{l_p}V)`.

For a direction `s ≠ self`, `s.d U l t y` is the derivative of `↿U` at `(l, t, y)` along the
coordinate vector `s.vec` (`Dir.d_eq_fderiv`), so partial derivatives of smooth families commute
(`Dir.d_comm`), and obey the Leibniz rules `Dir.d_add`, `Dir.d_sum`, `Dir.d_smul`, `Dir.d_mul`,
`Dir.d_inner`, `Dir.d_clm_apply`. In the Leibniz rules the derivative of a coefficient is
`Dir.dc`, which is `0` for `self` (so that `self.d (f • u) = self.dc f • u + f • self.d u`).
-/

namespace LorentzianCalderon.PDE

noncomputable section
open scoped ContDiff RealInnerProductSpace Topology
open Set Function Real

variable {n p : ℕ}

/-- The directions of partial derivatives, and the slots of a prolonged unknown: `self` (no
derivative), `space i` (`∂/∂yᵢ`), `time` (`∂/∂t`) and `param k` (`∂/∂lₖ`). -/
inductive Dir (n p : ℕ) where
  | self
  | space (i : Fin n)
  | time
  | param (k : Fin p)
  deriving Fintype, DecidableEq

@[simp] theorem uncurry_apply_triple {α β γ X : Type*} (V : α → β → γ → X) (a : α) (b : β)
    (c : γ) : (↿V) (a, b, c) = V a b c := rfl

namespace Dir

/-- The coordinate vector of a direction in `(l, t, y)`-space; `0` for `self`. -/
def vec : Dir n p → (Fin p → ℝ) × ℝ × (Fin n → ℝ)
  | self => 0
  | space i => (0, 0, Pi.single i 1)
  | time => (0, 1, 0)
  | param k => (Pi.single k 1, 0, 0)

theorem vec_space (i : Fin n) : (space i : Dir n p).vec = (0, 0, Pi.single i 1) := by rfl

theorem vec_time : (time : Dir n p).vec = (0, 1, 0) := by rfl

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The partial derivative in direction `s`: `dy i`, `dt`, `dpar k`, or the identity for
`self`. -/
def d : Dir n p → ((Fin p → ℝ) → ℝ → (Fin n → ℝ) → X) → (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X
  | self, V => V
  | space i, V => dy i V
  | time, V => dt V
  | param k, V => dpar k V

/-- The derivative of a coefficient in direction `s`: `s.d f`, but `0` for `s = self`. -/
def dc : Dir n p → ((Fin p → ℝ) → ℝ → (Fin n → ℝ) → X) → (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X
  | self, _ => 0
  | space i, V => dy i V
  | time, V => dt V
  | param k, V => dpar k V

@[simp] theorem d_self (V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X) :
    (self : Dir n p).d V = V := by rfl

@[simp] theorem d_space (i : Fin n) (V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X) :
    (space i : Dir n p).d V = dy i V := by rfl

@[simp] theorem d_time (V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X) :
    (time : Dir n p).d V = dt V := by rfl

@[simp] theorem d_param (k : Fin p) (V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X) :
    (param k : Dir n p).d V = dpar k V := by rfl

@[simp] theorem dc_self (V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X) :
    (self : Dir n p).dc V = 0 := by rfl

theorem dc_eq_d {s : Dir n p} (hs : s ≠ self) (V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X) :
    s.dc V = s.d V := by
  cases s <;> first | exact (hs rfl).elim | rfl

theorem _root_.LorentzianCalderon.PDE.IsPeriodicSmooth.d {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X} (hV : IsPeriodicSmooth V)
    (s : Dir n p) : IsPeriodicSmooth (s.d V) := by
  cases s
  · exact hV
  · exact hV.dy _
  · exact hV.dt
  · exact hV.dpar _

theorem _root_.LorentzianCalderon.PDE.IsPeriodicSmooth.dc {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X} (hV : IsPeriodicSmooth V)
    (s : Dir n p) : IsPeriodicSmooth (s.dc V) := by
  cases s
  · exact ⟨contDiff_const, fun _ _ => isPeriodic_iff.2 fun _ _ => rfl⟩
  · exact hV.dy _
  · exact hV.dt
  · exact hV.dpar _

/-- For `s ≠ self`, `s.d U` is the derivative of `↿U` along `s.vec`. -/
theorem d_eq_fderiv {s : Dir n p} (hs : s ≠ self) {U : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X}
    (hU : Differentiable ℝ ↿U) (l : Fin p → ℝ) (t : ℝ) (y : Fin n → ℝ) :
    s.d U l t y = fderiv ℝ ↿U (l, t, y) s.vec := by
  cases s with
  | self => exact (hs rfl).elim
  | space i =>
    have h : HasFDerivAt (fun y' : Fin n → ℝ => (l, t, y'))
        ((ContinuousLinearMap.inr ℝ (Fin p → ℝ) (ℝ × (Fin n → ℝ))).comp
          (ContinuousLinearMap.inr ℝ ℝ (Fin n → ℝ))) y :=
      (hasFDerivAt_prodMk_right l (t, y)).comp y (hasFDerivAt_prodMk_right t y)
    rw [d_space, dy_apply]
    show fderiv ℝ (↿U ∘ fun y' : Fin n → ℝ => (l, t, y')) y (Pi.single i 1) = _
    rw [((hU _).hasFDerivAt.comp y h).fderiv]
    rfl
  | time =>
    have h : HasDerivAt (fun s : ℝ => (l, s, y)) ((0 : Fin p → ℝ), (1 : ℝ), (0 : Fin n → ℝ)) t :=
      (hasDerivAt_const t l).prodMk ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))
    rw [d_time, dt_apply]
    show deriv (↿U ∘ fun s : ℝ => (l, s, y)) t = _
    rw [((hU _).hasFDerivAt.comp_hasDerivAt t h).deriv]
    rfl
  | param k =>
    rw [d_param, dpar_apply]
    show fderiv ℝ (↿U ∘ fun m : Fin p → ℝ => (m, t, y)) l (Pi.single k 1) = _
    rw [((hU _).hasFDerivAt.comp l (hasFDerivAt_prodMk_left l (t, y))).fderiv]
    rfl

theorem uncurry_d {s : Dir n p} (hs : s ≠ self) {U : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X}
    (hU : Differentiable ℝ ↿U) : ↿(s.d U) = fun z => fderiv ℝ ↿U z s.vec := by
  funext z
  exact d_eq_fderiv hs hU z.1 z.2.1 z.2.2

theorem contDiff_d {U : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X} (hU : ContDiff ℝ ∞ ↿U)
    (s : Dir n p) : ContDiff ℝ ∞ ↿(s.d U) := by
  by_cases hs : s = self
  · subst hs; exact hU
  rw [uncurry_d hs (hU.differentiable (by simp))]
  exact (hU.fderiv_right (by simp)).clm_apply contDiff_const

/-- The derivative along the line through `(l, t, y)` in direction `s.vec`. -/
theorem hasDerivAt_line {s : Dir n p} (hs : s ≠ self) {U : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X}
    (hU : Differentiable ℝ ↿U) (l : Fin p → ℝ) (t : ℝ) (y : Fin n → ℝ) :
    HasDerivAt (fun x : ℝ => ↿U ((l, t, y) + x • s.vec)) (s.d U l t y) 0 := by
  rw [d_eq_fderiv hs hU]
  have hγ : HasDerivAt (fun x : ℝ => (l, t, y) + x • s.vec) s.vec 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const s.vec).const_add (l, t, y)
  exact (hU _).hasFDerivAt.comp_hasDerivAt_of_eq 0 hγ (by simp)

theorem d_eq_deriv {s : Dir n p} (hs : s ≠ self) {U : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X}
    (hU : Differentiable ℝ ↿U) (l : Fin p → ℝ) (t : ℝ) (y : Fin n → ℝ) :
    s.d U l t y = deriv (fun x : ℝ => ↿U ((l, t, y) + x • s.vec)) 0 :=
  (hasDerivAt_line hs hU l t y).deriv.symm

theorem d_eq_of_hasDerivAt {s : Dir n p} (hs : s ≠ self)
    {U : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X} (hU : Differentiable ℝ ↿U) {l : Fin p → ℝ} {t : ℝ}
    {y : Fin n → ℝ} {v : X} (h : HasDerivAt (fun x : ℝ => ↿U ((l, t, y) + x • s.vec)) v 0) :
    s.d U l t y = v :=
  (d_eq_deriv hs hU l t y).trans h.deriv

/-- Partial derivatives of a smooth family commute. -/
theorem d_comm {U : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X} (hU : ContDiff ℝ ∞ ↿U) (s s' : Dir n p) :
    s.d (s'.d U) = s'.d (s.d U) := by
  by_cases hs : s = self
  · subst hs; rfl
  by_cases hs' : s' = self
  · subst hs'; rfl
  have hd := hU.differentiable (by simp)
  have hf : ContDiff ℝ ∞ (fderiv ℝ ↿U) := hU.fderiv_right (by simp)
  have hd' : ∀ v, Differentiable ℝ fun z => fderiv ℝ ↿U z v := fun v =>
    (hf.clm_apply contDiff_const).differentiable (by simp)
  have key : ∀ (v w) z, fderiv ℝ (fun z => fderiv ℝ ↿U z w) z v =
      fderiv ℝ (fderiv ℝ ↿U) z v w := fun v w z => by
    rw [fderiv_clm_apply (hf.differentiable (by simp) z) (differentiableAt_const w)]
    simp
  funext l t y
  rw [d_eq_fderiv hs (by rw [uncurry_d hs' hd]; exact hd' _),
    d_eq_fderiv hs' (by rw [uncurry_d hs hd]; exact hd' _), uncurry_d hs' hd, uncurry_d hs hd,
    key, key]
  exact (hU.contDiffAt.isSymmSndFDerivAt (by simp)) _ _

/-! ## Leibniz rules -/

section Leibniz

variable {s : Dir n p} {l : Fin p → ℝ} {t : ℝ} {y : Fin n → ℝ}

theorem d_add {U W : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X} (hU : Differentiable ℝ ↿U)
    (hW : Differentiable ℝ ↿W) :
    s.d (fun l t y => U l t y + W l t y) l t y = s.d U l t y + s.d W l t y := by
  by_cases hs : s = self
  · subst hs; rfl
  rw [d_eq_deriv hs (hU.add hW)]
  exact ((hasDerivAt_line hs hU l t y).add (hasDerivAt_line hs hW l t y)).deriv

theorem d_sub {U W : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X} (hU : Differentiable ℝ ↿U)
    (hW : Differentiable ℝ ↿W) :
    s.d (fun l t y => U l t y - W l t y) l t y = s.d U l t y - s.d W l t y := by
  by_cases hs : s = self
  · subst hs; rfl
  rw [d_eq_deriv hs (hU.sub hW)]
  exact ((hasDerivAt_line hs hU l t y).sub (hasDerivAt_line hs hW l t y)).deriv

theorem d_sum {κ : Type*} (S : Finset κ) {U : κ → (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X}
    (hU : ∀ k, Differentiable ℝ ↿(U k)) :
    s.d (fun l t y => ∑ k ∈ S, U k l t y) l t y = ∑ k ∈ S, s.d (U k) l t y := by
  by_cases hs : s = self
  · subst hs; rfl
  have hd : Differentiable ℝ fun z : (Fin p → ℝ) × ℝ × (Fin n → ℝ) => ∑ k ∈ S, ↿(U k) z :=
    Differentiable.fun_sum fun k _ => hU k
  rw [d_eq_deriv hs hd]
  exact (HasDerivAt.fun_sum fun k _ => hasDerivAt_line hs (hU k) l t y).deriv

theorem d_smul {f : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → ℝ} {U : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X}
    (hf : Differentiable ℝ ↿f) (hU : Differentiable ℝ ↿U) :
    s.d (fun l t y => f l t y • U l t y) l t y =
      s.dc f l t y • U l t y + f l t y • s.d U l t y := by
  by_cases hs : s = self
  · subst hs; simp
  rw [d_eq_deriv hs (hf.smul hU), dc_eq_d hs]
  have h := (hasDerivAt_line hs hf l t y).fun_smul (hasDerivAt_line hs hU l t y)
  simp only [zero_smul, add_zero] at h
  exact h.deriv.trans (add_comm _ _)

theorem d_mul {f g : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → ℝ} (hf : Differentiable ℝ ↿f)
    (hg : Differentiable ℝ ↿g) :
    s.d (fun l t y => f l t y * g l t y) l t y =
      s.dc f l t y * g l t y + f l t y * s.d g l t y :=
  d_smul hf hg

theorem d_inner (hs : s ≠ self) {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {U W : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → E} (hU : Differentiable ℝ ↿U)
    (hW : Differentiable ℝ ↿W) :
    s.d (fun l t y => ⟪U l t y, W l t y⟫) l t y =
      ⟪s.d U l t y, W l t y⟫ + ⟪U l t y, s.d W l t y⟫ := by
  rw [d_eq_deriv hs (hU.inner ℝ hW)]
  have h := (hasDerivAt_line hs hU l t y).inner ℝ (hasDerivAt_line hs hW l t y)
  simp only [zero_smul, add_zero] at h
  exact h.deriv.trans (add_comm _ _)

theorem d_clm_apply {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {L : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → E →L[ℝ] G} {U : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → E}
    (hL : Differentiable ℝ ↿L) (hU : Differentiable ℝ ↿U) :
    s.d (fun l t y => L l t y (U l t y)) l t y =
      s.dc L l t y (U l t y) + L l t y (s.d U l t y) := by
  by_cases hs : s = self
  · subst hs; simp
  rw [d_eq_deriv hs (hL.clm_apply hU), dc_eq_d hs]
  have h := (hasDerivAt_line hs hL l t y).clm_apply (hasDerivAt_line hs hU l t y)
  simp only [zero_smul, add_zero] at h
  exact h.deriv

theorem d_clm_const {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] G)
    {U : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → E} (hU : Differentiable ℝ ↿U) :
    s.d (fun l t y => L (U l t y)) l t y = L (s.d U l t y) := by
  by_cases hs : s = self
  · subst hs; rfl
  exact d_eq_of_hasDerivAt hs (L.differentiable.comp hU)
    (L.hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_line hs hU l t y))

end Leibniz

theorem d_dy {U : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X} (hU : ContDiff ℝ ∞ ↿U) (s : Dir n p)
    (i : Fin n) : s.d (dy i U) = dy i (s.d U) :=
  d_comm hU s (space i)

theorem d_dt {U : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → X} (hU : ContDiff ℝ ∞ ↿U) (s : Dir n p) :
    s.d (dt U) = dt (s.d U) :=
  d_comm hU s time

end Dir

end

end LorentzianCalderon.PDE
