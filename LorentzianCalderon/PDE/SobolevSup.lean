module

public import LorentzianCalderon.PDE.FourierProj

public section

/-!
# Sup norms by `L²(cell)` norms of derivatives

For a smooth periodic `u : (Fin n → ℝ) → E`, `norm_le_sum_cellNorm` bounds `‖u y‖` by
`∑_{S ⊆ Fin n} ‖∂_S u‖_{L²(cell)}`, where `∂_S = pdSet S` differentiates once along each coordinate
in `S` (iterating the one-dimensional `|f y| ≤ ∫₀¹ |f| + ∫₀¹ |f'|`, then Cauchy–Schwarz).

For a smooth periodic family `V l t y` (`IsPeriodicSmooth`), `norm_iteratedFDeriv_le_sum` and
`norm_iteratedFDeriv_le_of_cellNorm_le` bound `‖D^k ↿V (l, t, y)‖`, the `k`-th derivative in all
variables, by `L²(cell)` norms of the slices at `(l, t)` of finitely many partial derivatives
`dWord w V` (words `w` in the directions `Axis p n`: `∂_{lₖ}`, `∂ₜ`, `∂_{yᵢ}`, of length
`≤ k + n`), uniformly in `y`.
-/

namespace LorentzianCalderon.PDE

noncomputable section
open scoped ContDiff Topology
open Set MeasureTheory Function Real

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## Iterated partial derivatives -/

/-- Iterated partial derivatives along the coordinates in a list: `pdList [] u = u` and
`pdList (i :: l) u = ∂ᵢ (pdList l u)`, so the head of the list is differentiated last. -/
def pdList : List (Fin n) → ((Fin n → ℝ) → E) → (Fin n → ℝ) → E
  | [], u => u
  | i :: l, u => fun y => fderiv ℝ (pdList l u) y (Pi.single i 1)

/-- The mixed partial derivative `∂_S u`, differentiating once along each coordinate in `S`
(in decreasing order of the coordinates). -/
def pdSet (S : Finset (Fin n)) (u : (Fin n → ℝ) → E) : (Fin n → ℝ) → E :=
  pdList (S.sort (· ≥ ·)) u

/-- Iterated partial derivatives of a smooth periodic function are smooth and periodic. -/
theorem pdList_smooth {u : (Fin n → ℝ) → E} (hu : ContDiff ℝ ∞ u) (hp : IsPeriodic u) :
    ∀ l : List (Fin n), ContDiff ℝ ∞ (pdList l u) ∧ IsPeriodic (pdList l u)
  | [] => ⟨hu, hp⟩
  | i :: l => by
    obtain ⟨h1, h2⟩ := pdList_smooth hu hp l
    refine ⟨(h1.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const,
      isPeriodic_iff.2 fun j y => ?_⟩
    simp only [pdList]
    rw [← fderiv_comp_add_right]
    congr 2
    funext y'
    exact h2.add_single j y'

/-- Adding a coordinate larger than all of `S` differentiates `∂_S u` once more, last. -/
theorem pdSet_insert {S : Finset (Fin n)} {a : Fin n} (ha : ∀ x ∈ S, x < a)
    (u : (Fin n → ℝ) → E) :
    pdSet (insert a S) u = fun y => fderiv ℝ (pdSet S u) y (Pi.single a 1) := by
  simp only [pdSet]
  rw [Finset.sort_insert (· ≥ ·) (fun b hb => (ha b hb).le) (fun h => lt_irrefl a (ha a h))]
  rfl

/-! ## Fubini on the cell along one coordinate -/

/-- Fubini on the cell, splitting off the coordinate `a`. -/
private theorem cellIntegral_eq_insertNth {m : ℕ} (a : Fin (m + 1))
    {F : (Fin (m + 1) → ℝ) → ℝ} (hF : Continuous F) :
    cellIntegral F = ∫ w, (∫ s, F (Fin.insertNth a s w) ∂(volume.restrict (Icc (0 : ℝ) 1)))
      ∂(Measure.pi fun _ : Fin m => volume.restrict (Icc (0 : ℝ) 1)) := by
  set μ₁ : Measure ℝ := volume.restrict (Icc 0 1)
  have hμ : volume.restrict (cell (m + 1)) = Measure.pi fun _ => μ₁ := by
    rw [cell_def, ← pi_univ_Icc, volume_pi, Measure.restrict_pi_pi]
    rfl
  have hmp := (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ₁) a).symm
  have hint : Integrable F (Measure.pi fun _ => μ₁) := by
    rw [← hμ]; exact integrableOn_cell hF
  rw [cellIntegral_def, hμ, ← hmp.integral_comp', integral_prod_symm]
  · rfl
  · exact (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hint

/-- Integrating `H (update z a s)` over `s ∈ [0, 1]` and then over the cell is `∫_cell H`. -/
theorem cellIntegral_integral_update {H : (Fin n → ℝ) → ℝ} (hH : Continuous H) (a : Fin n) :
    cellIntegral (fun z => ∫ s in Icc (0 : ℝ) 1, H (update z a s)) = cellIntegral H := by
  cases n with
  | zero => exact a.elim0
  | succ m =>
  have hG : Continuous fun z : Fin (m + 1) → ℝ => ∫ s in Icc (0 : ℝ) 1, H (update z a s) :=
    continuous_parametric_integral_of_continuous (f := fun z s => H (update z a s))
      (hH.comp (by fun_prop)) isCompact_Icc
  rw [cellIntegral_eq_insertNth a hG, cellIntegral_eq_insertNth a hH]
  congr 1
  funext w
  simp only [Fin.update_insertNth]
  rw [integral_const]
  simp [Measure.real]

/-! ## The one-dimensional estimate -/

/-- `‖g x‖ ≤ ∫₀¹ ‖g‖ + ∫₀¹ ‖∂ₐg‖` along the line through `x` in the direction `a`, for
periodic `C¹` `g`. -/
theorem norm_le_integral_update [CompleteSpace E] {g : (Fin n → ℝ) → E} (hg : ContDiff ℝ 1 g)
    (hp : IsPeriodic g) (a : Fin n) (x : Fin n → ℝ) :
    ‖g x‖ ≤ (∫ s in Icc (0 : ℝ) 1, ‖g (update x a s)‖) +
      ∫ s in Icc (0 : ℝ) 1, ‖fderiv ℝ g (update x a s) (Pi.single a 1)‖ := by
  set f : ℝ → E := fun s => g (update x a s)
  set f' : ℝ → E := fun s => fderiv ℝ g (update x a s) (Pi.single a 1)
  have hf : ∀ s, HasDerivAt f (f' s) s := fun s =>
    ((hg.differentiable one_ne_zero _).hasFDerivAt).comp_hasDerivAt s (hasDerivAt_update x a s)
  have hfc : Continuous f := hg.continuous.comp (by fun_prop)
  have hf'c : Continuous f' :=
    ((hg.continuous_fderiv one_ne_zero).comp (by fun_prop)).clm_apply continuous_const
  have hper : Periodic f 1 := fun s => by
    simp only [f]
    rw [show update x a (s + 1) = update x a s + Pi.single a 1 by
      funext j; by_cases h : j = a <;> simp [h]]
    exact hp.add_single a _
  set C := ∫ s in Icc (0 : ℝ) 1, ‖f' s‖
  have hstep : ∀ r ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ‖f r‖ ≤ ‖f s‖ + C := by
    intro r hr s hs
    have hint : ∫ τ in s..r, f' τ = f r - f s :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ => hf τ) (hf'c.intervalIntegrable _ _)
    have h1 : ‖f r - f s‖ ≤ C := by
      rw [← hint]
      refine (intervalIntegral.norm_integral_le_integral_norm_uIoc).trans ?_
      refine setIntegral_mono_set (hf'c.norm.integrableOn_Icc)
        (Filter.Eventually.of_forall fun _ => norm_nonneg _) (Filter.Eventually.of_forall ?_)
      intro τ hτ
      rcases hτ with ⟨h1, h2⟩
      exact ⟨(le_min hs.1 hr.1).trans h1.le, h2.trans (max_le hs.2 hr.2)⟩
    calc ‖f r‖ = ‖(f r - f s) + f s‖ := by rw [sub_add_cancel]
      _ ≤ ‖f r - f s‖ + ‖f s‖ := norm_add_le _ _
      _ ≤ ‖f s‖ + C := by linarith
  have hx : f (Int.fract (x a)) = g x := by
    rw [Int.fract, show x a - ⌊x a⌋ = x a - (⌊x a⌋ : ℤ) * 1 by ring, hper.sub_int_mul_eq]
    simp [f]
  have hfr : Int.fract (x a) ∈ Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  calc ‖g x‖ = ∫ _ in Icc (0 : ℝ) 1, ‖f (Int.fract (x a))‖ := by
        rw [setIntegral_const]; simp [hx]
    _ ≤ ∫ s in Icc (0 : ℝ) 1, (‖f s‖ + C) :=
        setIntegral_mono_on (integrableOn_const (by simp))
          ((hfc.norm.add continuous_const).integrableOn_Icc) measurableSet_Icc
          fun s hs => hstep _ hfr s hs
    _ = (∫ s in Icc (0 : ℝ) 1, ‖f s‖) + C := by
        rw [integral_add (hfc.norm.integrableOn_Icc)
          (integrableOn_const (by simp)), setIntegral_const]
        simp

/-! ## The sup bound -/

/-- Updating a coordinate outside `T` of `T.piecewise z y`. -/
theorem update_piecewise {T : Finset (Fin n)} {a : Fin n} (ha : a ∉ T) (z y : Fin n → ℝ)
    (s : ℝ) : update (T.piecewise z y) a s = (insert a T).piecewise (update z a s) y := by
  funext j
  by_cases hj : j = a
  · subst hj; simp
  · simp [Finset.piecewise, hj]

/-- `z ↦ T.piecewise z y` is continuous. -/
theorem continuous_piecewise_left (T : Finset (Fin n)) (y : Fin n → ℝ) :
    Continuous fun z : Fin n → ℝ => T.piecewise z y :=
  continuous_pi fun i => by
    simp only [Finset.piecewise]
    split_ifs
    · exact continuous_apply i
    · exact continuous_const

/-- **Sup bound**: `‖u y‖ ≤ ∑_{S ⊆ Fin n} ∫_cell ‖∂_S u‖` for periodic smooth `u`, by the
one-dimensional estimate `|f y| ≤ ∫₀¹ |f| + ∫₀¹ |f'|` in each coordinate. -/
theorem norm_le_sum_cellIntegral [CompleteSpace E] {u : (Fin n → ℝ) → E} (hu : ContDiff ℝ ∞ u)
    (hp : IsPeriodic u) (y : Fin n → ℝ) :
    ‖u y‖ ≤ ∑ S : Finset (Fin n), cellIntegral (fun z => ‖pdSet S u z‖) := by
  have hS : ∀ S : Finset (Fin n), ContDiff ℝ ∞ (pdSet S u) ∧ IsPeriodic (pdSet S u) :=
    fun S => pdList_smooth hu hp _
  have key : ∀ T : Finset (Fin n), ‖u y‖ ≤
      ∑ S ∈ T.powerset, cellIntegral (fun z => ‖pdSet S u (T.piecewise z y)‖) := by
    intro T
    induction T using Finset.induction_on_max with
    | empty => simp [pdSet, pdList, cellIntegral_const]
    | insert a T ha ih =>
      have haT : a ∉ T := fun h => lt_irrefl a (ha a h)
      rw [Finset.sum_powerset_insert haT, ← Finset.sum_add_distrib]
      refine ih.trans (Finset.sum_le_sum fun S hS' => ?_)
      have hST : ∀ x ∈ S, x < a := fun x hx => ha x (Finset.mem_powerset.1 hS' hx)
      rw [pdSet_insert hST]
      obtain ⟨hg, hgp⟩ := hS S
      have hg1 : ContDiff ℝ 1 (pdSet S u) := hg.of_le (by exact_mod_cast le_top)
      have hpw := continuous_piecewise_left (insert a T) y
      have hc1 : Continuous fun z => ‖pdSet S u ((insert a T).piecewise z y)‖ :=
        (hg.continuous.comp hpw).norm
      have hc2 : Continuous fun z =>
          ‖fderiv ℝ (pdSet S u) ((insert a T).piecewise z y) (Pi.single a 1)‖ :=
        (((hg1.continuous_fderiv one_ne_zero).comp hpw).clm_apply continuous_const).norm
      have hi : ∀ {H : (Fin n → ℝ) → ℝ}, Continuous H →
          IntegrableOn (fun z => ∫ s in Icc (0 : ℝ) 1, H (update z a s)) (cell n) := fun {H} hH =>
        integrableOn_cell (continuous_parametric_integral_of_continuous
          (f := fun z s => H (update z a s)) (hH.comp (by fun_prop)) isCompact_Icc)
      rw [← cellIntegral_integral_update hc1 a, ← cellIntegral_integral_update hc2 a,
        cellIntegral_def, cellIntegral_def, cellIntegral_def, ← integral_add (hi hc1) (hi hc2)]
      refine integral_mono (integrableOn_cell ((hg.continuous.comp
        (continuous_piecewise_left T y)).norm)) ((hi hc1).add (hi hc2)) fun z => ?_
      have := norm_le_integral_update hg1 hgp a (T.piecewise z y)
      simpa only [update_piecewise haT] using this
  simpa [Finset.piecewise_univ, Finset.powerset_univ] using key Finset.univ

omit [NormedSpace ℝ E] in
/-- `∫_cell ‖f‖ ≤ ‖f‖_{L²(cell)}` (Cauchy–Schwarz on the cell, which has volume `1`). -/
theorem cellIntegral_norm_le_cellNorm {f : (Fin n → ℝ) → E} (hf : Continuous f) :
    cellIntegral (fun y => ‖f y‖) ≤ cellNorm f := by
  set c := cellIntegral (fun y => ‖f y‖)
  have hc : 0 ≤ c := by
    simp only [c, cellIntegral_def]
    exact integral_nonneg fun y => norm_nonneg _
  have h0 : 0 ≤ cellIntegral (fun y => (‖f y‖ - c) ^ 2) := by
    rw [cellIntegral_def]
    exact integral_nonneg fun y => sq_nonneg _
  have e : cellIntegral (fun y => (‖f y‖ - c) ^ 2) = cellIntegral (fun y => ‖f y‖ ^ 2) - c ^ 2 := by
    have : (fun y => (‖f y‖ - c) ^ 2) = fun y => ‖f y‖ ^ 2 - 2 * c * ‖f y‖ + c ^ 2 := by
      funext y; ring
    rw [this, cellIntegral_def, integral_add (integrableOn_cell (by fun_prop))
      (integrableOn_cell continuous_const), integral_sub (integrableOn_cell (by fun_prop))
      (integrableOn_cell (by fun_prop)), integral_const_mul, setIntegral_const]
    simp only [Measure.real, volume_cell, smul_eq_mul]
    simp only [cellIntegral_def, c]
    simp
    ring
  rw [cellNorm_def]
  exact (Real.le_sqrt hc (by rw [cellIntegral_def]; exact integral_nonneg fun y => sq_nonneg _)).2
    (sub_nonneg.1 (e ▸ h0))

/-- **Sup bound** in `L²(cell)` norms: `‖u y‖ ≤ ∑_{S ⊆ Fin n} ‖∂_S u‖_{L²(cell)}`. -/
theorem norm_le_sum_cellNorm [CompleteSpace E] {u : (Fin n → ℝ) → E} (hu : ContDiff ℝ ∞ u)
    (hp : IsPeriodic u) (y : Fin n → ℝ) :
    ‖u y‖ ≤ ∑ S : Finset (Fin n), cellNorm (pdSet S u) :=
  (norm_le_sum_cellIntegral hu hp y).trans (Finset.sum_le_sum fun _ _ =>
    cellIntegral_norm_le_cellNorm (pdList_smooth hu hp _).1.continuous)

/-! ## Families: all partial derivatives in `(l, t, y)` -/

section Families

variable {p : ℕ}

/-- The directions of the partial derivatives of a family `V l t y`: `Sum.inl k` is `∂_{lₖ}`,
`Sum.inr (Sum.inl ())` is `∂ₜ` and `Sum.inr (Sum.inr i)` is `∂_{yᵢ}`. -/
abbrev Axis (p n : ℕ) := Fin p ⊕ Unit ⊕ Fin n

/-- The partial derivative of a family in the direction `d`. -/
def dDir (d : Axis p n) (V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → E) :
    (Fin p → ℝ) → ℝ → (Fin n → ℝ) → E :=
  match d with
  | .inl k => dpar k V
  | .inr (.inl _) => dt V
  | .inr (.inr i) => dy i V

/-- Iterated partial derivatives of a family along a word of directions; the head of the word is
differentiated last. -/
def dWord : List (Axis p n) → ((Fin p → ℝ) → ℝ → (Fin n → ℝ) → E) →
    (Fin p → ℝ) → ℝ → (Fin n → ℝ) → E
  | [], V => V
  | d :: w, V => dDir d (dWord w V)

theorem dDir_inl (k : Fin p) (V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → E) :
    dDir (.inl k) V = dpar k V := by rfl

theorem dDir_inr_inl (u : Unit) (V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → E) :
    dDir (.inr (.inl u)) V = dt V := by rfl

theorem dDir_inr_inr (i : Fin n) (V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → E) :
    dDir (.inr (.inr i)) V = dy i V := by rfl

theorem dWord_nil (V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → E) : dWord [] V = V := by rfl

theorem dWord_cons (d : Axis p n) (w : List (Axis p n)) (V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → E) :
    dWord (d :: w) V = dDir d (dWord w V) := by rfl

/-- `dWord` turns concatenation into composition. -/
theorem dWord_append (w w' : List (Axis p n)) (V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → E) :
    dWord (w ++ w') V = dWord w (dWord w' V) := by
  induction w with
  | nil => rfl
  | cons d w ih => simp only [List.cons_append, dWord, ih]

/-- Smooth periodic families are closed under `dDir`. -/
theorem IsPeriodicSmooth.dDir {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → E}
    (hV : IsPeriodicSmooth V) (d : Axis p n) : IsPeriodicSmooth (dDir d V) := by
  rcases d with k | _ | i
  exacts [hV.dpar k, hV.dt, hV.dy i]

/-- Smooth periodic families are closed under `dWord`. -/
theorem IsPeriodicSmooth.dWord {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → E}
    (hV : IsPeriodicSmooth V) : ∀ w : List (Axis p n), IsPeriodicSmooth (PDE.dWord w V)
  | [] => hV
  | d :: w => (hV.dWord w).dDir d

/-- `∂_{y_L}` of a slice is the slice of the family derivative along the word `L`. -/
theorem pdList_slice (W : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → E) :
    ∀ (L : List (Fin n)) (l : Fin p → ℝ) (t : ℝ),
      pdList L (W l t) = dWord (L.map fun i => Sum.inr (Sum.inr i)) W l t
  | [], _, _ => rfl
  | i :: L, l, t => by
    funext y
    simp only [pdList, List.map_cons, dWord, dDir, PDE.dy_def]
    rw [pdList_slice W L l t]

/-- The coordinate vector of the direction `d` in `(Fin p → ℝ) × ℝ × (Fin n → ℝ)`. -/
def dirVec : Axis p n → (Fin p → ℝ) × ℝ × (Fin n → ℝ)
  | .inl k => (Pi.single k 1, 0, 0)
  | .inr (.inl _) => (0, 1, 0)
  | .inr (.inr i) => (0, 0, Pi.single i 1)

/-- The coordinate of `v` in the direction `d`. -/
def dirCoord : Axis p n → (Fin p → ℝ) × ℝ × (Fin n → ℝ) → ℝ
  | .inl k, v => v.1 k
  | .inr (.inl _), v => v.2.1
  | .inr (.inr i), v => v.2.2 i

/-- Every vector is the combination of the coordinate vectors with its coordinates. -/
theorem sum_dirCoord_smul (v : (Fin p → ℝ) × ℝ × (Fin n → ℝ)) :
    ∑ d : Axis p n, dirCoord d v • dirVec d = v := by
  rcases v with ⟨a, b, c⟩
  refine Prod.ext (funext fun k => ?_) (Prod.ext ?_ (funext fun i => ?_)) <;>
    simp [Fintype.sum_sum_type, dirCoord, dirVec, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply,
      Pi.single_apply]

/-- Coordinates are bounded by the (sup) norm. -/
theorem abs_dirCoord_le (d : Axis p n) (v : (Fin p → ℝ) × ℝ × (Fin n → ℝ)) :
    |dirCoord d v| ≤ ‖v‖ := by
  rcases d with k | _ | i
  · exact (norm_le_pi_norm v.1 k).trans (norm_fst_le v)
  · exact (norm_fst_le v.2).trans (norm_snd_le v)
  · exact ((norm_le_pi_norm v.2.2 i).trans (norm_snd_le v.2)).trans (norm_snd_le v)

/-- The norm of a multilinear map on `(Fin p → ℝ) × ℝ × (Fin n → ℝ)` is at most the sum of its
values on tuples of coordinate vectors. -/
theorem norm_le_sum_dirVec {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {k : ℕ}
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin k => (Fin p → ℝ) × ℝ × (Fin n → ℝ)) G) :
    ‖M‖ ≤ ∑ w : Fin k → Axis p n, ‖M fun j => dirVec (w j)‖ := by
  refine M.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun m => ?_
  have hm : m = fun j => ∑ d, dirCoord d (m j) • dirVec d :=
    funext fun j => (sum_dirCoord_smul _).symm
  conv_lhs => rw [hm, M.map_sum]
  simp only [M.map_smul_univ]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun w _ => ?_
  rw [norm_smul, Real.norm_eq_abs, Finset.abs_prod, mul_comm]
  exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun j _ => abs_nonneg _)
    fun j _ => abs_dirCoord_le _ _) (norm_nonneg _)

/-- Iterated directional derivatives: `dirDeriv [] f = f` and
`dirDeriv (v :: vs) f = ∂_v (dirDeriv vs f)`. -/
def dirDeriv {X G : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup G]
    [NormedSpace ℝ G] : List X → (X → G) → X → G
  | [], f => f
  | v :: vs, f => fun x => fderiv ℝ (dirDeriv vs f) x v

/-- The `k`-th derivative applied to `m` is the iterated directional derivative along `m`. -/
theorem iteratedFDeriv_eq_dirDeriv {X G : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : X → G} (hf : ContDiff ℝ ∞ f) :
    ∀ (k : ℕ) (m : Fin k → X) (x : X), iteratedFDeriv ℝ k f x m = dirDeriv (List.ofFn m) f x
  | 0, m, x => by simp [dirDeriv]
  | k + 1, m, x => by
    rw [iteratedFDeriv_succ_apply_left, ← fderiv_continuousMultilinear_apply_const_apply
      ((hf.differentiable_iteratedFDeriv (mod_cast ENat.natCast_lt_top k)) x),
      List.ofFn_succ]
    simp only [dirDeriv]
    congr 2
    funext y
    exact iteratedFDeriv_eq_dirDeriv hf k _ y

/-- The family derivative `dDir d` is the derivative of `↿V` along `dirVec d`. -/
theorem uncurry_dDir {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → E} (hV : Differentiable ℝ ↿V)
    (d : Axis p n) (x : (Fin p → ℝ) × ℝ × (Fin n → ℝ)) :
    ↿(dDir d V) x = fderiv ℝ ↿V x (dirVec d) := by
  rcases x with ⟨l, t, y⟩
  rcases d with k | ⟨⟨⟩⟩ | i
  · have h := ((hV (l, t, y)).hasFDerivAt.comp l (hasFDerivAt_prodMk_left (𝕜 := ℝ) l (t, y)))
    rw [show ↿(dDir (Sum.inl k) V) (l, t, y) = dpar k V l t y from rfl, dpar_apply]
    rw [show (fun m => V m t y) = ↿V ∘ fun m => (m, (t, y)) from rfl, h.fderiv]
    rfl
  · have h : HasDerivAt (fun s : ℝ => ((l, s, y) : (Fin p → ℝ) × ℝ × (Fin n → ℝ))) (0, 1, 0) t :=
      (hasDerivAt_const t l).prodMk ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))
    have h' := (hV (l, t, y)).hasFDerivAt.comp_hasDerivAt t h
    rw [show ↿(dDir (Sum.inr (Sum.inl ())) V) (l, t, y) = dt V l t y from rfl, dt_apply]
    rw [show (fun s => V l s y) = ↿V ∘ fun s => (l, s, y) from rfl, h'.deriv]
    rfl
  · have h := ((hV (l, t, y)).hasFDerivAt.comp y
      ((hasFDerivAt_prodMk_right (𝕜 := ℝ) l (t, y)).comp y
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) t y)))
    rw [show ↿(dDir (Sum.inr (Sum.inr i)) V) (l, t, y) = dy i V l t y from rfl, dy_apply]
    rw [show V l t = ↿V ∘ (fun f => (l, f)) ∘ Prod.mk t from rfl, h.fderiv]
    rfl

/-- `dWord w` is the iterated derivative of `↿V` along the vectors of `w`. -/
theorem uncurry_dWord [CompleteSpace E] {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → E}
    (hV : IsPeriodicSmooth V) : ∀ w : List (Axis p n), ↿(dWord w V) = dirDeriv (w.map dirVec) ↿V
  | [] => rfl
  | d :: w => funext fun x => by
    simp only [dWord, List.map_cons, dirDeriv]
    rw [uncurry_dDir ((hV.dWord w).smooth.differentiable (by simp)) d x, uncurry_dWord hV w]

/-- **`C^k` bound by `L²(cell)` norms**: every `k`-th derivative of a smooth periodic family in
all its variables `(l, t, y)` is bounded at `(l, t, y)` by `L²(cell)` norms of finitely many
partial derivatives `∂_S ∂_w V` of the slice at `(l, t)` (`w` a word of `k` directions,
`S ⊆ Fin n`). -/
theorem norm_iteratedFDeriv_le_sum [CompleteSpace E] {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → E}
    (hV : IsPeriodicSmooth V) (k : ℕ) (l : Fin p → ℝ) (t : ℝ) (y : Fin n → ℝ) :
    ‖iteratedFDeriv ℝ k ↿V (l, t, y)‖ ≤
      ∑ w : Fin k → Axis p n, ∑ S : Finset (Fin n),
        cellNorm (pdSet S (dWord (List.ofFn w) V l t)) := by
  refine (norm_le_sum_dirVec _).trans (Finset.sum_le_sum fun w _ => ?_)
  have e : List.ofFn (fun j => dirVec (w j)) = (List.ofFn w).map dirVec := by
    rw [List.map_ofFn]; rfl
  rw [iteratedFDeriv_eq_dirDeriv hV.smooth, e, ← uncurry_dWord hV]
  exact norm_le_sum_cellNorm ((hV.dWord _).contDiff_slice l t) ((hV.dWord _).periodic l t) y

/-- **`C^k` bound by `L²(cell)` norms**, uniform form: if all derivatives `dWord w V` with
`|w| ≤ k + n` have `L²(cell)` norm `≤ ε` at `(l, t)`, then
`‖D^k V (l, t, y)‖ ≤ (p + 1 + n)^k 2^n ε` for all `y`. -/
theorem norm_iteratedFDeriv_le_of_cellNorm_le [CompleteSpace E]
    {V : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → E} (hV : IsPeriodicSmooth V) (k : ℕ)
    {l : Fin p → ℝ} {t ε : ℝ}
    (hε : ∀ w : List (Axis p n), w.length ≤ k + n → cellNorm (dWord w V l t) ≤ ε)
    (y : Fin n → ℝ) :
    ‖iteratedFDeriv ℝ k ↿V (l, t, y)‖ ≤ (p + 1 + n) ^ k * 2 ^ n * ε := by
  refine (norm_iteratedFDeriv_le_sum hV k l t y).trans ?_
  calc _ ≤ ∑ _w : Fin k → Axis p n, ∑ _S : Finset (Fin n), ε :=
        Finset.sum_le_sum fun w _ => Finset.sum_le_sum fun S _ => by
          rw [pdSet, pdList_slice, ← dWord_append]
          refine hε _ ?_
          simp only [List.length_append, List.length_map, Finset.length_sort, List.length_ofFn]
          have := S.card_le_univ
          simp only [Fintype.card_fin] at this
          omega
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fun,
          Fintype.card_sum, Fintype.card_unit, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

end Families

end

end LorentzianCalderon.PDE
