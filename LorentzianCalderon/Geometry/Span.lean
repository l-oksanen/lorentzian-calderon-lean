module

public import LorentzianCalderon.Causal.Form

public section

/-!
# Null covectors in an open set span

Blueprint lemma `lem_span`. Let `A` be a Lorentzian scalar product on `ℝ^{1+n}`, `n ≥ 2`.
Covectors `ξ` are null if `A⁻¹(ξ, ξ) = 0`. The null covectors in a nonempty relatively open
subset of the null cone span the covectors (`IsLorentzian.span_nullCovectors`), and their outer
products `ξ ξᵀ` together with `A` span the symmetric matrices
(`IsLorentzian.mem_span_nullCovectors`). Finitely many of them already do both
(`IsLorentzian.exists_finset_null_span`).

The proof writes `A = Pᵀ η P` with `η` the Minkowski matrix, propagates the vanishing of a
quadratic form from an open piece of the null cone to the whole cone by the identity theorem for
analytic functions, and tests the result on explicit null vectors.
-/

namespace LorentzianCalderon

open Matrix

variable {n : ℕ}

theorem IsLorentzian.isHermitian {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : IsLorentzian A) : A.IsHermitian := by
  simpa [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial] using hA.symm

/-- A Lorentzian matrix has at most one nonpositive eigenvalue. -/
theorem IsLorentzian.eigenvalues_pos_of_ne {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : IsLorentzian A) {i j : Fin (n + 1)} (hij : i ≠ j)
    (hi : hA.isHermitian.eigenvalues i ≤ 0) : 0 < hA.isHermitian.eigenvalues j := by
  by_contra! hj
  obtain ⟨V, hV⟩ := hA.spacelike
  set u := hA.isHermitian.eigenvectorBasis
  set μ := hA.isHermitian.eigenvalues
  have hli : LinearIndependent ℝ ![u i, u j] := by
    have := u.orthonormal.linearIndependent.comp ![i, j] (by
      intro a b; fin_cases a <;> fin_cases b <;> simp [hij, hij.symm])
    convert this using 1
    ext k : 1
    fin_cases k <;> rfl
  let W : Submodule ℝ (E n) := Submodule.span ℝ (Set.range ![u i, u j])
  have hW : Module.finrank ℝ W = 2 := by simp [W, finrank_span_eq_card hli]
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq V W
  have hle : Module.finrank ℝ ↥(V ⊔ W) ≤ n + 1 := by
    simpa using Submodule.finrank_le (V ⊔ W)
  have hne : V ⊓ W ≠ ⊥ := by
    intro h
    rw [h, finrank_bot, hV.finrank_eq, hW] at hsum
    omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp (Submodule.mem_inf.mp hx).2
  have hpos := hV.pos _ (Submodule.mem_inf.mp hx).1 hx0
  have hdot : ∀ k l, (u k).ofLp ⬝ᵥ (u l).ofLp = if k = l then 1 else 0 := by
    intro k l
    have := orthonormal_iff_ite.mp u.orthonormal k l
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm] at this
    exact this
  have hev : ∀ k, A *ᵥ (u k).ofLp = μ k • (u k).ofLp := hA.isHermitian.mulVec_eigenvectorBasis
  rw [form_eq_dotProduct] at hpos
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, WithLp.ofLp_add,
    WithLp.ofLp_smul, mulVec_add, mulVec_smul, hev,
    dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct, hdot, smul_eq_mul,
    ↓reduceIte, hij, hij.symm, mul_one, mul_zero, add_zero, zero_add] at hpos
  nlinarith [mul_nonneg (sq_nonneg (c 0)) (neg_nonneg.mpr hi),
    mul_nonneg (sq_nonneg (c 1)) (neg_nonneg.mpr hj)]

/-- A Lorentzian matrix is congruent to the Minkowski matrix. -/
theorem IsLorentzian.exists_eq_transpose_mul_minkowski_mul
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hA : IsLorentzian A) :
    ∃ P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ, A = Pᵀ * minkowski n * P := by
  have hH := hA.isHermitian
  set μ := hH.eigenvalues
  set u := hH.eigenvectorBasis
  obtain ⟨i₀, hi₀⟩ : ∃ i, μ i < 0 := by
    by_contra! h
    have hdet := hH.det_eq_prod_eigenvalues
    simp only [RCLike.ofReal_real_eq_id, id] at hdet
    have : 0 ≤ A.det := hdet ▸ Finset.prod_nonneg fun i _ => h i
    linarith [hA.det_neg]
  have hpos : ∀ j, j ≠ i₀ → 0 < μ j := fun j hj => hA.eigenvalues_pos_of_ne (Ne.symm hj) hi₀.le
  have hspec : ∀ a b, A a b = ∑ i, μ i * (u i a * u i b) := by
    intro a b
    conv_lhs => rw [hH.spectral_theorem]
    simp only [Unitary.conjStarAlgAut_apply, mul_apply, star_apply, diagonal_apply,
      Function.comp_apply, RCLike.ofReal_real_eq_id, id, star_trivial,
      IsHermitian.eigenvectorUnitary_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte]
    exact Finset.sum_congr rfl fun x _ => by ring
  let σ := Equiv.swap (0 : Fin (n + 1)) i₀
  refine ⟨Matrix.of fun k l => √|μ (σ k)| * u (σ k) l, ?_⟩
  ext a b
  rw [hspec, minkowski_def, mul_apply]
  simp only [mul_diagonal, transpose_apply, of_apply]
  rw [← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hs : √|μ (σ i)| * √|μ (σ i)| = |μ (σ i)| := Real.mul_self_sqrt (abs_nonneg _)
  by_cases hi : i = 0
  · subst hi
    rw [show σ 0 = i₀ from Equiv.swap_apply_left _ _, abs_of_neg hi₀] at hs ⊢
    simp only [↓reduceIte]
    linear_combination (u i₀ a * u i₀ b) * hs
  · have hσ : σ i ≠ i₀ := by
      simpa [σ, Equiv.swap_apply_eq_iff] using hi
    rw [abs_of_pos (hpos _ hσ)] at hs ⊢
    simp only [hi, ↓reduceIte]
    linear_combination (-(u (σ i) a * u (σ i) b)) * hs

/-! ### The Minkowski null cone -/

theorem minkowski_apply (a b : Fin (n + 1)) :
    minkowski n a b = if a = b then (if a = 0 then -1 else 1) else 0 := by
  simp [minkowski_def, diagonal_apply]

theorem minkowski_mulVec_apply (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    (minkowski n *ᵥ x) i = (if i = 0 then -1 else 1) * x i := by
  simp [minkowski_def, mulVec_diagonal]

theorem dotProduct_minkowski_mulVec_self (x : Fin (n + 1) → ℝ) :
    x ⬝ᵥ (minkowski n *ᵥ x) = -x 0 ^ 2 + ∑ i : Fin n, x i.succ ^ 2 := by
  simp [dotProduct, minkowski_mulVec_apply, Fin.sum_univ_succ, Fin.succ_ne_zero, sq]

theorem single_add_single_dotProduct_mulVec (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (a b : Fin (n + 1)) (p q : ℝ) :
    (Pi.single a p + Pi.single b q) ⬝ᵥ (M *ᵥ (Pi.single a p + Pi.single b q)) =
      p * p * M a a + p * q * (M a b + M b a) + q * q * M b b := by
  simp only [mulVec_add, dotProduct_add, add_dotProduct, single_dotProduct, mulVec_single,
    Pi.smul_apply, col_apply, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  ring

theorem single_add_single_add_single_dotProduct_mulVec
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (a b c : Fin (n + 1)) (p q r : ℝ) :
    (Pi.single a p + Pi.single b q + Pi.single c r) ⬝ᵥ
        (M *ᵥ (Pi.single a p + Pi.single b q + Pi.single c r)) =
      p * p * M a a + q * q * M b b + r * r * M c c + p * q * (M a b + M b a) +
        p * r * (M a c + M c a) + q * r * (M b c + M c b) := by
  simp only [mulVec_add, dotProduct_add, add_dotProduct, single_dotProduct, mulVec_single,
    Pi.smul_apply, col_apply, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  ring

theorem null_single_add_single {a : Fin (n + 1)} (ha : a ≠ 0) {s : ℝ} (hs : s * s = 1) :
    (Pi.single 0 1 + Pi.single a s) ⬝ᵥ (minkowski n *ᵥ (Pi.single 0 1 + Pi.single a s)) = 0 := by
  rw [single_add_single_dotProduct_mulVec]
  simp [minkowski_apply, ha, Ne.symm ha, hs]

theorem single_add_single_dotProduct_minkowski_mulVec {a : Fin (n + 1)} (ha : a ≠ 0) (s : ℝ)
    (x : Fin (n + 1) → ℝ) :
    (Pi.single 0 1 + Pi.single a s) ⬝ᵥ (minkowski n *ᵥ x) = -x 0 + s * x a := by
  simp [add_dotProduct, single_dotProduct, minkowski_mulVec_apply, ha]

/-- A nonzero Minkowski-null vector has nonzero time component dominating two space
components. -/
theorem null_aux {m : ℕ} {x : Fin (m + 3) → ℝ} (hx : x ≠ 0)
    (hnull : x ⬝ᵥ (minkowski (m + 2) *ᵥ x) = 0) :
    x 0 ≠ 0 ∧ x 1 ^ 2 + x 2 ^ 2 ≤ x 0 ^ 2 := by
  rw [dotProduct_minkowski_mulVec_self] at hnull
  have hrest : 0 ≤ ∑ i : Fin m, x i.succ.succ.succ ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsum : ∑ i : Fin (m + 2), x i.succ ^ 2 =
      x 1 ^ 2 + x 2 ^ 2 + ∑ i : Fin m, x i.succ.succ.succ ^ 2 := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
    ring
  refine ⟨fun h0 => hx ?_, by linarith⟩
  have hall : ∀ i ∈ Finset.univ, x (Fin.succ i) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg _).mp (by rw [h0] at hnull; linarith)
  funext i
  refine Fin.cases h0 (fun j => ?_) i
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (hall j (Finset.mem_univ _))

/-- For two nonzero null vectors there is a null vector pairing nontrivially with both. -/
theorem exists_null_ne_zero_ne_zero (hn : 2 ≤ n) {x y : Fin (n + 1) → ℝ} (hx : x ≠ 0)
    (hxn : x ⬝ᵥ (minkowski n *ᵥ x) = 0) (hy : y ≠ 0) (hyn : y ⬝ᵥ (minkowski n *ᵥ y) = 0) :
    ∃ z, z ⬝ᵥ (minkowski n *ᵥ z) = 0 ∧ z ⬝ᵥ (minkowski n *ᵥ x) ≠ 0 ∧
      z ⬝ᵥ (minkowski n *ᵥ y) ≠ 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h10 : (1 : Fin (m + 3)) ≠ 0 := by simp
  have h20 : (2 : Fin (m + 3)) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_zero] at this
    rw [show ((2 : Fin (m + 3)) : ℕ) = 2 from
      Nat.mod_eq_of_lt (a := 2) (b := m + 3) (by omega)] at this
    omega
  by_contra! h
  have h1 := h _ (null_single_add_single (a := 1) h10 (s := 1) (by norm_num))
  have h2 := h _ (null_single_add_single (a := 1) h10 (s := -1) (by norm_num))
  have h3 := h _ (null_single_add_single (a := 2) h20 (s := 1) (by norm_num))
  simp only [single_add_single_dotProduct_minkowski_mulVec h10,
    single_add_single_dotProduct_minkowski_mulVec h20] at h1 h2 h3
  obtain ⟨hx0, hx12⟩ := null_aux hx hxn
  obtain ⟨hy0, hy12⟩ := null_aux hy hyn
  have key : ∀ v : Fin (m + 3) → ℝ, v 0 ≠ 0 → v 1 ^ 2 + v 2 ^ 2 ≤ v 0 ^ 2 →
      ¬(-v 0 + 1 * v 1 = 0 ∧ -v 0 + -1 * v 1 = 0) ∧ ¬(-v 0 + 1 * v 1 = 0 ∧ -v 0 + 1 * v 2 = 0) ∧
        ¬(-v 0 + -1 * v 1 = 0 ∧ -v 0 + 1 * v 2 = 0) := by
    intro v hv0 hv
    have : 0 < v 0 ^ 2 := by positivity
    refine ⟨fun ⟨h, h'⟩ => hv0 (by linarith), fun ⟨h, h'⟩ => ?_, fun ⟨h, h'⟩ => ?_⟩
    · rw [show v 1 = v 0 by linarith, show v 2 = v 0 by linarith] at hv; linarith
    · rw [show v 1 = -v 0 by linarith, show v 2 = v 0 by linarith] at hv; nlinarith
  have kx := key x hx0 hx12
  have ky := key y hy0 hy12
  tauto

/-- A symmetric matrix whose quadratic form vanishes on the Minkowski null cone is a
multiple of the Minkowski matrix. -/
theorem eq_smul_minkowski_of_null {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hH : Hᵀ = H)
    (h : ∀ v, v ≠ 0 → v ⬝ᵥ (minkowski n *ᵥ v) = 0 → v ⬝ᵥ (H *ᵥ v) = 0) :
    H = (-H 0 0) • minkowski n := by
  have hsymm : ∀ a b, H b a = H a b := fun a b => by rw [← transpose_apply H a b, hH]
  have h2 : ∀ a, a ≠ 0 → H 0 a = 0 ∧ H a a = -H 0 0 := by
    intro a ha
    have hp := h _ ?_ (null_single_add_single ha (s := 1) (by norm_num))
    have hm := h _ ?_ (null_single_add_single ha (s := -1) (by norm_num))
    · rw [single_add_single_dotProduct_mulVec, hsymm 0 a] at hp hm
      constructor <;> linarith
    all_goals
      intro h0
      have := congrFun h0 0
      simp [Ne.symm ha] at this
  have h3 : ∀ a b, a ≠ 0 → b ≠ 0 → a ≠ b → H a b = 0 := by
    intro a b ha hb hab
    have hnull : (Pi.single 0 5 + Pi.single a 3 + Pi.single b 4) ⬝ᵥ
        (minkowski n *ᵥ (Pi.single 0 5 + Pi.single a 3 + Pi.single b 4)) = 0 := by
      rw [single_add_single_add_single_dotProduct_mulVec]
      simp [minkowski_apply, ha, hb, hab, Ne.symm ha, Ne.symm hb, Ne.symm hab]
      norm_num
    have hv := h _ ?_ hnull
    · rw [single_add_single_add_single_dotProduct_mulVec, hsymm 0 a, hsymm 0 b, hsymm a b,
        (h2 a ha).1, (h2 b hb).1, (h2 a ha).2, (h2 b hb).2] at hv
      linarith
    · intro h0
      have := congrFun h0 0
      simp [Ne.symm ha, Ne.symm hb] at this
  ext a b
  simp only [Matrix.smul_apply, minkowski_apply, smul_eq_mul]
  by_cases ha : a = 0 <;> by_cases hb : b = 0
  · subst ha hb; simp
  · subst ha; simp [Ne.symm hb, (h2 b hb).1]
  · subst hb; simp [ha, hsymm 0 a, (h2 a ha).1]
  · by_cases hab : a = b
    · subst hab; simp [ha, (h2 a ha).2]
    · simp [hab, h3 a b ha hb hab]

/-! ### Propagation along a null cone -/

theorem analyticAt_dotProduct_mulVec {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ)
    {f g : (Fin k → ℝ) → Fin k → ℝ} {x : Fin k → ℝ} (hf : AnalyticAt ℝ f x)
    (hg : AnalyticAt ℝ g x) : AnalyticAt ℝ (fun w => f w ⬝ᵥ (M *ᵥ g w)) x := by
  have hc : ∀ (h : (Fin k → ℝ) → Fin k → ℝ), AnalyticAt ℝ h x → ∀ i,
      AnalyticAt ℝ (fun w => h w i) x :=
    fun h hh i => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i).analyticAt _
      |>.comp hh
  simp only [dotProduct, mulVec]
  exact Finset.analyticAt_fun_sum _ fun i _ => (hc f hf i).mul
    (Finset.analyticAt_fun_sum _ fun j _ => analyticAt_const.mul (hc g hg j))

/-- Let `B` be symmetric and let the quadratic form of `H` vanish at the `B`-null vectors of
an open set `U` containing the `B`-null vector `ξ₀`. Then it vanishes at every `B`-null `v`
for which some `B`-null `ζ` pairs nontrivially with both `ξ₀` and `v`. The proof
parametrizes the null cone by the quadratic map `w ↦ B(w, w) ζ - 2 B(ζ, w) w` and uses the
identity theorem for analytic functions. -/
theorem dotProduct_mulVec_eq_zero_of_null {B H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hB : Bᵀ = B) {U : Set (Fin (n + 1) → ℝ)} (hU : IsOpen U)
    (hH : ∀ ξ ∈ U, ξ ⬝ᵥ (B *ᵥ ξ) = 0 → ξ ⬝ᵥ (H *ᵥ ξ) = 0)
    {ξ₀ ζ v : Fin (n + 1) → ℝ} (hξ₀ : ξ₀ ∈ U) (hξ₀n : ξ₀ ⬝ᵥ (B *ᵥ ξ₀) = 0)
    (hζ : ζ ⬝ᵥ (B *ᵥ ζ) = 0) (hv : v ⬝ᵥ (B *ᵥ v) = 0)
    (hζξ₀ : ζ ⬝ᵥ (B *ᵥ ξ₀) ≠ 0) (hζv : ζ ⬝ᵥ (B *ᵥ v) ≠ 0) :
    v ⬝ᵥ (H *ᵥ v) = 0 := by
  set c := -(2 * ζ ⬝ᵥ (B *ᵥ ξ₀))⁻¹ with hc
  set F : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ :=
    fun w => c • ((w ⬝ᵥ (B *ᵥ w)) • ζ - (2 * ζ ⬝ᵥ (B *ᵥ w)) • w) with hF
  have hsymm : ∀ x y, x ⬝ᵥ (B *ᵥ y) = y ⬝ᵥ (B *ᵥ x) := by
    intro x y
    rw [dotProduct_mulVec, ← mulVec_transpose, hB, dotProduct_comm]
  have hFnull : ∀ w, F w ⬝ᵥ (B *ᵥ F w) = 0 := by
    intro w
    simp only [hF, mulVec_smul, mulVec_sub, smul_dotProduct, dotProduct_smul, sub_dotProduct,
      dotProduct_sub, hζ, smul_eq_mul]
    rw [hsymm w ζ]
    ring
  have hFv : ∀ w, w ⬝ᵥ (B *ᵥ w) = 0 → F w = (-(2 * c * ζ ⬝ᵥ (B *ᵥ w))) • w := by
    intro w hw
    simp only [hF, hw, zero_smul, zero_sub, smul_neg, smul_smul, neg_smul]
    ring_nf
  have hF₀ : F ξ₀ = ξ₀ := by
    rw [hFv ξ₀ hξ₀n, hc]
    convert one_smul ℝ ξ₀ using 2
    field_simp
  have hFa : ∀ x, AnalyticAt ℝ F x := by
    intro x
    have h1 := analyticAt_dotProduct_mulVec B (analyticAt_id (z := x)) (analyticAt_id (z := x))
    have h2 := analyticAt_dotProduct_mulVec B (analyticAt_const (v := ζ) (x := x))
      (analyticAt_id (z := x))
    simp only [hF]
    fun_prop
  have hG : AnalyticOnNhd ℝ (fun w => F w ⬝ᵥ (H *ᵥ F w)) Set.univ :=
    fun x _ => analyticAt_dotProduct_mulVec H (hFa x) (hFa x)
  have hev : (fun w => F w ⬝ᵥ (H *ᵥ F w)) =ᶠ[nhds ξ₀] 0 := by
    have hpre : F ⁻¹' U ∈ nhds ξ₀ :=
      (hFa ξ₀).continuousAt.preimage_mem_nhds (by rw [hF₀]; exact hU.mem_nhds hξ₀)
    filter_upwards [hpre] with w hw
    exact hH _ hw (hFnull w)
  have := hG.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ ξ₀) hev (Set.mem_univ v)
  simp only [Pi.zero_apply, hFv v hv, mulVec_smul, dotProduct_smul, smul_dotProduct,
    smul_eq_mul] at this
  have hc0 : c ≠ 0 := by simpa [hc] using hζξ₀
  simpa [hc0, hζv] using this

/-! ### The null cone of a Lorentzian scalar product -/

theorem minkowski_mul_self : minkowski n * minkowski n = 1 := by
  rw [minkowski_def, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  split_ifs <;> norm_num

/-- A symmetric matrix whose quadratic form vanishes on a nonempty relatively open subset of
the null cone of `A⁻¹` is a multiple of `A⁻¹`. -/
theorem IsLorentzian.eq_smul_inv_of_null (hn : 2 ≤ n) {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : IsLorentzian A) {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hH : Hᵀ = H)
    {U : Set (Fin (n + 1) → ℝ)} (hU : IsOpen U) {ξ₀ : Fin (n + 1) → ℝ} (hξ₀ : ξ₀ ∈ U)
    (hξ₀0 : ξ₀ ≠ 0) (hξ₀n : ξ₀ ⬝ᵥ (A⁻¹ *ᵥ ξ₀) = 0)
    (hHU : ∀ ξ ∈ U, ξ ⬝ᵥ (A⁻¹ *ᵥ ξ) = 0 → ξ ⬝ᵥ (H *ᵥ ξ) = 0) :
    ∃ c : ℝ, H = c • A⁻¹ := by
  obtain ⟨P, hP⟩ := hA.exists_eq_transpose_mul_minkowski_mul
  have hdet : IsUnit P.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have := hA.det_neg
    rw [hP, det_mul, det_mul, h0] at this
    simp at this
  have hdetT : IsUnit Pᵀ.det := by rwa [det_transpose]
  have hinv : A⁻¹ = P⁻¹ * minkowski n * (Pᵀ)⁻¹ := by
    refine inv_eq_right_inv ?_
    rw [hP]
    calc Pᵀ * minkowski n * P * (P⁻¹ * minkowski n * Pᵀ⁻¹)
        = Pᵀ * minkowski n * (P * P⁻¹) * minkowski n * Pᵀ⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [mul_nonsing_inv _ hdet, Matrix.mul_one, Matrix.mul_assoc Pᵀ, minkowski_mul_self,
            Matrix.mul_one, mul_nonsing_inv _ hdetT]
  have hK : P * A⁻¹ * Pᵀ = minkowski n := by
    rw [hinv]
    calc P * (P⁻¹ * minkowski n * Pᵀ⁻¹) * Pᵀ = (P * P⁻¹) * minkowski n * (Pᵀ⁻¹ * Pᵀ) := by
          simp only [Matrix.mul_assoc]
      _ = minkowski n := by rw [mul_nonsing_inv _ hdet, nonsing_inv_mul _ hdetT, Matrix.one_mul,
          Matrix.mul_one]
  have htr : ∀ (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) x y,
      (Pᵀ *ᵥ x) ⬝ᵥ (M *ᵥ (Pᵀ *ᵥ y)) = x ⬝ᵥ ((P * M * Pᵀ) *ᵥ y) := by
    intro M x y
    rw [mulVec_mulVec, dotProduct_mulVec, dotProduct_mulVec, mulVec_transpose, vecMul_vecMul,
      Matrix.mul_assoc]
  have hsurj : ∀ w, Pᵀ *ᵥ (Pᵀ⁻¹ *ᵥ w) = w := fun w => by
    rw [mulVec_mulVec, mul_nonsing_inv _ hdetT, one_mulVec]
  have hAinv : (A⁻¹)ᵀ = A⁻¹ := by rw [transpose_nonsing_inv, hA.symm]
  set y₀ := Pᵀ⁻¹ *ᵥ ξ₀
  have hy₀0 : y₀ ≠ 0 := by
    intro h
    apply hξ₀0
    rw [← hsurj ξ₀]
    simp [y₀, h]
  have hy₀n : y₀ ⬝ᵥ (minkowski n *ᵥ y₀) = 0 := by rw [← hK, ← htr, hsurj, hξ₀n]
  have hH' : (P * H * Pᵀ)ᵀ = P * H * Pᵀ := by
    rw [transpose_mul, transpose_mul, transpose_transpose, hH, Matrix.mul_assoc]
  have hnull : ∀ w, w ≠ 0 → w ⬝ᵥ (minkowski n *ᵥ w) = 0 → w ⬝ᵥ ((P * H * Pᵀ) *ᵥ w) = 0 := by
    intro w hw hwn
    obtain ⟨z, hz, hzy₀, hzw⟩ := exists_null_ne_zero_ne_zero hn hy₀0 hy₀n hw hwn
    rw [← hK, ← htr] at hz hzy₀ hzw hwn
    rw [hsurj] at hzy₀
    rw [← htr]
    exact dotProduct_mulVec_eq_zero_of_null hAinv hU hHU hξ₀ hξ₀n hz hwn hzy₀ hzw
  obtain ⟨c, hHeq⟩ : ∃ c : ℝ, P * H * Pᵀ = c • minkowski n :=
    ⟨_, eq_smul_minkowski_of_null hH' hnull⟩
  refine ⟨c, ?_⟩
  calc H = P⁻¹ * (P * H * Pᵀ) * Pᵀ⁻¹ := by
        simp only [← Matrix.mul_assoc, nonsing_inv_mul _ hdet, Matrix.one_mul]
        rw [Matrix.mul_assoc, mul_nonsing_inv _ hdetT, Matrix.mul_one]
    _ = _ := by
        rw [hHeq, hinv, Matrix.mul_smul, Matrix.smul_mul]

/-! ### Spanning -/

/-- The null covectors of `A` in `U`: the nonzero `ξ ∈ U` with `A⁻¹(ξ, ξ) = 0`. -/
def nullCovectors (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (U : Set (Fin (n + 1) → ℝ)) :
    Set (Fin (n + 1) → ℝ) :=
  {ξ | ξ ∈ U ∧ ξ ≠ 0 ∧ ξ ⬝ᵥ (A⁻¹ *ᵥ ξ) = 0}

theorem dotProduct_vecMulVec_mulVec (X ξ : Fin (n + 1) → ℝ) :
    ξ ⬝ᵥ (vecMulVec X X *ᵥ ξ) = (ξ ⬝ᵥ X) ^ 2 := by
  rw [vecMulVec_mulVec, op_smul_eq_smul, dotProduct_smul, smul_eq_mul, dotProduct_comm X ξ, sq]

/-- (a) The null covectors in a nonempty relatively open subset of the null cone span. -/
theorem IsLorentzian.span_nullCovectors (hn : 2 ≤ n)
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hA : IsLorentzian A)
    {U : Set (Fin (n + 1) → ℝ)} (hU : IsOpen U) (hne : (nullCovectors A U).Nonempty) :
    Submodule.span ℝ (nullCovectors A U) = ⊤ := by
  obtain ⟨ξ₀, hξ₀, hξ₀0, hξ₀n⟩ := hne
  by_contra htop
  obtain ⟨x, hx⟩ : ∃ x, x ∉ Submodule.span ℝ (nullCovectors A U) := by
    by_contra! h
    exact htop (eq_top_iff.mpr fun x _ => h x)
  obtain ⟨f, hfx, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
  have hf0 : ∀ ξ ∈ nullCovectors A U, f ξ = 0 := fun ξ hξ => by
    have := Submodule.mem_map_of_mem (f := f) (Submodule.subset_span hξ)
    rwa [hf, Submodule.mem_bot] at this
  set X : Fin (n + 1) → ℝ := fun i => f fun j => if i = j then 1 else 0
  have hfX : ∀ ξ, f ξ = ξ ⬝ᵥ X := fun ξ => by
    rw [LinearMap.pi_apply_eq_sum_univ f ξ]
    rfl
  obtain ⟨c, hc⟩ := hA.eq_smul_inv_of_null hn (H := vecMulVec X X) (transpose_vecMulVec X X) hU
    hξ₀ hξ₀0 hξ₀n fun ξ hξ hξn => by
      rw [dotProduct_vecMulVec_mulVec, ← hfX]
      by_cases h0 : ξ = 0
      · simp [h0]
      · simp [hf0 ξ ⟨hξ, h0, hξn⟩]
  have hdetA : IsUnit A.det := isUnit_iff_ne_zero.mpr hA.det_neg.ne
  obtain ⟨z, hz0, hXz⟩ : ∃ z : Fin (n + 1) → ℝ, z ≠ 0 ∧ X ⬝ᵥ z = 0 := by
    have h10 : (1 : Fin (n + 1)) ≠ 0 := by
      intro h
      have := congrArg Fin.val h
      rw [Fin.val_one', Fin.val_zero, Nat.mod_eq_of_lt (by omega)] at this
      omega
    by_cases hX0 : X 0 = 0
    · refine ⟨Pi.single 0 1, fun h => by simpa using congrFun h 0, ?_⟩
      simp [hX0]
    · refine ⟨Pi.single 0 (X 1) - Pi.single 1 (X 0), fun h => hX0 ?_, ?_⟩
      · simpa [h10] using congrFun h 1
      · simp [dotProduct_sub, dotProduct_single]
        ring
  have hc0 : c = 0 := by
    by_contra hc0
    have h1 : (c • A⁻¹) *ᵥ z = 0 := by
      rw [← hc, vecMulVec_mulVec, hXz]
      simp
    rw [smul_mulVec, smul_eq_zero] at h1
    refine hz0 ?_
    rw [← one_mulVec z, ← mul_nonsing_inv A hdetA, ← mulVec_mulVec, h1.resolve_left hc0,
      mulVec_zero]
  have hX : X = 0 := by
    funext i
    have := congrFun (congrFun hc i) i
    simpa [hc0, vecMulVec_apply] using this
  exact hfx (by rw [hfX, hX, dotProduct_zero])

/-- (b) `A` and the outer products `ξ ξᵀ` of the null covectors in a nonempty relatively open
subset of the null cone span the symmetric matrices. -/
theorem IsLorentzian.mem_span_nullCovectors (hn : 2 ≤ n)
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hA : IsLorentzian A)
    {U : Set (Fin (n + 1) → ℝ)} (hU : IsOpen U) (hne : (nullCovectors A U).Nonempty)
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hM : Mᵀ = M) :
    M ∈ Submodule.span ℝ (insert A ((fun ξ => vecMulVec ξ ξ) '' nullCovectors A U)) := by
  obtain ⟨ξ₀, hξ₀, hξ₀0, hξ₀n⟩ := hne
  by_contra hM'
  obtain ⟨f, hfM, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hM' inferInstance
  have hf0 : ∀ N ∈ insert A ((fun ξ => vecMulVec ξ ξ) '' nullCovectors A U), f N = 0 :=
    fun N hN => by
      have := Submodule.mem_map_of_mem (f := f) (Submodule.subset_span hN)
      rwa [hf, Submodule.mem_bot] at this
  set F : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun i j => f (single i j 1)
  set H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun i j => (F i j + F j i) / 2
  have hH : Hᵀ = H := by
    ext i j
    change (F j i + F i j) / 2 = (F i j + F j i) / 2
    ring
  have hfN : ∀ N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ, Nᵀ = N →
      f N = ∑ i, ∑ j, N i j * H i j := by
    intro N hN
    have h1 : f N = ∑ i, ∑ j, N i j * F i j := by
      conv_lhs => rw [matrix_eq_sum_single N]
      simp only [map_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [show single i j (N i j) = N i j • single i j 1 by rw [smul_single, smul_eq_mul, mul_one],
        map_smul, smul_eq_mul]
    have h2 : ∑ i, ∑ j, N i j * F j i = ∑ i, ∑ j, N i j * F i j := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [← transpose_apply N i j, hN]
    simp only [H, mul_div_assoc', mul_add, add_div, Finset.sum_add_distrib, ← Finset.sum_div, h2,
      ← h1]
    ring
  have hquad : ∀ ξ, ξ ⬝ᵥ (H *ᵥ ξ) = f (vecMulVec ξ ξ) := by
    intro ξ
    rw [hfN _ (transpose_vecMulVec ξ ξ)]
    simp only [dotProduct, mulVec, vecMulVec_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  obtain ⟨c, hc⟩ := hA.eq_smul_inv_of_null hn hH hU hξ₀ hξ₀0 hξ₀n fun ξ hξ hξn => by
    rw [hquad]
    by_cases h0 : ξ = 0
    · simp [h0]
    · exact hf0 _ (Set.mem_insert_of_mem _ ⟨ξ, ⟨hξ, h0, hξn⟩, rfl⟩)
  have hdetA : IsUnit A.det := isUnit_iff_ne_zero.mpr hA.det_neg.ne
  have hAinv : ∀ i j, A⁻¹ j i = A⁻¹ i j := fun i j => by
    rw [← transpose_apply A⁻¹ i j, transpose_nonsing_inv, hA.symm]
  have hfA : f A = c * (n + 1) := by
    rw [hfN A hA.symm, hc]
    have : ∑ i, ∑ j, A i j * A⁻¹ i j = ∑ i, (A * A⁻¹) i i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_apply]
      exact Finset.sum_congr rfl fun j _ => by rw [hAinv]
    simp only [Matrix.smul_apply, smul_eq_mul, mul_left_comm _ c, ← Finset.mul_sum, this,
      mul_nonsing_inv A hdetA, one_apply_eq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    push_cast
    ring
  have hc0 : c = 0 := by
    have := hf0 A (Set.mem_insert _ _)
    rw [hfA] at this
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h (by positivity)
  exact hfM (by rw [hfN M hM, hc, hc0]; simp)

/-- The symmetric `(n+1) × (n+1)` matrices. -/
def symmetricMatrices (n : ℕ) : Submodule ℝ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) where
  carrier := {M | Mᵀ = M}
  add_mem' {M N} hM hN := by
    simp only [Set.mem_ofPred_eq, transpose_add] at *
    rw [hM, hN]
  zero_mem' := transpose_zero
  smul_mem' c M hM := by
    simp only [Set.mem_ofPred_eq, transpose_smul] at *
    rw [hM]

theorem mem_symmetricMatrices {n : ℕ} {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} :
    M ∈ symmetricMatrices n ↔ Mᵀ = M := Iff.rfl

/-- **Null covectors in an open set span.** A nonempty relatively open subset of the null
cone of `A⁻¹` contains a finite set of null covectors that includes a basis and whose outer
products together with `A` span the symmetric matrices. -/
theorem IsLorentzian.exists_finset_null_span (hn : 2 ≤ n)
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hA : IsLorentzian A)
    {U : Set (Fin (n + 1) → ℝ)} (hU : IsOpen U)
    (hne : ∃ ξ ∈ U, ξ ≠ 0 ∧ ξ ⬝ᵥ (A⁻¹ *ᵥ ξ) = 0) :
    ∃ (s : Finset (Fin (n + 1) → ℝ)) (b : Fin (n + 1) → Fin (n + 1) → ℝ),
      (∀ ξ ∈ s, ξ ∈ U ∧ ξ ≠ 0 ∧ ξ ⬝ᵥ (A⁻¹ *ᵥ ξ) = 0) ∧ (∀ i, b i ∈ s) ∧
        LinearIndependent ℝ b ∧
        ∀ M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ, Mᵀ = M →
          M ∈ Submodule.span ℝ (insert A ((fun ξ => vecMulVec ξ ξ) '' (s : Set _))) := by
  classical
  set S := nullCovectors A U
  have hS : S.Nonempty := by
    obtain ⟨ξ, h⟩ := hne
    exact ⟨ξ, h⟩
  obtain ⟨t, htS, hspan, hli⟩ := exists_linearIndependent ℝ S
  let bt := Module.Basis.mk hli (by rw [Subtype.range_coe, hspan, hA.span_nullCovectors hn hU hS])
  let e := bt.indexEquiv (Pi.basisFun ℝ (Fin (n + 1)))
  let b : Fin (n + 1) → Fin (n + 1) → ℝ := fun i => (e.symm i : Fin (n + 1) → ℝ)
  have hb : LinearIndependent ℝ b := hli.comp e.symm e.symm.injective
  have key : ∀ g ∈ Submodule.span ℝ (insert A ((fun ξ => vecMulVec ξ ξ) '' S)),
      ∃ s' : Finset (Fin (n + 1) → ℝ), ↑s' ⊆ S ∧
        g ∈ Submodule.span ℝ (insert A ((fun ξ => vecMulVec ξ ξ) '' (s' : Set _))) := by
    intro g hg
    obtain ⟨T, hT, hgT⟩ := Submodule.mem_span_finite_of_mem_span hg
    have hTe : ↑(T.erase A) ⊆ (fun ξ => vecMulVec ξ ξ) '' S := by
      intro N hN
      rw [Finset.coe_erase] at hN
      exact (hT hN.1).resolve_left hN.2
    obtain ⟨s', hs'S, hs'⟩ := Finset.subset_set_image_iff.mp hTe
    refine ⟨s', hs'S, Submodule.span_mono ?_ hgT⟩
    intro N hN
    by_cases hNA : N = A
    · exact hNA ▸ Set.mem_insert _ _
    · refine Set.mem_insert_of_mem _ ?_
      have : N ∈ s'.image fun ξ => vecMulVec ξ ξ := by
        rw [hs']
        exact Finset.mem_erase.mpr ⟨hNA, hN⟩
      simpa using this
  obtain ⟨G, hG⟩ := IsNoetherian.noetherian (symmetricMatrices n)
  have hGsym : ∀ g ∈ G, gᵀ = g := fun g hg => by
    have : g ∈ symmetricMatrices n := hG ▸ Submodule.subset_span hg
    exact mem_symmetricMatrices.1 this
  choose! sg hsgS hsg using fun g (hg : g ∈ G) => key g (hA.mem_span_nullCovectors hn hU hS
    (hGsym g hg))
  refine ⟨G.biUnion sg ∪ Finset.univ.image b, b, ?_, ?_, hb, ?_⟩
  · intro ξ hξ
    rcases Finset.mem_union.mp hξ with h | h
    · obtain ⟨g, hg, hξg⟩ := Finset.mem_biUnion.mp h
      exact hsgS g hg hξg
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp h
      exact htS (e.symm i).2
  · exact fun i => Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  · intro M hM
    have hMG : M ∈ Submodule.span ℝ (G : Set _) := hG ▸ hM
    refine Submodule.span_le.mpr (fun g hg => ?_) hMG
    refine Submodule.span_mono (Set.insert_subset_insert (Set.image_mono ?_)) (hsg g hg)
    intro ξ hξ
    exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨g, hg, hξ⟩)

end LorentzianCalderon
