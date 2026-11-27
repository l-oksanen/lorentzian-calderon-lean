module

public import LorentzianCalderon.Geometry.NormalNbhd

public section

/-!
# Local causality in totally normal sets

Let `W` be totally normal with inverse `L`, and `γ` a future causal curve in `W` from `a`.
Following O'Neill, Semi-Riemannian geometry, Lemma 5.33, p. 146 (and Lemma 14.2 A, p. 403), the
function `Q(t) = g_a(L(a, γ t), L(a, γ t))` is nonincreasing (`grad Q = 2 P` by the Gauss lemma,
`P` the radial velocity) and `L(a, γ t)` stays in the future causal cone of `a`. Moreover:

* `L(a, γ t)` is future timelike, so `a ≪ γ t` along the radial geodesic, unless `γ` is a
  monotone reparametrization of the radial null geodesic `r ↦ exp_a (r L(a, γ t))`
  (`IsTotallyNormal.isFutureTimelike_or_radial`);
* there are no closed causal curves in `W` (`IsTotallyNormal.apply_ne_of_isPathOn`);
* `x ≪ γ(α)` implies `x ≪ γ(β)`, and `γ(β) ≪ z` implies `γ(α) ≪ z`
  (`IsTotallyNormal.chronLT_of_chronLT_of_isPathOn`,
  `IsTotallyNormal.chronLT_of_isPathOn_of_chronLT`).

Since the causal cone is not open, the causal case of Lemma 5.33 is obtained from the timelike
one by moving the base point `a` slightly into its past (`IsTotallyNormal.exists_past`).
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Set Filter Metric

variable {n : ℕ} {g : MatrixField n} {Y : E n → E n}

/-! ### Relations along the pieces of a path -/

section Pieces

variable {P : E n → E n → Prop} {a b : ℝ} {γ : ℝ → E n}

/-- A reflexive and transitive relation that holds between the endpoints of every smooth piece
of a path holds between any two parameters, in order. -/
theorem IsPathOn.rel_of_isPathPiece (h : IsPathOn P a b γ) {R : ℝ → ℝ → Prop}
    (hrefl : ∀ u, R u u) (htrans : ∀ u v w, u ≤ v → v ≤ w → R u v → R v w → R u w)
    (hpiece : ∀ x y, a ≤ x → x < y → y ≤ b → IsPathPiece P x y γ → R x y) :
    ∀ u v, a ≤ u → u ≤ v → v ≤ b → R u v := by
  classical
  obtain ⟨-, F, hF⟩ := isPathOn_iff.1 h
  suffices key : ∀ N u v, a ≤ u → u ≤ v → v ≤ b → (F.filter (· ∈ Ioo u v)).card ≤ N → R u v from
    fun u v hu huv hv => key _ u v hu huv hv le_rfl
  intro N
  induction N with
  | zero =>
    intro u v hu huv hv hc
    rcases huv.lt_or_eq with huv | rfl
    · refine hpiece u v hu huv hv (hF u v hu huv hv fun z hz hzI => ?_)
      rw [Nat.le_zero, Finset.card_eq_zero] at hc
      have : z ∈ F.filter (· ∈ Ioo u v) := Finset.mem_filter.2 ⟨hz, hzI⟩
      rw [hc] at this
      exact Finset.notMem_empty z this
    · exact hrefl u
  | succ N ih =>
    intro u v hu huv hv hc
    by_cases hne : (F.filter (· ∈ Ioo u v)).Nonempty
    · obtain ⟨z, hz⟩ := hne
      obtain ⟨-, hzI⟩ := Finset.mem_filter.1 hz
      have hlt : ∀ c d, u ≤ c → d ≤ v → z ∉ Ioo c d →
          (F.filter (· ∈ Ioo c d)).card ≤ N := by
        intro c d hc' hd' hzcd
        have hsub : F.filter (· ∈ Ioo c d) ⊂ F.filter (· ∈ Ioo u v) := by
          refine (Finset.ssubset_iff_of_subset fun y hy => ?_).2 ⟨z, hz, fun h => hzcd ?_⟩
          · obtain ⟨hyF, hy⟩ := Finset.mem_filter.1 hy
            exact Finset.mem_filter.2 ⟨hyF, hc'.trans_lt hy.1, hy.2.trans_le hd'⟩
          · exact (Finset.mem_filter.1 h).2
        have := Finset.card_lt_card hsub
        omega
      exact htrans u z v hzI.1.le hzI.2.le
        (ih u z hu hzI.1.le (hzI.2.le.trans hv) (hlt u z le_rfl hzI.2.le fun h => lt_irrefl _ h.2))
        (ih z v (hu.trans hzI.1.le) hzI.2.le hv (hlt z v hzI.1.le le_rfl fun h => lt_irrefl _ h.1))
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      exact ih u v hu huv hv (by rw [hne, Finset.card_empty]; exact Nat.zero_le _)

/-- A function strictly decreasing on every smooth piece of a path is strictly decreasing. -/
theorem IsPathOn.strictAntiOn_of_isPathPiece (h : IsPathOn P a b γ) {f : ℝ → ℝ}
    (hpiece : ∀ x y, a ≤ x → x < y → y ≤ b → IsPathPiece P x y γ → StrictAntiOn f (Icc x y)) :
    StrictAntiOn f (Icc a b) := by
  have key := h.rel_of_isPathPiece (R := fun u v => u < v → f v < f u) (fun u h => absurd h
    (lt_irrefl u)) (fun u v w huv hvw h1 h2 huw => by
      rcases huv.lt_or_eq with huv | rfl
      · rcases hvw.lt_or_eq with hvw | rfl
        · exact (h2 hvw).trans (h1 huv)
        · exact h1 huv
      · exact h2 huw)
    fun x y hx hxy hy hp _ => hpiece x y hx hxy hy hp ⟨le_rfl, hxy.le⟩ ⟨hxy.le, le_rfl⟩ hxy
  exact fun u hu v hv huv => key u v hu.1 huv.le hv.2 huv

/-- A function nonincreasing on every smooth piece of a path is nonincreasing. -/
theorem IsPathOn.antitoneOn_of_isPathPiece (h : IsPathOn P a b γ) {f : ℝ → ℝ}
    (hpiece : ∀ x y, a ≤ x → x < y → y ≤ b → IsPathPiece P x y γ → AntitoneOn f (Icc x y)) :
    AntitoneOn f (Icc a b) := by
  have key := h.rel_of_isPathPiece (R := fun u v => f v ≤ f u) (fun u => le_rfl)
    (fun u v w _ _ h1 h2 => h2.trans h1)
    fun x y hx hxy hy hp => hpiece x y hx hxy hy hp ⟨le_rfl, hxy.le⟩ ⟨hxy.le, le_rfl⟩ hxy.le
  exact fun u hu v hv huv => key u v hu.1 huv hv.2

/-- A function nondecreasing on every smooth piece of a path is nondecreasing. -/
theorem IsPathOn.monotoneOn_of_isPathPiece (h : IsPathOn P a b γ) {f : ℝ → ℝ}
    (hpiece : ∀ x y, a ≤ x → x < y → y ≤ b → IsPathPiece P x y γ → MonotoneOn f (Icc x y)) :
    MonotoneOn f (Icc a b) := by
  have key := h.rel_of_isPathPiece (R := fun u v => f u ≤ f v) (fun u => le_rfl)
    (fun u v w _ _ h1 h2 => h1.trans h2)
    fun x y hx hxy hy hp => hpiece x y hx hxy hy hp ⟨le_rfl, hxy.le⟩ ⟨hxy.le, le_rfl⟩ hxy.le
  exact fun u hu v hv huv => key u v hu.1 huv hv.2

/-- Every subinterval of the domain of a path contains a smooth piece. -/
theorem IsPathOn.exists_isPathPiece (h : IsPathOn P a b γ) {u v : ℝ} (hau : a ≤ u) (huv : u < v)
    (hvb : v ≤ b) : ∃ x y, u ≤ x ∧ x < y ∧ y ≤ v ∧ IsPathPiece P x y γ := by
  classical
  obtain ⟨-, F, hF⟩ := isPathOn_iff.1 h
  set S := insert v (F.filter (· ∈ Ioo u v))
  have hS : S.Nonempty := Finset.insert_nonempty _ _
  have hmem : ∀ z ∈ S, u < z ∧ z ≤ v := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact ⟨huv, le_rfl⟩
    · exact ⟨(Finset.mem_filter.1 hz).2.1, (Finset.mem_filter.1 hz).2.2.le⟩
  obtain ⟨hm1, hm2⟩ := hmem _ (S.min'_mem hS)
  refine ⟨u, S.min' hS, le_rfl, hm1, hm2,
    hF u _ hau hm1 (hm2.trans hvb) fun z hz hzI => ?_⟩
  have hzS : z ∈ S := Finset.mem_insert_of_mem
    (Finset.mem_filter.2 ⟨hz, hzI.1, hzI.2.trans_le hm2⟩)
  exact absurd (S.min'_le z hzS) (not_le.2 hzI.2)

/-- Inside a smooth piece, the one-sided velocity is the velocity. -/
theorem IsPathPiece.hasDerivAt {x y t : ℝ} (h : IsPathPiece P x y γ) (ht : t ∈ Ioo x y) :
    HasDerivAt γ (derivWithin γ (Icc x y) t) t :=
  (((isPathPiece_iff.1 h).1.differentiableOn (by simp) t
    (Ioo_subset_Icc_self ht)).hasDerivWithinAt).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)

end Pieces

/-! ### Causal vectors -/

section Cone

variable {x u v : E n}

/-- Two future causal vectors have nonpositive scalar product. -/
theorem IsFutureCausal.form_nonpos (hg : IsSpacetime g Y) (hu : IsFutureCausal g Y x u)
    (hv : IsFutureCausal g Y x v) : form (g x) u v ≤ 0 := by
  have hL := hg.lorentzian x
  set α := form (g x) u (Y x)
  set β := form (g x) v (Y x)
  have hα : α < 0 := hu.future
  have hβ : β < 0 := hv.future
  set z := β • u - α • v
  have hzY : form (g x) z (Y x) = 0 := by
    simp only [z, form_sub_left, form_smul_left, α, β]
    ring
  have hvu : form (g x) v u = form (g x) u v := form_comm hL.symm v u
  have hzz : form (g x) z z = β ^ 2 * form (g x) u u - 2 * (α * β) * form (g x) u v +
      α ^ 2 * form (g x) v v := by
    simp only [z, form_sub_left, form_sub_right, form_smul_left, form_smul_right, hvu]
    ring
  by_cases hz : z = 0
  · have hv' : v = (β / α) • u := by
      have : α • v = β • u := (sub_eq_zero.1 hz).symm
      calc v = α⁻¹ • (α • v) := (inv_smul_smul₀ hα.ne v).symm
        _ = (β / α) • u := by rw [this, smul_smul, div_eq_inv_mul]
    rw [hv', form_smul_right]
    exact mul_nonpos_of_nonneg_of_nonpos (div_pos_of_neg_of_neg hβ hα).le hu.causal
  · have hpos : 0 < form (g x) z z := by
      by_contra hle
      exact hL.form_ne_zero (not_lt.1 hle) hz
        (hg.globallyHyperbolic.timeOrientation.timelike x) hzY
    have hαβ : 0 < α * β := mul_pos_of_neg_of_neg hα hβ
    rw [hzz] at hpos
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg β) hu.causal,
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg α) hv.causal]

/-- A future causal vector orthogonal to a future null vector `u` is a positive multiple of
`u`. -/
theorem IsFutureCausal.eq_smul_of_form_eq_zero (hg : IsSpacetime g Y)
    (hu : IsFutureCausal g Y x u) (hv : IsFutureCausal g Y x v) (huu : form (g x) u u = 0)
    (huv : form (g x) u v = 0) : ∃ κ > (0 : ℝ), v = κ • u := by
  have hL := hg.lorentzian x
  set α := form (g x) u (Y x)
  set β := form (g x) v (Y x)
  have hα : α < 0 := hu.future
  have hβ : β < 0 := hv.future
  set z := β • u - α • v
  have hzY : form (g x) z (Y x) = 0 := by
    simp only [z, form_sub_left, form_smul_left, α, β]
    ring
  have hvu : form (g x) v u = 0 := (form_comm hL.symm v u).trans huv
  have hzz : form (g x) z z = α ^ 2 * form (g x) v v := by
    simp only [z, form_sub_left, form_sub_right, form_smul_left, form_smul_right, hvu, huv, huu]
    ring
  have hz : z = 0 := by
    by_contra hz
    refine hL.form_ne_zero ?_ hz (hg.globallyHyperbolic.timeOrientation.timelike x) hzY
    rw [hzz]
    exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg α) hv.causal
  refine ⟨β / α, div_pos_of_neg_of_neg hβ hα, ?_⟩
  have : α • v = β • u := (sub_eq_zero.1 hz).symm
  calc v = α⁻¹ • (α • v) := (inv_smul_smul₀ hα.ne v).symm
    _ = (β / α) • u := by rw [this, smul_smul, div_eq_inv_mul]

/-- A vector in the closed future cone is zero or future causal. -/
theorem isFutureCausal_of_form_nonpos (hg : IsSpacetime g Y) (h1 : form (g x) v v ≤ 0)
    (h2 : form (g x) v (Y x) ≤ 0) (hv : v ≠ 0) : IsFutureCausal g Y x v :=
  ⟨hv, h1, lt_of_le_of_ne h2 ((hg.lorentzian x).form_ne_zero h1 hv
    (hg.globallyHyperbolic.timeOrientation.timelike x))⟩

/-- The future timecone is open. -/
theorem isOpen_setOf_isFutureTimelike (hg : IsSpacetime g Y) (x : E n) :
    IsOpen {v : E n | IsFutureTimelike g Y x v} := by
  have h1 : Continuous fun v : E n => form (g x) v v :=
    (continuous_form hg).comp (continuous_const.prodMk (continuous_id.prodMk continuous_id))
  have h2 : Continuous fun v : E n => form (g x) v (Y x) :=
    (continuous_form hg).comp (continuous_const.prodMk (continuous_id.prodMk continuous_const))
  have : {v : E n | IsFutureTimelike g Y x v} =
      {v | form (g x) v v < 0} ∩ {v | form (g x) v (Y x) < 0} := by
    ext v
    exact ⟨fun h => ⟨h.timelike, h.future⟩, fun h => ⟨h.1, h.2⟩⟩
  rw [this]
  exact (isOpen_lt h1 continuous_const).inter (isOpen_lt h2 continuous_const)

end Cone

namespace IsTotallyNormal

variable {W : Set (E n)} {ρ : ℝ} {L : E n × E n → E n} {γ : ℝ → E n} {α β : ℝ}

/-- The derivative of `Q(t) = g_a(L(a, γ t), L(a, γ t))` inside a smooth piece of `γ`. -/
theorem hasDerivAt_form_of_isPathPiece (hg : IsSpacetime g Y) (hW : IsTotallyNormal g W ρ L)
    {a : E n} (ha : a ∈ W) {P : E n → E n → Prop} {x y t : ℝ} (hp : IsPathPiece P x y γ)
    (ht : t ∈ Ioo x y) (hγt : γ t ∈ W) :
    HasDerivAt (fun r => form (g a) (L (a, γ r)) (L (a, γ r)))
      (2 * form (g (γ t)) (fderiv ℝ (expMap g a) (L (a, γ t)) (L (a, γ t)))
        (derivWithin γ (Icc x y) t)) t :=
  hasDerivWithinAt_univ.1 (hW.hasDerivWithinAt_form hg ha
    (hp.hasDerivAt ht).hasDerivWithinAt hγt)

/-- `Q(t) = g_a(L(a, γ t), L(a, γ t))` is continuous along a continuous curve in `W`. -/
theorem continuousOn_form (hg : IsSpacetime g Y) (hW : IsTotallyNormal g W ρ L) {a : E n}
    (ha : a ∈ W) {s : Set ℝ} (hγ : ContinuousOn γ s) (hγW : ∀ t ∈ s, γ t ∈ W) :
    ContinuousOn (fun r => form (g a) (L (a, γ r)) (L (a, γ r))) s := by
  have hw := hW.continuousOn_comp ha hγ hγW
  have := (continuous_form hg).comp_continuousOn
    ((continuousOn_const (c := a)).prodMk (hw.prodMk hw))
  simp only [Function.comp_def] at this
  exact this

/-- `Q` is strictly decreasing where `L(a, γ t)` is future timelike. -/
theorem strictAntiOn_form (hg : IsSpacetime g Y) (hW : IsTotallyNormal g W ρ L) {a : E n}
    (ha : a ∈ W) (hγ : IsPathOn (IsFutureCausal g Y) α β γ) (hγW : ∀ t ∈ Icc α β, γ t ∈ W)
    (hT : ∀ t ∈ Ioo α β, IsFutureTimelike g Y a (L (a, γ t))) :
    StrictAntiOn (fun r => form (g a) (L (a, γ r)) (L (a, γ r))) (Icc α β) := by
  refine hγ.strictAntiOn_of_isPathPiece fun x y hx hxy hy hp => ?_
  have hsub : Icc x y ⊆ Icc α β := Icc_subset_Icc hx hy
  refine strictAntiOn_of_deriv_neg (convex_Icc x y) (hW.continuousOn_form hg ha
    ((isPathPiece_iff.1 hp).1.continuousOn) fun t ht => hγW t (hsub ht)) fun t ht => ?_
  rw [interior_Icc] at ht
  have hγt := hγW t (hsub (Ioo_subset_Icc_self ht))
  rw [(hW.hasDerivAt_form_of_isPathPiece hg ha hp ht hγt).deriv]
  have hw := hT t ⟨hx.trans_lt ht.1, ht.2.trans_le hy⟩
  have hdom := hW.inExpDomain a ha _ (hW.mem_ball a ha _ hγt)
  have hR := hdom.isFutureTimelike_fderiv hg hw
  rw [hW.expMap_inv a ha _ hγt] at hR
  have := hR.form_neg (hg.lorentzian _) (hg.globallyHyperbolic.timeOrientation.timelike _)
    ((isPathPiece_iff.1 hp).2 t (Ioo_subset_Icc_self ht))
  linarith

/-- `Q` is nonincreasing where `L(a, γ t)` is zero or future causal. -/
theorem antitoneOn_form' (hg : IsSpacetime g Y) (hW : IsTotallyNormal g W ρ L) {a : E n}
    (ha : a ∈ W) (hγ : IsPathOn (IsFutureCausal g Y) α β γ) (hγW : ∀ t ∈ Icc α β, γ t ∈ W)
    (hC : ∀ t ∈ Ioo α β, L (a, γ t) = 0 ∨ IsFutureCausal g Y a (L (a, γ t))) :
    AntitoneOn (fun r => form (g a) (L (a, γ r)) (L (a, γ r))) (Icc α β) := by
  refine hγ.antitoneOn_of_isPathPiece fun x y hx hxy hy hp => ?_
  have hsub : Icc x y ⊆ Icc α β := Icc_subset_Icc hx hy
  have hd : ∀ t ∈ Ioo x y, HasDerivAt (fun r => form (g a) (L (a, γ r)) (L (a, γ r)))
      (2 * form (g (γ t)) (fderiv ℝ (expMap g a) (L (a, γ t)) (L (a, γ t)))
        (derivWithin γ (Icc x y) t)) t := fun t ht =>
    hW.hasDerivAt_form_of_isPathPiece hg ha hp ht (hγW t (hsub (Ioo_subset_Icc_self ht)))
  refine antitoneOn_of_deriv_nonpos (convex_Icc x y) (hW.continuousOn_form hg ha
    ((isPathPiece_iff.1 hp).1.continuousOn) fun t ht => hγW t (hsub ht)) ?_ fun t ht => ?_
  · rw [interior_Icc]
    exact fun t ht => (hd t ht).differentiableAt.differentiableWithinAt
  rw [interior_Icc] at ht
  have hγt := hγW t (hsub (Ioo_subset_Icc_self ht))
  rw [(hd t ht).deriv]
  rcases hC t ⟨hx.trans_lt ht.1, ht.2.trans_le hy⟩ with h0 | hw
  · simp [h0]
  have hdom := hW.inExpDomain a ha _ (hW.mem_ball a ha _ hγt)
  have hR := hdom.isFutureCausal_fderiv hg hw
  rw [hW.expMap_inv a ha _ hγt] at hR
  have := hR.form_nonpos hg ((isPathPiece_iff.1 hp).2 t (Ioo_subset_Icc_self ht))
  linarith

/-- O'Neill, Lemma 5.33, timelike case: if `L(a, γ α)` is future timelike, `L(a, γ t)` stays
future timelike, and `Q` is strictly decreasing along `γ`. -/
theorem isFutureTimelike_of_isPathOn (hg : IsSpacetime g Y) (hW : IsTotallyNormal g W ρ L)
    {a : E n} (ha : a ∈ W) (hγ : IsPathOn (IsFutureCausal g Y) α β γ)
    (hγW : ∀ t ∈ Icc α β, γ t ∈ W) (h0 : IsFutureTimelike g Y a (L (a, γ α))) :
    (∀ t ∈ Icc α β, IsFutureTimelike g Y a (L (a, γ t))) ∧
      StrictAntiOn (fun r => form (g a) (L (a, γ r)) (L (a, γ r))) (Icc α β) := by
  have hαβ := hγ.lt
  set w : ℝ → E n := fun t => L (a, γ t)
  have hwc : ContinuousOn w (Icc α β) := hW.continuousOn_comp ha hγ.continuousOn hγW
  have key : ∀ τ ∈ Icc α β, (∀ t ∈ Ico α τ, IsFutureTimelike g Y a (w t)) →
      StrictAntiOn (fun r => form (g a) (w r) (w r)) (Icc α τ) := by
    intro τ hτ hT
    rcases hτ.1.lt_or_eq with hατ | rfl
    · exact hW.strictAntiOn_form hg ha (hγ.restrict le_rfl hατ hτ.2)
        (fun t ht => hγW t ⟨ht.1, ht.2.trans hτ.2⟩) fun t ht => hT t ⟨ht.1.le, ht.2⟩
    · simp
  by_cases hall : ∀ t ∈ Icc α β, IsFutureTimelike g Y a (w t)
  · exact ⟨hall, key β ⟨hαβ.le, le_rfl⟩ fun t ht => hall t ⟨ht.1, ht.2.le⟩⟩
  exfalso
  push Not at hall
  set B := Icc α β ∩ w ⁻¹' {v | IsFutureTimelike g Y a v}ᶜ
  have hBc : IsClosed B := hwc.preimage_isClosed_of_isClosed isClosed_Icc
    (isOpen_setOf_isFutureTimelike hg a).isClosed_compl
  have hBne : B.Nonempty := by
    obtain ⟨t, ht, hnt⟩ := hall
    exact ⟨t, ht, hnt⟩
  have hBbdd : BddBelow B := ⟨α, fun t ht => ht.1.1⟩
  set τ := sInf B
  have hτ : τ ∈ B := hBc.csInf_mem hBne hBbdd
  have hbefore : ∀ t ∈ Ico α τ, IsFutureTimelike g Y a (w t) := by
    intro t ht
    by_contra h
    exact absurd (csInf_le hBbdd ⟨⟨ht.1, ht.2.le.trans hτ.1.2⟩, h⟩) (not_le.2 ht.2)
  have hατ : α < τ := lt_of_le_of_ne hτ.1.1 fun h => hτ.2 (by rw [← h]; exact h0)
  have hlt := key τ hτ.1 hbefore ⟨le_rfl, hατ.le⟩ ⟨hατ.le, le_rfl⟩ hατ
  have hneg : form (g a) (w τ) (w τ) < 0 := hlt.trans h0.timelike
  have hfut : form (g a) (w τ) (Y a) ≤ 0 := by
    have hc : ContinuousWithinAt (fun t => form (g a) (w t) (Y a)) (Icc α τ) τ :=
      ((continuous_form hg).comp_continuousOn (continuousOn_const.prodMk
        ((hwc.mono (Icc_subset_Icc le_rfl hτ.1.2)).prodMk continuousOn_const))) τ
        ⟨hατ.le, le_rfl⟩
    have ht : Tendsto (fun t => form (g a) (w t) (Y a)) (𝓝[<] τ)
        (𝓝 (form (g a) (w τ) (Y a))) := by
      rw [← nhdsWithin_Ioo_eq_nhdsLT hατ]
      exact hc.tendsto.mono_left (nhdsWithin_mono _ Ioo_subset_Icc_self)
    refine le_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsLT hατ] with t ht
    exact (hbefore t ⟨ht.1.le, ht.2⟩).future.le
  have hne : w τ ≠ 0 := fun h => by simp [h] at hneg
  exact hτ.2 ⟨hneg, (isFutureCausal_of_form_nonpos hg hneg.le hfut hne).future⟩

/-- Points arbitrarily close to `a ∈ W` with `L(a', a)` future timelike: `a' = exp_a (-r Y(a))`
for small `r > 0`. -/
theorem exists_past (hg : IsSpacetime g Y) (hW : IsTotallyNormal g W ρ L) {a : E n}
    (ha : a ∈ W) : ∃ c : ℝ → E n, Tendsto c (𝓝[>] 0) (𝓝 a) ∧
      ∀ᶠ r in 𝓝[>] (0 : ℝ), c r ∈ W ∧ IsFutureTimelike g Y (c r) (L (c r, a)) := by
  set T := Y a
  obtain ⟨hΞ, hΞ0⟩ := isGeodesic_expMap_smul hg a T
  set Ξ : ℝ → E n := fun z => expMap g a (z • T)
  have hD0 : (0 : ℝ) ∈ {z : ℝ | InExpDomain g a (z • T)} := by
    simpa using inExpDomain_zero (g := g) a
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hΞ.isOpen 0 hD0
  have hΞa : Ξ 0 = a := by simp [Ξ, expMap_zero hg]
  have hcont : ContinuousAt Ξ 0 :=
    hΞ.smooth.continuousOn.continuousAt (hΞ.isOpen.mem_nhds hD0)
  have hdcont : ContinuousAt (deriv Ξ) 0 :=
    hΞ.contDiffOn_deriv.continuousOn.continuousAt (hΞ.isOpen.mem_nhds hD0)
  have hneg : Tendsto (fun r : ℝ => -r) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((continuous_neg.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds)
  have hc : Tendsto (fun r => Ξ (-r)) (𝓝[>] 0) (𝓝 a) := by
    rw [← hΞa]
    exact hcont.tendsto.comp hneg
  refine ⟨fun r => Ξ (-r), hc, ?_⟩
  have e1 : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < δ :=
    nhdsWithin_le_nhds (Iio_mem_nhds hδ)
  have e2 : ∀ᶠ r in 𝓝[>] (0 : ℝ), Ξ (-r) ∈ W := hc.eventually (hW.isOpen.mem_nhds ha)
  have e3 : ∀ᶠ r in 𝓝[>] (0 : ℝ), r • deriv Ξ (-r) ∈ ball (0 : E n) ρ := by
    have : Tendsto (fun r : ℝ => r • deriv Ξ (-r)) (𝓝[>] 0) (𝓝 ((0 : ℝ) • deriv Ξ 0)) :=
      (tendsto_id.mono_left nhdsWithin_le_nhds).smul (hdcont.tendsto.comp hneg)
    rw [zero_smul] at this
    exact this.eventually (ball_mem_nhds _ (hW.pos ha))
  filter_upwards [e1, e2, e3, self_mem_nhdsWithin] with r hr1 hr2 hr3 hr4
  have hr4 : (0 : ℝ) < r := hr4
  have hσ := hΞ.comp_affine r (-r)
  have hsub : Icc (0 : ℝ) 1 ⊆ (fun s => r * s + -r) ⁻¹' {z : ℝ | InExpDomain g a (z • T)} := by
    intro s hs
    refine hball ?_
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    constructor <;> nlinarith [hs.1, hs.2]
  have he := hσ.expMap_eq hg hsub
  have h0 : r * 0 + -r ∈ {z : ℝ | InExpDomain g a (z • T)} := hsub (left_mem_Icc.2 zero_le_one)
  rw [hΞ.deriv_comp_affine h0] at he
  simp only [mul_zero, zero_add, mul_one, add_neg_cancel] at he
  have hL : L (Ξ (-r), a) = r • deriv Ξ (-r) :=
    hW.injOn _ hr2 (hW.mem_ball _ hr2 a ha) hr3 (by rw [hW.expMap_inv _ hr2 a ha, he, hΞa])
  refine ⟨hr2, ?_⟩
  show IsFutureTimelike g Y (Ξ (-r)) (L (Ξ (-r), a))
  rw [hL]
  have hT : IsFutureTimelike g Y (Ξ 0) (deriv Ξ 0) := by
    rw [hΞa, hΞ0]
    exact ⟨hg.globallyHyperbolic.timeOrientation.timelike a,
      hg.globallyHyperbolic.timeOrientation.timelike a⟩
  have hJ : Icc (-r) 0 ⊆ {z : ℝ | InExpDomain g a (z • T)} := fun z hz =>
    hball (by rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]; constructor <;>
      linarith [hz.1, hz.2])
  exact (hΞ.isFutureTimelike hg hJ ordConnected_Icc ⟨by linarith, le_rfl⟩ hT
    ⟨le_rfl, by linarith⟩).smul hr4

/-- O'Neill, Lemma 5.33, causal case: along a future causal curve in `W` from `a`, `L(a, γ β)`
lies in the closed future cone of `a`. -/
theorem form_nonpos_of_isPathOn (hg : IsSpacetime g Y) (hW : IsTotallyNormal g W ρ L)
    (hγ : IsPathOn (IsFutureCausal g Y) α β γ) (hγW : ∀ t ∈ Icc α β, γ t ∈ W) :
    form (g (γ α)) (L (γ α, γ β)) (L (γ α, γ β)) ≤ 0 ∧
      form (g (γ α)) (L (γ α, γ β)) (Y (γ α)) ≤ 0 := by
  have hαβ := hγ.lt
  have ha := hγW α ⟨le_rfl, hαβ.le⟩
  have hb := hγW β ⟨hαβ.le, le_rfl⟩
  obtain ⟨c, hc, hev⟩ := hW.exists_past hg ha
  have hT : ∀ᶠ r in 𝓝[>] (0 : ℝ), IsFutureTimelike g Y (c r) (L (c r, γ β)) := by
    filter_upwards [hev] with r hr
    exact (hW.isFutureTimelike_of_isPathOn hg hr.1 hγ hγW hr.2).1 β ⟨hαβ.le, le_rfl⟩
  have hL : Tendsto (fun r => L (c r, γ β)) (𝓝[>] 0) (𝓝 (L (γ α, γ β))) :=
    (hW.continuousAt ha hb).tendsto.comp (hc.prodMk_nhds tendsto_const_nhds)
  have hY : Tendsto (fun r => Y (c r)) (𝓝[>] 0) (𝓝 (Y (γ α))) :=
    (hg.globallyHyperbolic.timeOrientation.continuous.tendsto _).comp hc
  constructor
  · refine le_of_tendsto (((continuous_form hg).tendsto _).comp
      (hc.prodMk_nhds (hL.prodMk_nhds hL))) ?_
    filter_upwards [hT] with r hr
    exact hr.timelike.le
  · refine le_of_tendsto (((continuous_form hg).tendsto _).comp
      (hc.prodMk_nhds (hL.prodMk_nhds hY))) ?_
    filter_upwards [hT] with r hr
    exact hr.future.le

/-- There are no closed future causal curves in `W`. -/
theorem apply_ne_of_isPathOn (hg : IsSpacetime g Y) (hW : IsTotallyNormal g W ρ L)
    (hγ : IsPathOn (IsFutureCausal g Y) α β γ) (hγW : ∀ t ∈ Icc α β, γ t ∈ W) :
    γ β ≠ γ α := by
  have hαβ := hγ.lt
  obtain ⟨c, -, hev⟩ := hW.exists_past hg (hγW α ⟨le_rfl, hαβ.le⟩)
  obtain ⟨r, hr⟩ := hev.exists
  have := (hW.isFutureTimelike_of_isPathOn hg hr.1 hγ hγW hr.2).2 ⟨le_rfl, hαβ.le⟩
    ⟨hαβ.le, le_rfl⟩ hαβ
  intro h
  simp only [h] at this
  exact lt_irrefl _ this

/-- Along a future causal curve in `W` from `a`, `L(a, γ β)` is future causal. -/
theorem isFutureCausal_of_isPathOn (hg : IsSpacetime g Y) (hW : IsTotallyNormal g W ρ L)
    (hγ : IsPathOn (IsFutureCausal g Y) α β γ) (hγW : ∀ t ∈ Icc α β, γ t ∈ W) :
    IsFutureCausal g Y (γ α) (L (γ α, γ β)) := by
  have hαβ := hγ.lt
  have ha := hγW α ⟨le_rfl, hαβ.le⟩
  have hb := hγW β ⟨hαβ.le, le_rfl⟩
  obtain ⟨h1, h2⟩ := hW.form_nonpos_of_isPathOn hg hγ hγW
  refine isFutureCausal_of_form_nonpos hg h1 h2 fun h0 => hW.apply_ne_of_isPathOn hg hγ hγW ?_
  rw [← hW.expMap_inv _ ha _ hb, h0, expMap_zero hg]

/-- O'Neill, Lemma 5.33: `Q(t) = g_a(L(a, γ t), L(a, γ t))` is nonincreasing along a future
causal curve in `W` from `a`. -/
theorem antitoneOn_form (hg : IsSpacetime g Y) (hW : IsTotallyNormal g W ρ L)
    (hγ : IsPathOn (IsFutureCausal g Y) α β γ) (hγW : ∀ t ∈ Icc α β, γ t ∈ W) :
    AntitoneOn (fun r => form (g (γ α)) (L (γ α, γ r)) (L (γ α, γ r))) (Icc α β) :=
  hW.antitoneOn_form' hg (hγW α ⟨le_rfl, hγ.lt.le⟩) hγ hγW fun _ ht => Or.inr
    (hW.isFutureCausal_of_isPathOn hg (hγ.restrict le_rfl ht.1 ht.2.le)
      fun s hs => hγW s ⟨hs.1, hs.2.trans ht.2.le⟩)

/-- The radial null case of O'Neill, Lemma 5.33: if `L(a, γ β)` is not timelike along a future
causal curve `γ` in `W` from `a = γ α`, then `γ` is a monotone reparametrization
`t ↦ exp_a (λ(t) u)`, `u = L(a, γ β)`, of the radial null geodesic, and its velocities are null. -/
theorem isFutureTimelike_or_radial (hg : IsSpacetime g Y) (hW : IsTotallyNormal g W ρ L)
    (hγ : IsPathOn (IsFutureCausal g Y) α β γ) (hγW : ∀ t ∈ Icc α β, γ t ∈ W) :
    IsFutureTimelike g Y (γ α) (L (γ α, γ β)) ∨
      (IsFutureCausal g Y (γ α) (L (γ α, γ β)) ∧
        form (g (γ α)) (L (γ α, γ β)) (L (γ α, γ β)) = 0 ∧
        (∃ lam : ℝ → ℝ, MonotoneOn lam (Icc α β) ∧ ContinuousOn lam (Icc α β) ∧ lam α = 0 ∧
          lam β = 1 ∧ ∀ t ∈ Icc α β, γ t = expMap g (γ α) (lam t • L (γ α, γ β))) ∧
        ∀ x y, α ≤ x → x < y → y ≤ β → IsPathPiece (IsFutureCausal g Y) x y γ →
          ∀ t ∈ Ioo x y, form (g (γ t)) (derivWithin γ (Icc x y) t)
            (derivWithin γ (Icc x y) t) = 0) := by
  have hαβ := hγ.lt
  have ha : γ α ∈ W := hγW α ⟨le_rfl, hαβ.le⟩
  have hu := hW.isFutureCausal_of_isPathOn hg hγ hγW
  by_cases hT : IsFutureTimelike g Y (γ α) (L (γ α, γ β))
  · exact Or.inl hT
  right
  have hnull : form (g (γ α)) (L (γ α, γ β)) (L (γ α, γ β)) = 0 :=
    le_antisymm hu.causal (not_lt.1 fun h => hT ⟨h, hu.future⟩)
  have hwfc : ∀ t ∈ Ioc α β, IsFutureCausal g Y (γ α) (L (γ α, γ t)) := fun t ht =>
    hW.isFutureCausal_of_isPathOn hg (hγ.restrict le_rfl ht.1 ht.2)
      fun s hs => hγW s ⟨hs.1, hs.2.trans ht.2⟩
  have hwα : L (γ α, γ α) = 0 := hW.inv_self hg ha
  have hF0 : ∀ t ∈ Icc α β, form (g (γ α)) (L (γ α, γ t)) (L (γ α, γ t)) = 0 := by
    intro t ht
    refine le_antisymm ?_ ?_
    · rcases ht.1.lt_or_eq with h | h
      · exact (hwfc t ⟨h, ht.2⟩).causal
      · rw [← h, hwα, form_zero_left]
    · have := hW.antitoneOn_form hg hγ hγW ht ⟨hαβ.le, le_rfl⟩ ht.2
      simp only at this
      rwa [hnull] at this
  have hvel : ∀ x y, α ≤ x → x < y → y ≤ β → IsPathPiece (IsFutureCausal g Y) x y γ →
      ∀ t ∈ Ioo x y, form (g (γ t)) (derivWithin γ (Icc x y) t)
        (derivWithin γ (Icc x y) t) = 0 ∧
      ∃ κ > (0 : ℝ), HasDerivAt (fun r => L (γ α, γ r)) (κ • L (γ α, γ t)) t := by
    intro x y hx hxy hy hp t ht
    have htα : t ∈ Ioc α β := ⟨hx.trans_lt ht.1, (ht.2.trans_le hy).le⟩
    have hγt := hγW t ⟨htα.1.le, htα.2⟩
    have hmem := hW.mem_ball _ ha _ hγt
    have hdom := hW.inExpDomain _ ha _ hmem
    obtain ⟨w', hw', hdw'⟩ := hW.hasDerivWithinAt_inv hg ha (s := univ)
      (hp.hasDerivAt ht).hasDerivWithinAt hγt
    rw [hasDerivWithinAt_univ] at hw'
    have hFd := hW.hasDerivAt_form_of_isPathPiece hg ha hp ht hγt
    have hF0' : HasDerivAt (fun r => form (g (γ α)) (L (γ α, γ r)) (L (γ α, γ r))) 0 t :=
      (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq (eventually_of_mem
        (Ioo_mem_nhds ht.1 ht.2) fun r hr => hF0 r ⟨hx.trans hr.1.le, hr.2.le.trans hy⟩)
    have hRv : form (g (γ t)) (fderiv ℝ (expMap g (γ α)) (L (γ α, γ t)) (L (γ α, γ t)))
        (derivWithin γ (Icc x y) t) = 0 := by
      have := hFd.unique hF0'
      linarith
    have hR := hdom.isFutureCausal_fderiv hg (hwfc t htα)
    rw [hW.expMap_inv _ ha _ hγt] at hR
    have hRR : form (g (γ t)) (fderiv ℝ (expMap g (γ α)) (L (γ α, γ t)) (L (γ α, γ t)))
        (fderiv ℝ (expMap g (γ α)) (L (γ α, γ t)) (L (γ α, γ t))) = 0 := by
      have := form_fderiv_expMap_radial hg hdom (L (γ α, γ t))
      rw [hW.expMap_inv _ ha _ hγt] at this
      rw [this]
      exact hF0 t ⟨htα.1.le, htα.2⟩
    obtain ⟨κ, hκ, hvκ⟩ :=
      hR.eq_smul_of_form_eq_zero hg ((isPathPiece_iff.1 hp).2 t (Ioo_subset_Icc_self ht)) hRR hRv
    refine ⟨by rw [hvκ, form_smul_left, form_smul_right, hRR, mul_zero, mul_zero], κ, hκ, ?_⟩
    have hw'κ : w' = κ • L (γ α, γ t) :=
      (hW.bijective _ ha _ hmem).1 (by rw [hdw', map_smul, ← hvκ])
    rwa [hw'κ] at hw'
  refine ⟨hu, hnull, ?_, fun x y hx hxy hy hp t ht => (hvel x y hx hxy hy hp t ht).1⟩
  set φ : ℝ → ℝ := fun r => -form (g (γ α)) (L (γ α, γ r)) (Y (γ α)) with hφ_def
  have hφpos : ∀ t ∈ Ioc α β, 0 < φ t := fun t ht => by
    simp only [hφ_def]
    linarith [(hwfc t ht).future]
  have hwc : ContinuousOn (fun r => L (γ α, γ r)) (Icc α β) :=
    hW.continuousOn_comp ha hγ.continuousOn hγW
  have hφc : ContinuousOn φ (Icc α β) := by
    have := (continuous_form hg).comp_continuousOn
      ((continuousOn_const (c := γ α)).prodMk (hwc.prodMk (continuousOn_const (c := Y (γ α)))))
    simp only [Function.comp_def] at this
    exact this.neg
  have hφd : ∀ x y, α ≤ x → x < y → y ≤ β → IsPathPiece (IsFutureCausal g Y) x y γ →
      ∀ t ∈ Ioo x y, ∃ κ > (0 : ℝ), HasDerivAt (fun r => L (γ α, γ r)) (κ • L (γ α, γ t)) t ∧
        HasDerivAt φ (κ * φ t) t := by
    intro x y hx hxy hy hp t ht
    obtain ⟨-, κ, hκ, hd⟩ := hvel x y hx hxy hy hp t ht
    refine ⟨κ, hκ, hd, ?_⟩
    have := hasDerivWithinAt_univ.1 (HasDerivWithinAt.form (g (γ α)) hd.hasDerivWithinAt
      (hasDerivWithinAt_const t univ (Y (γ α))))
    convert this.neg using 1
    simp [hφ_def, form_smul_left]
  have hφu : 0 < φ β := hφpos β ⟨hαβ, le_rfl⟩
  have hDc : ∀ t ∈ Ioc α β, (φ t)⁻¹ • L (γ α, γ t) = (φ β)⁻¹ • L (γ α, γ β) := by
    intro t ht
    rcases ht.2.lt_or_eq with htβ | rfl
    swap
    · rfl
    have key := (hγ.restrict ht.1.le htβ le_rfl).rel_of_isPathPiece
      (R := fun r s => (φ r)⁻¹ • L (γ α, γ r) = (φ s)⁻¹ • L (γ α, γ s)) (fun _ => rfl)
      (fun _ _ _ _ _ h1 h2 => h1.trans h2) ?_ t β le_rfl htβ.le le_rfl
    · exact key
    intro x y hx hxy hy hp
    have hxα : α < x := ht.1.trans_le hx
    ext i
    have hcont : ContinuousOn (fun r => ((φ r)⁻¹ • L (γ α, γ r)) i) (Icc x y) := by
      have hsub : Icc x y ⊆ Icc α β := Icc_subset_Icc hxα.le hy
      have h1 : ContinuousOn (fun r => (φ r)⁻¹) (Icc x y) :=
        (hφc.mono hsub).inv₀ fun r hr => (hφpos r ⟨hxα.trans_le hr.1, hr.2.trans hy⟩).ne'
      have h2 : ContinuousOn (fun r => L (γ α, γ r) i) (Icc x y) :=
        (EuclideanSpace.proj i : E n →L[ℝ] ℝ).continuous.comp_continuousOn (hwc.mono hsub)
      exact (h1.mul h2).congr fun r _ => by simp
    have hderiv : ∀ r ∈ Ioo x y, HasDerivAt (fun r => ((φ r)⁻¹ • L (γ α, γ r)) i) 0 r := by
      intro r hr
      obtain ⟨κ, -, hd, hφr⟩ := hφd x y (ht.1.le.trans hx) hxy hy hp r hr
      have hpos := hφpos r ⟨hxα.trans hr.1, (hr.2.trans_le hy).le⟩
      have h3 := (hφr.inv hpos.ne').smul hd
      have h0 : (φ r)⁻¹ • κ • L (γ α, γ r) + (-(κ * φ r) / φ r ^ 2) • L (γ α, γ r) = 0 := by
        rw [smul_smul, ← add_smul]
        convert zero_smul ℝ (L (γ α, γ r)) using 2
        field_simp
        ring
      have h3' : HasDerivAt (fun r => (φ r)⁻¹ • L (γ α, γ r)) 0 r := by
        convert h3 using 1
        rw [Pi.inv_apply, h0]
      have := (EuclideanSpace.proj i : E n →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt r h3'
      simp only [map_zero] at this
      exact this
    obtain ⟨c, -, hc⟩ := exists_hasDerivAt_eq_slope _ (fun _ => (0 : ℝ)) hxy hcont hderiv
    have hyx : y - x ≠ 0 := sub_ne_zero.2 hxy.ne'
    simp only at hc
    rw [eq_div_iff hyx, zero_mul] at hc
    exact (sub_eq_zero.1 hc.symm).symm
  refine ⟨fun r => φ r / φ β, ?_, hφc.div_const _, ?_, div_self hφu.ne', ?_⟩
  · refine hγ.monotoneOn_of_isPathPiece fun x y hx hxy hy hp => ?_
    have hsub : Icc x y ⊆ Icc α β := Icc_subset_Icc hx hy
    refine monotoneOn_of_deriv_nonneg (convex_Icc x y) ((hφc.mono hsub).div_const _) ?_ ?_ <;>
      rw [interior_Icc]
    · intro t ht
      obtain ⟨κ, -, -, hd⟩ := hφd x y hx hxy hy hp t ht
      exact (hd.div_const _).differentiableAt.differentiableWithinAt
    · intro t ht
      obtain ⟨κ, hκ, -, hd⟩ := hφd x y hx hxy hy hp t ht
      rw [(hd.div_const _).deriv]
      exact div_nonneg (mul_nonneg hκ.le (hφpos t ⟨hx.trans_lt ht.1, (ht.2.trans_le hy).le⟩).le)
        hφu.le
  · simp [hφ_def, hwα]
  · intro t ht
    rcases ht.1.lt_or_eq with hαt | rfl
    · have h := hDc t ⟨hαt, ht.2⟩
      have hpos := hφpos t ⟨hαt, ht.2⟩
      have hw : L (γ α, γ t) = (φ t / φ β) • L (γ α, γ β) := by
        calc L (γ α, γ t) = φ t • ((φ t)⁻¹ • L (γ α, γ t)) := by
              rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
          _ = (φ t / φ β) • L (γ α, γ β) := by rw [h, smul_smul, div_eq_mul_inv]
      rw [← hw, hW.expMap_inv _ ha _ (hγW t ht)]
    · simp [hφ_def, hwα, expMap_zero hg]

/-- Local push-up (O'Neill, Corollary 14.1, in `W`): `x ≪ γ(α)` implies `x ≪ γ(β)` for a future
causal curve `γ` in `W`. -/
theorem chronLT_of_chronLT_of_isPathOn (hg : IsSpacetime g Y) (hW : IsTotallyNormal g W ρ L)
    {x : E n} (hx : ChronLT g Y x (γ α)) (hγ : IsPathOn (IsFutureCausal g Y) α β γ)
    (hγW : ∀ t ∈ Icc α β, γ t ∈ W) : ChronLT g Y x (γ β) := by
  have hαβ := hγ.lt
  have hαW := hγW α ⟨le_rfl, hαβ.le⟩
  obtain ⟨c, hc, hc0, hc1⟩ := chronLT_iff.1 hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hW.isOpen _ hαW
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuousWithinAt_iff.1
    (hc.continuousOn 1 ⟨zero_le_one, le_rfl⟩) ε hε
  set s₁ := max (1 / 2) (1 - δ / 2)
  have hs₁ : 0 < s₁ ∧ s₁ < 1 :=
    ⟨lt_max_of_lt_left (by norm_num), max_lt (by norm_num) (by linarith)⟩
  have hcW : ∀ t ∈ Icc s₁ 1, c t ∈ W := by
    intro t ht
    refine hball ?_
    rw [← hc1]
    refine hδc ⟨hs₁.1.le.trans ht.1, ht.2⟩ ?_
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [le_max_right (1 / 2 : ℝ) (1 - δ / 2), ht.1, ht.2]
  set e := 1 + (β - α)
  have h₁ : IsPathOn (IsFutureCausal g Y) s₁ 1 c :=
    (hc.restrict hs₁.1.le hs₁.2 le_rfl).mono fun _ _ h => h.isFutureCausal
  have h₂ : IsPathOn (IsFutureCausal g Y) 1 e (fun t => γ (1 * t + (α - 1))) :=
    IsPathOn.comp_affine (by convert hγ using 1 <;> ring) one_pos fun _ _ h => by simpa using h
  have hpath := h₁.append h₂ (by simp [hc1])
  set d := fun t => if t ≤ 1 then c t else γ (1 * t + (α - 1))
  have hdW : ∀ t ∈ Icc s₁ e, d t ∈ W := by
    intro t ht
    by_cases h : t ≤ 1
    · simp only [d, h, ite_true]
      exact hcW t ⟨ht.1, h⟩
    · simp only [d, h, ite_false]
      exact hγW _ ⟨by linarith [not_le.1 h], by linarith [ht.2]⟩
  have hd0 : d s₁ = c s₁ := by simp [d, hs₁.2.le]
  have hde : d e = γ β := by
    have h1 : ¬ e ≤ 1 := by simp only [e]; linarith
    simp only [d, h1, ite_false, e]
    congr 1
    ring
  rcases hW.isFutureTimelike_or_radial hg hpath hdW with hT | ⟨-, -, -, hnull⟩
  · have hs₁W := hdW s₁ ⟨le_rfl, by linarith⟩
    have heW := hdW e ⟨by linarith, le_rfl⟩
    have h := (hW.inExpDomain _ hs₁W _ (hW.mem_ball _ hs₁W _ heW)).chronLT hg hT
    rw [hW.expMap_inv _ hs₁W _ heW, hd0, hde] at h
    have hxs : ChronLT g Y x (c s₁) := by
      have := chronLT_of_isPathOn (hc.restrict le_rfl hs₁.1 hs₁.2.le)
      rwa [hc0] at this
    exact hxs.trans h
  · obtain ⟨p, q, hp, hpq, hq, hpiece⟩ := hc.exists_isPathPiece hs₁.1.le hs₁.2 le_rfl
    have heq : EqOn d c (Icc p q) := fun t ht => by simp [d, ht.2.trans hq]
    have hpiece' : IsPathPiece (IsFutureCausal g Y) p q d :=
      (hpiece.mono fun _ _ h => h.isFutureCausal).congr heq
    have ht : (p + q) / 2 ∈ Ioo p q := ⟨by linarith, by linarith⟩
    have h0 := hnull p q hp hpq (hq.trans (by linarith)) hpiece' _ ht
    have hT := (isPathPiece_iff.1 hpiece).2 _ (Ioo_subset_Icc_self ht)
    rw [derivWithin_congr heq (heq (Ioo_subset_Icc_self ht)), heq (Ioo_subset_Icc_self ht)] at h0
    exact (lt_irrefl _ (h0 ▸ hT.timelike)).elim

/-- The time dual of `chronLT_of_chronLT_of_isPathOn`: `γ(β) ≪ z` implies `γ(α) ≪ z`. -/
theorem chronLT_of_isPathOn_of_chronLT (hg : IsSpacetime g Y) (hW : IsTotallyNormal g W ρ L)
    (hγ : IsPathOn (IsFutureCausal g Y) α β γ) (hγW : ∀ t ∈ Icc α β, γ t ∈ W) {z : E n}
    (hz : ChronLT g Y (γ β) z) : ChronLT g Y (γ α) z := by
  have h' : IsPathOn (IsFutureCausal g (-Y)) (-β) (-α) (fun t => γ (0 - t)) :=
    IsPathOn.comp_reflect (by simpa using hγ) fun _ _ h =>
      isFutureCausal_neg_iff.2 (by rwa [neg_neg])
  have hz' : ChronLT g (-Y) z ((fun t => γ (0 - t)) (-β)) := by simpa using hz.neg
  have := hW.chronLT_of_chronLT_of_isPathOn (γ := fun t => γ (0 - t)) (α := -β) (β := -α)
    hg.neg hz' h' fun t ht =>
    hγW _ ⟨by linarith [ht.2], by linarith [ht.1]⟩
  exact chronLT_neg_iff.1 (by simpa using this)

end IsTotallyNormal

end

end LorentzianCalderon
