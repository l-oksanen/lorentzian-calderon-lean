module

public import LorentzianCalderon.Causal.Form

public section

/-!
# Elementary causal theory

Paths with velocities in a cone (`IsPathOn`), their continuity, restriction, concatenation and affine
reparametrization; transitivity of `CausalLE` and `ChronLT`; time reversal `Y ↦ -Y`.

The central tool is `isPathOn_iff`, a description of paths without explicit partitions: a path
on `[a, b]` is smooth with admissible velocities on every subinterval avoiding a finite set of
break points.
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Set Filter

variable {n : ℕ}

/-! ### Cones of velocities -/

section Cones

variable {g : MatrixField n} {Y : E n → E n} {x v : E n} {c : ℝ}

/-- The velocity predicate `P` is invariant under positive rescaling of the velocity. -/
def ScaleInvariant (P : E n → E n → Prop) : Prop :=
  ∀ x v (c : ℝ), 0 < c → P x v → P x (c • v)

theorem scaleInvariant_iff {P : E n → E n → Prop} :
    ScaleInvariant P ↔
      ∀ x v (c : ℝ), 0 < c → P x v → P x (c • v) := Iff.rfl

lemma IsFutureCausal.smul (h : IsFutureCausal g Y x v) (hc : 0 < c) :
    IsFutureCausal g Y x (c • v) where
  ne_zero := smul_ne_zero hc.ne' h.ne_zero
  causal := by
    simpa using mul_nonpos_of_nonneg_of_nonpos hc.le
      (mul_nonpos_of_nonneg_of_nonpos hc.le h.causal)
  future := by simpa using mul_neg_of_pos_of_neg hc h.future

lemma IsFutureTimelike.smul (h : IsFutureTimelike g Y x v) (hc : 0 < c) :
    IsFutureTimelike g Y x (c • v) where
  timelike := by simpa using mul_neg_of_pos_of_neg hc (mul_neg_of_pos_of_neg hc h.timelike)
  future := by simpa using mul_neg_of_pos_of_neg hc h.future

lemma isFutureCausal_smul_iff (hc : 0 < c) :
    IsFutureCausal g Y x (c • v) ↔ IsFutureCausal g Y x v :=
  ⟨fun h => by simpa [smul_smul, hc.ne'] using h.smul (inv_pos.2 hc), fun h => h.smul hc⟩

lemma isFutureTimelike_smul_iff (hc : 0 < c) :
    IsFutureTimelike g Y x (c • v) ↔ IsFutureTimelike g Y x v :=
  ⟨fun h => by simpa [smul_smul, hc.ne'] using h.smul (inv_pos.2 hc), fun h => h.smul hc⟩

lemma scaleInvariant_isFutureCausal : ScaleInvariant (IsFutureCausal g Y) :=
  fun _ _ _ hc h => h.smul hc

lemma scaleInvariant_isFutureTimelike : ScaleInvariant (IsFutureTimelike g Y) :=
  fun _ _ _ hc h => h.smul hc

lemma IsFutureTimelike.ne_zero (h : IsFutureTimelike g Y x v) : v ≠ 0 := by
  rintro rfl
  simpa using h.timelike

lemma IsFutureTimelike.isFutureCausal (h : IsFutureTimelike g Y x v) :
    IsFutureCausal g Y x v :=
  ⟨h.ne_zero, h.timelike.le, h.future⟩

lemma isFutureCausal_neg_iff : IsFutureCausal g (-Y) x v ↔ IsFutureCausal g Y x (-v) := by
  constructor
  · intro h
    exact ⟨neg_ne_zero.2 h.ne_zero, by simpa using h.causal, by simpa using h.future⟩
  · intro h
    exact ⟨neg_ne_zero.1 h.ne_zero, by simpa using h.causal, by simpa using h.future⟩

lemma isFutureTimelike_neg_iff : IsFutureTimelike g (-Y) x v ↔ IsFutureTimelike g Y x (-v) := by
  constructor
  · intro h
    exact ⟨by simpa using h.timelike, by simpa using h.future⟩
  · intro h
    exact ⟨by simpa using h.timelike, by simpa using h.future⟩

end Cones

/-! ### Smooth pieces -/

section Piece

variable {P Q : E n → E n → Prop} {a b a' b' : ℝ} {γ γ' : ℝ → E n}

/-- `γ` is smooth on `[a, b]` with one-sided velocities satisfying `P`. -/
def IsPathPiece (P : E n → E n → Prop) (a b : ℝ) (γ : ℝ → E n) : Prop :=
  ContDiffOn ℝ ∞ γ (Icc a b) ∧ ∀ t ∈ Icc a b, P (γ t) (derivWithin γ (Icc a b) t)

theorem isPathPiece_iff {P : E n → E n → Prop} {a b : ℝ} {γ : ℝ → E n} :
    IsPathPiece P a b γ ↔
      ContDiffOn ℝ ∞ γ (Icc a b) ∧ ∀ t ∈ Icc a b, P (γ t) (derivWithin γ (Icc a b) t) := Iff.rfl

lemma IsPathPiece.mono_interval (h : IsPathPiece P a b γ) (ha : a ≤ a') (hab' : a' < b')
    (hb : b' ≤ b) : IsPathPiece P a' b' γ := by
  have hsub : Icc a' b' ⊆ Icc a b := Icc_subset_Icc ha hb
  refine ⟨h.1.mono hsub, fun t ht => ?_⟩
  rw [derivWithin_subset hsub (uniqueDiffOn_Icc hab' t ht)
    (h.1.differentiableOn (by simp) t (hsub ht))]
  exact h.2 t (hsub ht)

lemma IsPathPiece.congr (h : IsPathPiece P a b γ) (heq : EqOn γ' γ (Icc a b)) :
    IsPathPiece P a b γ' := by
  refine ⟨h.1.congr heq, fun t ht => ?_⟩
  rw [derivWithin_congr heq (heq ht), heq ht]
  exact h.2 t ht

lemma IsPathPiece.mono (h : IsPathPiece P a b γ) (hPQ : ∀ x v, P x v → Q x v) :
    IsPathPiece Q a b γ :=
  ⟨h.1, fun t ht => hPQ _ _ (h.2 t ht)⟩

lemma IsPathPiece.comp_affine {α β : ℝ} (h : IsPathPiece P a b γ) (hab' : a' < b')
    (hmaps : MapsTo (fun t => α * t + β) (Icc a' b') (Icc a b))
    (hPQ : ∀ x v, P x v → Q x (α • v)) :
    IsPathPiece Q a' b' (fun t => γ (α * t + β)) := by
  have hφ : ContDiff ℝ ∞ (fun t : ℝ => α * t + β) := by fun_prop
  refine ⟨h.1.comp hφ.contDiffOn hmaps, fun t ht => ?_⟩
  have hd : HasDerivWithinAt (fun t : ℝ => α * t + β) α (Icc a' b') t := by
    simpa using (((hasDerivAt_id t).const_mul α).add_const β).hasDerivWithinAt
  have hγ := (h.1.differentiableOn (by simp) _ (hmaps ht)).hasDerivWithinAt
  have := (hγ.scomp t hd hmaps).derivWithin (uniqueDiffOn_Icc hab' t ht)
  simp only [Function.comp_def] at this
  rw [this]
  exact hPQ _ _ (h.2 _ (hmaps ht))

end Piece

/-! ### Paths -/

section Path

variable {P Q : E n → E n → Prop} {a b c d : ℝ} {γ γ' γ₁ γ₂ : ℝ → E n}

/-- A partition-free description of paths: a path on `[a, b]` is smooth with admissible
velocities on every subinterval that avoids a finite set of break points. -/
theorem isPathOn_iff :
    IsPathOn P a b γ ↔ a < b ∧ ∃ F : Finset ℝ, ∀ x y, a ≤ x → x < y → y ≤ b →
      (∀ z ∈ F, z ∉ Ioo x y) → IsPathPiece P x y γ := by
  classical
  rw [isPathOn_def]
  constructor
  · rintro ⟨k, s, hs, hγ⟩
    have hab : a < b := by
      have := hs.strictMono (show (0 : Fin (k + 2)) < Fin.last (k + 1) from Fin.last_pos)
      rwa [hs.first, hs.last] at this
    refine ⟨hab, Finset.univ.image s, fun x y hax hxy hyb hF => ?_⟩
    obtain ⟨j, hj⟩ : ∃ j : Fin (k + 1), s j.castSucc ≤ x ∧ x < s j.succ := by
      by_contra hcon
      push Not at hcon
      have key : ∀ m (hm : m < k + 2), s ⟨m, hm⟩ ≤ x := by
        intro m
        induction m with
        | zero =>
          intro hm
          have : (⟨0, hm⟩ : Fin (k + 2)) = 0 := rfl
          rw [this, hs.first]
          exact hax
        | succ m ih => intro hm; exact hcon ⟨m, by omega⟩ (ih (by omega))
      have := key (k + 1) (by omega)
      rw [show (⟨k + 1, by omega⟩ : Fin (k + 2)) = Fin.last (k + 1) from rfl, hs.last] at this
      linarith
    have hy : y ≤ s j.succ := by
      by_contra hlt
      push Not at hlt
      exact hF _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)) ⟨hj.2, hlt⟩
    have hsm := hγ.smooth j
    have hvel := hγ.velocity j
    rw [piece_def] at hsm hvel
    exact (show IsPathPiece P _ _ γ from ⟨hsm, hvel⟩).mono_interval hj.1 hxy hy
  · rintro ⟨hab, F, hF⟩
    set G : Finset ℝ := insert a (insert b (F.filter (· ∈ Ioo a b))) with hG
    have haG : a ∈ G := by simp [G]
    have hbG : b ∈ G := by simp [G]
    have hmem : ∀ z ∈ G, a ≤ z ∧ z ≤ b := by
      intro z hz
      simp only [G, Finset.mem_insert, Finset.mem_filter, mem_Ioo] at hz
      rcases hz with rfl | rfl | ⟨-, h1, h2⟩
      · exact ⟨le_rfl, hab.le⟩
      · exact ⟨hab.le, le_rfl⟩
      · exact ⟨h1.le, h2.le⟩
    have hcard : 2 ≤ G.card := by
      have : ({a, b} : Finset ℝ) ⊆ G := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        exacts [haG, hbG]
      simpa [Finset.card_pair hab.ne] using Finset.card_le_card this
    obtain ⟨k, hk⟩ : ∃ k, G.card = k + 2 := ⟨G.card - 2, by omega⟩
    set s := G.orderEmbOfFin hk
    have hfirst : s 0 = a := by
      rw [show (0 : Fin (k + 2)) = ⟨0, by omega⟩ from rfl, Finset.orderEmbOfFin_zero hk (by omega)]
      exact le_antisymm (Finset.min'_le _ _ haG)
        (Finset.le_min' _ _ _ fun z hz => (hmem z hz).1)
    have hlast : s (Fin.last (k + 1)) = b := by
      rw [show Fin.last (k + 1) = ⟨k + 2 - 1, by omega⟩ from Fin.ext (by simp),
        Finset.orderEmbOfFin_last hk (by omega)]
      exact le_antisymm (Finset.max'_le _ _ _ fun z hz => (hmem z hz).2)
        (Finset.le_max' _ _ hbG)
    have hpiece : ∀ i : Fin (k + 1), IsPathPiece P (s i.castSucc) (s i.succ) γ := by
      intro i
      refine hF _ _ (hmem _ (Finset.orderEmbOfFin_mem _ _ _)).1
        (s.strictMono i.castSucc_lt_succ) (hmem _ (Finset.orderEmbOfFin_mem _ _ _)).2 ?_
      intro z hz hzI
      have hzG : z ∈ G := by
        have h1 := (hmem _ (Finset.orderEmbOfFin_mem G hk i.castSucc)).1
        have h2 := (hmem _ (Finset.orderEmbOfFin_mem G hk i.succ)).2
        simp only [G, Finset.mem_insert, Finset.mem_filter, mem_Ioo]
        exact Or.inr (Or.inr ⟨hz, by linarith [hzI.1], by linarith [hzI.2]⟩)
      obtain ⟨l, rfl⟩ : z ∈ range s := by
        rw [Finset.range_orderEmbOfFin]
        exact hzG
      have h1 := s.lt_iff_lt.1 hzI.1
      have h2 := s.lt_iff_lt.1 hzI.2
      rw [Fin.lt_def] at h1 h2
      simp only [Fin.val_castSucc, Fin.val_succ] at h1 h2
      omega
    exact ⟨k, s, ⟨s.strictMono, hfirst, hlast⟩,
      ⟨fun i => piece_def s i ▸ (hpiece i).1, fun i => piece_def s i ▸ (hpiece i).2⟩⟩

lemma IsPathOn.lt (h : IsPathOn P a b γ) : a < b :=
  (isPathOn_iff.1 h).1

lemma IsPathOn.isPathPiece_of_lt (h : IsPathOn P a b γ) :
    ∃ F : Finset ℝ, ∀ x y, a ≤ x → x < y → y ≤ b → (∀ z ∈ F, z ∉ Ioo x y) →
      IsPathPiece P x y γ :=
  (isPathOn_iff.1 h).2

lemma IsPathOn.mono (h : IsPathOn P a b γ) (hPQ : ∀ x v, P x v → Q x v) :
    IsPathOn Q a b γ := by
  obtain ⟨k, s, hs, hγ⟩ := isPathOn_def.1 h
  exact isPathOn_def.2 ⟨k, s, hs, ⟨hγ.smooth, fun i t ht => hPQ _ _ (hγ.velocity i t ht)⟩⟩

lemma IsPathOn.congr (h : IsPathOn P a b γ) (heq : EqOn γ' γ (Icc a b)) :
    IsPathOn P a b γ' := by
  obtain ⟨hab, F, hF⟩ := isPathOn_iff.1 h
  exact isPathOn_iff.2 ⟨hab, F, fun x y hax hxy hyb hz =>
    (hF x y hax hxy hyb hz).congr (heq.mono (Icc_subset_Icc hax hyb))⟩

/-- Restriction of a path to a subinterval. -/
lemma IsPathOn.restrict (h : IsPathOn P a b γ) (hac : a ≤ c) (hcd : c < d) (hdb : d ≤ b) :
    IsPathOn P c d γ := by
  obtain ⟨-, F, hF⟩ := isPathOn_iff.1 h
  exact isPathOn_iff.2 ⟨hcd, F, fun x y hcx hxy hyd hz =>
    hF x y (hac.trans hcx) hxy (hyd.trans hdb) hz⟩

/-- Concatenation of paths. -/
lemma IsPathOn.append (h₁ : IsPathOn P a b γ₁) (h₂ : IsPathOn P b c γ₂) (heq : γ₁ b = γ₂ b) :
    IsPathOn P a c (fun t => if t ≤ b then γ₁ t else γ₂ t) := by
  classical
  obtain ⟨hab, F₁, hF₁⟩ := isPathOn_iff.1 h₁
  obtain ⟨hbc, F₂, hF₂⟩ := isPathOn_iff.1 h₂
  refine isPathOn_iff.2 ⟨hab.trans hbc, insert b (F₁ ∪ F₂), fun x y hax hxy hyc hz => ?_⟩
  have hb := hz b (Finset.mem_insert_self _ _)
  have hz₁ : ∀ z ∈ F₁, z ∉ Ioo x y := fun z hz' => hz z (by simp [hz'])
  have hz₂ : ∀ z ∈ F₂, z ∉ Ioo x y := fun z hz' => hz z (by simp [hz'])
  by_cases hyb : y ≤ b
  · refine (hF₁ x y hax hxy hyb hz₁).congr fun t ht => ?_
    simp [ht.2.trans hyb]
  · have hbx : b ≤ x := by
      by_contra hxb
      exact hb ⟨lt_of_not_ge hxb, lt_of_not_ge hyb⟩
    refine (hF₂ x y hbx hxy hyc hz₂).congr fun t ht => ?_
    by_cases htb : t ≤ b
    · have : t = b := le_antisymm htb (hbx.trans ht.1)
      simp [this, heq]
    · simp [htb]

/-- Affine reparametrization with positive factor. -/
lemma IsPathOn.comp_affine {α β : ℝ} (h : IsPathOn P (α * a + β) (α * b + β) γ) (hα : 0 < α)
    (hPQ : ∀ x v, P x v → Q x (α • v)) :
    IsPathOn Q a b (fun t => γ (α * t + β)) := by
  classical
  obtain ⟨hab, F, hF⟩ := isPathOn_iff.1 h
  have hab' : a < b := by
    by_contra hba
    push Not at hba
    have := mul_le_mul_of_nonneg_left hba hα.le
    linarith
  refine isPathOn_iff.2 ⟨hab', F.image (fun z => (z - β) / α), fun x y hax hxy hyb hz => ?_⟩
  have hmono : ∀ {u w : ℝ}, u ≤ w → α * u + β ≤ α * w + β := fun huw => by
    have := mul_le_mul_of_nonneg_left huw hα.le
    linarith
  have hsmono : ∀ {u w : ℝ}, u < w → α * u + β < α * w + β := fun huw => by
    have := mul_lt_mul_of_pos_left huw hα
    linarith
  refine (hF (α * x + β) (α * y + β) (hmono hax) (hsmono hxy) (hmono hyb) ?_).comp_affine hxy
    (fun t ht => ⟨hmono ht.1, hmono ht.2⟩) hPQ
  intro z hzF hzI
  refine hz _ (Finset.mem_image_of_mem _ hzF) ⟨?_, ?_⟩
  · rw [lt_div_iff₀ hα]
    linarith [hzI.1]
  · rw [div_lt_iff₀ hα]
    linarith [hzI.2]

/-- Reparametrization by the reflection `t ↦ β - t`; velocities change sign. -/
lemma IsPathOn.comp_reflect {β : ℝ} (h : IsPathOn P (β - b) (β - a) γ)
    (hPQ : ∀ x v, P x v → Q x (-v)) :
    IsPathOn Q a b (fun t => γ (β - t)) := by
  classical
  obtain ⟨hab, F, hF⟩ := isPathOn_iff.1 h
  refine isPathOn_iff.2 ⟨by linarith, F.image (fun z => β - z), fun x y hax hxy hyb hz => ?_⟩
  have := (hF (β - y) (β - x) (by linarith) (by linarith) (by linarith) ?_).comp_affine
    (α := -1) (β := β) hxy (fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩)
    (fun x v hv => by simpa using hPQ x v hv)
  · exact this.congr fun t _ => by simp only; ring_nf
  · intro z hzF hzI
    exact hz _ (Finset.mem_image_of_mem _ hzF) ⟨by linarith [hzI.2], by linarith [hzI.1]⟩

/-- A path on `[a, b]` reparametrized on `[0, 1]`. -/
lemma IsPathOn.toUnit (h : IsPathOn P a b γ) (hP : ScaleInvariant P) :
    IsPathOn P 0 1 (fun t => γ ((b - a) * t + a)) := by
  have hab := h.lt
  refine IsPathOn.comp_affine (by convert h using 1 <;> ring) (by linarith)
    fun x v hv => hP x v _ (by linarith) hv

/-- A path on `[0, 1]` reparametrized on `[a, b]`. -/
lemma IsPathOn.ofUnit (h : IsPathOn P 0 1 γ) (hP : ScaleInvariant P) (hab : a < b) :
    IsPathOn P a b (fun t => γ ((b - a)⁻¹ * t + -(a / (b - a)))) := by
  have hba : 0 < b - a := by linarith
  refine IsPathOn.comp_affine ?_ (inv_pos.2 hba) fun x v hv => hP x v _ (inv_pos.2 hba) hv
  convert h using 1 <;> field_simp <;> ring

/-- A straight line `t ↦ x + t • v` with admissible velocity `v` is a path. -/
lemma isPathOn_line {x v : E n} (hab : a < b) (hP : ∀ t ∈ Icc a b, P (x + t • v) v) :
    IsPathOn P a b (fun t => x + t • v) := by
  refine isPathOn_iff.2 ⟨hab, ∅, fun y z hay hyz hzb _ => ⟨by fun_prop, fun t ht => ?_⟩⟩
  have hd : HasDerivWithinAt (fun t : ℝ => x + t • v) v (Icc y z) t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x |>.hasDerivWithinAt
  rw [hd.derivWithin (uniqueDiffOn_Icc hyz t ht)]
  exact hP t ⟨hay.trans ht.1, ht.2.trans hzb⟩

/-- Concatenation of paths on `[0, 1]`, reparametrized on `[0, 1]`. -/
theorem exists_isPathOn_trans (hP : ScaleInvariant P) (h₁ : IsPathOn P 0 1 γ₁)
    (h₂ : IsPathOn P 0 1 γ₂) (h : γ₁ 1 = γ₂ 0) :
    ∃ γ, IsPathOn P 0 1 γ ∧ γ 0 = γ₁ 0 ∧ γ 1 = γ₂ 1 := by
  have h₂' : IsPathOn P 1 2 (fun t => γ₂ (1 * t + -1)) :=
    IsPathOn.comp_affine (by convert h₂ using 1 <;> norm_num) one_pos (by simp)
  have h₃ := h₁.append h₂' (by norm_num [h])
  refine ⟨_, IsPathOn.comp_affine (α := 2) (β := 0) (by convert h₃ using 1 <;> norm_num)
    two_pos fun x v hv => hP x v 2 two_pos hv, by norm_num, by norm_num⟩

lemma IsPartitionOf.exists_mem_piece {k : ℕ} {a b : ℝ} {s : Fin (k + 2) → ℝ}
    (hs : IsPartitionOf a b s) {x : ℝ} (hx : x ∈ Icc a b) : ∃ i, x ∈ piece s i := by
  have key : ∀ m (hm : m < k + 2), x ≤ s ⟨m, hm⟩ → ∃ i, x ∈ piece s i := by
    intro m
    induction m with
    | zero =>
      intro hm hxm
      refine ⟨0, (piece_def s 0).symm ▸ ⟨?_, ?_⟩⟩
      · simpa [hs.first] using hx.1
      · exact hxm.trans (hs.strictMono.monotone (Fin.zero_le _))
    | succ m ih =>
      intro hm hxm
      by_cases h : x ≤ s ⟨m, by omega⟩
      · exact ih _ h
      · exact ⟨⟨m, by omega⟩, by rw [piece_def]; exact ⟨(not_le.1 h).le, hxm⟩⟩
  refine key (k + 1) (by omega) ?_
  rw [show (⟨k + 1, by omega⟩ : Fin (k + 2)) = Fin.last (k + 1) from rfl, hs.last]
  exact hx.2

/-- A path is continuous. -/
lemma IsPathOn.continuousOn {P : E n → E n → Prop} {a b : ℝ} {γ : ℝ → E n}
    (h : IsPathOn P a b γ) : ContinuousOn γ (Icc a b) := by
  obtain ⟨k, s, hs, hγ⟩ := isPathOn_def.1 h
  have hcover : Icc a b ⊆ ⋃ i, piece s i := fun x hx => mem_iUnion.2 (hs.exists_mem_piece hx)
  simp only [piece_def] at hcover
  exact (LocallyFinite.continuousOn_iUnion (locallyFinite_of_finite _) (fun i => isClosed_Icc)
    fun i => piece_def s i ▸ (hγ.smooth i).continuousOn).mono hcover

end Path

/-! ### Causal and chronological relations -/

section Relations

variable {g : MatrixField n} {Y : E n → E n} {p q r : E n} {a b : ℝ} {γ : ℝ → E n}

lemma isCausalCurve_iff {k : ℕ} {s : Fin (k + 2) → ℝ} :
    IsCausalCurve g Y p q s γ ↔ IsPartitionOf 0 1 s ∧
      IsPiecewisePath (IsFutureCausal g Y) s γ ∧ γ 0 = p ∧ γ 1 = q :=
  ⟨fun h => ⟨⟨h.partition.strictMono, h.partition.first, h.partition.last⟩,
      ⟨h.smooth, h.causal⟩, h.source, h.target⟩,
    fun ⟨hs, hγ, h0, h1⟩ => ⟨⟨hs.strictMono, hs.first, hs.last⟩, h0, h1, hγ.smooth,
      hγ.velocity⟩⟩

theorem causalLE_iff :
    CausalLE g Y p q ↔
      p = q ∨ ∃ γ, IsPathOn (IsFutureCausal g Y) 0 1 γ ∧ γ 0 = p ∧ γ 1 = q := by
  refine causalLE_def.trans (or_congr Iff.rfl ⟨?_, ?_⟩)
  · rintro ⟨k, s, γ, h⟩
    obtain ⟨hs, hγ, h0, h1⟩ := isCausalCurve_iff.1 h
    exact ⟨γ, isPathOn_def.2 ⟨k, s, hs, hγ⟩, h0, h1⟩
  · rintro ⟨γ, hγ, h0, h1⟩
    obtain ⟨k, s, hs, hγ⟩ := isPathOn_def.1 hγ
    exact ⟨k, s, γ, isCausalCurve_iff.2 ⟨hs, hγ, h0, h1⟩⟩

lemma IsCausalCurve.isPathOn {k : ℕ} {s : Fin (k + 2) → ℝ} (h : IsCausalCurve g Y p q s γ) :
    IsPathOn (IsFutureCausal g Y) 0 1 γ :=
  isPathOn_def.2 ⟨k, s, (isCausalCurve_iff.1 h).1, (isCausalCurve_iff.1 h).2.1⟩

theorem causalLE_of_isPathOn (h : IsPathOn (IsFutureCausal g Y) a b γ) :
    CausalLE g Y (γ a) (γ b) :=
  causalLE_iff.2 <| Or.inr ⟨_, h.toUnit scaleInvariant_isFutureCausal, by simp, by simp⟩

theorem chronLT_of_isPathOn (h : IsPathOn (IsFutureTimelike g Y) a b γ) :
    ChronLT g Y (γ a) (γ b) :=
  chronLT_iff.2 ⟨_, h.toUnit scaleInvariant_isFutureTimelike, by simp, by simp⟩

lemma ChronLT.exists_isPathOn (h : ChronLT g Y p q) (hab : a < b) :
    ∃ γ, IsPathOn (IsFutureTimelike g Y) a b γ ∧ γ a = p ∧ γ b = q := by
  obtain ⟨γ, hγ, h0, h1⟩ := chronLT_iff.1 h
  have hba : b - a ≠ 0 := by linarith
  refine ⟨_, hγ.ofUnit scaleInvariant_isFutureTimelike hab, ?_, ?_⟩
  · convert h0 using 2; field_simp; ring
  · convert h1 using 2; field_simp; ring

lemma CausalLE.exists_isPathOn (h : CausalLE g Y p q) (hpq : p ≠ q) (hab : a < b) :
    ∃ γ, IsPathOn (IsFutureCausal g Y) a b γ ∧ γ a = p ∧ γ b = q := by
  obtain ⟨γ, hγ, h0, h1⟩ := (causalLE_iff.1 h).resolve_left hpq
  have hba : b - a ≠ 0 := by linarith
  refine ⟨_, hγ.ofUnit scaleInvariant_isFutureCausal hab, ?_, ?_⟩
  · convert h0 using 2; field_simp; ring
  · convert h1 using 2; field_simp; ring

@[refl]
lemma CausalLE.refl (p : E n) : CausalLE g Y p p := causalLE_def.2 (Or.inl rfl)

theorem CausalLE.trans (hpq : CausalLE g Y p q) (hqr : CausalLE g Y q r) : CausalLE g Y p r := by
  rcases causalLE_iff.1 hpq with rfl | ⟨γ₁, h₁, h₁0, h₁1⟩
  · exact hqr
  rcases causalLE_iff.1 hqr with rfl | ⟨γ₂, h₂, h₂0, h₂1⟩
  · exact hpq
  obtain ⟨γ, hγ, h0, h1⟩ :=
    exists_isPathOn_trans scaleInvariant_isFutureCausal h₁ h₂ (h₁1.trans h₂0.symm)
  exact causalLE_iff.2 (Or.inr ⟨γ, hγ, h0.trans h₁0, h1.trans h₂1⟩)

theorem ChronLT.trans (hpq : ChronLT g Y p q) (hqr : ChronLT g Y q r) : ChronLT g Y p r := by
  obtain ⟨γ₁, h₁, h₁0, h₁1⟩ := chronLT_iff.1 hpq
  obtain ⟨γ₂, h₂, h₂0, h₂1⟩ := chronLT_iff.1 hqr
  obtain ⟨γ, hγ, h0, h1⟩ :=
    exists_isPathOn_trans scaleInvariant_isFutureTimelike h₁ h₂ (h₁1.trans h₂0.symm)
  exact chronLT_iff.2 ⟨γ, hγ, h0.trans h₁0, h1.trans h₂1⟩

theorem ChronLT.causalLE (h : ChronLT g Y p q) : CausalLE g Y p q := by
  obtain ⟨γ, hγ, h0, h1⟩ := chronLT_iff.1 h
  exact causalLE_iff.2 (Or.inr ⟨γ, hγ.mono fun _ _ hv => hv.isFutureCausal, h0, h1⟩)

lemma mem_causalFuture_self (p : E n) : p ∈ causalFuture g Y p :=
  mem_causalFuture.2 (CausalLE.refl p)

lemma mem_causalPast_self (p : E n) : p ∈ causalPast g Y p := mem_causalPast.2 (CausalLE.refl p)

lemma chronFuture_subset_causalFuture (p : E n) : chronFuture g Y p ⊆ causalFuture g Y p :=
  fun _ h => mem_causalFuture.2 (ChronLT.causalLE (mem_chronFuture.1 h))

lemma chronPast_subset_causalPast (p : E n) : chronPast g Y p ⊆ causalPast g Y p :=
  fun _ h => mem_causalPast.2 (ChronLT.causalLE (mem_chronPast.1 h))

lemma subset_causalFutureSet (A : Set (E n)) : A ⊆ causalFutureSet g Y A :=
  fun p hp => mem_causalFutureSet.2 ⟨p, hp, mem_causalFuture_self p⟩

lemma subset_causalPastSet (A : Set (E n)) : A ⊆ causalPastSet g Y A :=
  fun p hp => mem_causalPastSet.2 ⟨p, hp, mem_causalPast_self p⟩

/-! ### Time reversal -/

lemma CausalLE.neg (h : CausalLE g Y q p) : CausalLE g (-Y) p q := by
  rcases causalLE_iff.1 h with rfl | ⟨γ, hγ, h0, h1⟩
  · exact CausalLE.refl _
  refine causalLE_iff.2 (Or.inr ⟨fun t => γ (1 - t), ?_, by simpa using h1, by simpa using h0⟩)
  exact IsPathOn.comp_reflect (by simpa using hγ)
    fun x v hv => isFutureCausal_neg_iff.2 (by simpa using hv)

theorem causalLE_neg_iff : CausalLE g (-Y) p q ↔ CausalLE g Y q p :=
  ⟨fun h => by simpa using h.neg, CausalLE.neg⟩

lemma ChronLT.neg (h : ChronLT g Y q p) : ChronLT g (-Y) p q := by
  obtain ⟨γ, hγ, h0, h1⟩ := chronLT_iff.1 h
  refine chronLT_iff.2 ⟨fun t => γ (1 - t), ?_, by simpa using h1, by simpa using h0⟩
  exact IsPathOn.comp_reflect (by simpa using hγ)
    fun x v hv => isFutureTimelike_neg_iff.2 (by simpa using hv)

theorem chronLT_neg_iff : ChronLT g (-Y) p q ↔ ChronLT g Y q p :=
  ⟨fun h => by simpa using h.neg, ChronLT.neg⟩

lemma causalFuture_neg (p : E n) : causalFuture g (-Y) p = causalPast g Y p :=
  Set.ext fun _ => mem_causalFuture.trans (causalLE_neg_iff.trans mem_causalPast.symm)

lemma causalPast_neg (p : E n) : causalPast g (-Y) p = causalFuture g Y p :=
  Set.ext fun _ => mem_causalPast.trans (causalLE_neg_iff.trans mem_causalFuture.symm)

lemma chronFuture_neg (p : E n) : chronFuture g (-Y) p = chronPast g Y p :=
  Set.ext fun _ => mem_chronFuture.trans (chronLT_neg_iff.trans mem_chronPast.symm)

lemma chronPast_neg (p : E n) : chronPast g (-Y) p = chronFuture g Y p :=
  Set.ext fun _ => mem_chronPast.trans (chronLT_neg_iff.trans mem_chronFuture.symm)

lemma causalFutureSet_neg (A : Set (E n)) : causalFutureSet g (-Y) A = causalPastSet g Y A := by
  simp only [causalFutureSet_def, causalPastSet_def, causalFuture_neg]

lemma causalPastSet_neg (A : Set (E n)) : causalPastSet g (-Y) A = causalFutureSet g Y A := by
  simp only [causalFutureSet_def, causalPastSet_def, causalPast_neg]

lemma IsTimeOrientation.neg (h : IsTimeOrientation g Y) : IsTimeOrientation g (-Y) :=
  ⟨h.continuous.neg, fun x => by simpa using h.timelike x⟩

lemma IsGloballyHyperbolic.neg (h : IsGloballyHyperbolic g Y) : IsGloballyHyperbolic g (-Y) :=
  ⟨h.timeOrientation.neg, fun p q => by
    rw [causalFuture_neg, causalPast_neg, inter_comm]
    exact h.compact_diamond q p⟩

lemma IsSpacetime.neg (h : IsSpacetime g Y) : IsSpacetime g (-Y) :=
  ⟨h.two_le, h.smooth, h.lorentzian, h.globallyHyperbolic.neg, by
    obtain ⟨T, σ, hσ, h⟩ := h.exterior
    refine ⟨T, -σ, hσ.symm.imp (fun h => by rw [h]; norm_num) (fun h => by rw [h]),
      fun x hx => ⟨(h x hx).1, ?_⟩⟩
    have := (h x hx).2
    simp only [form_def, Pi.neg_apply, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul, neg_mul,
      mul_neg, neg_neg] at this ⊢
    exact this⟩

lemma IsSpacetime.det_ne_zero (hg : IsSpacetime g Y) (x : E n) : (g x).det ≠ 0 :=
  (hg.lorentzian x).det_neg.ne

lemma IsSpacetime.symm (hg : IsSpacetime g Y) (x : E n) : (g x)ᵀ = g x :=
  (hg.lorentzian x).symm

end Relations

end

end LorentzianCalderon
