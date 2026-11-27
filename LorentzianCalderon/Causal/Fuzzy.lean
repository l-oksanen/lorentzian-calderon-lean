module

public import LorentzianCalderon.Geometry.CausalClosed
public import LorentzianCalderon.Geometry.Lagrangian
public import LorentzianCalderon.Geometry.LocalCausality

public section

/-!
# Fuzzy chains and the bound on their lengths

A *fuzzy step* `z → z'` of size `ε` is a step of length `< ε` whose direction is within `ε` of a
future causal vector at a point within `ε` of `z`; a *fuzzy chain* is a finite sequence of such
steps. Every causal curve can be approximated by fuzzy chains, and fuzzy steps are open
conditions, which makes them suited to building time functions by taking suprema
(`Causal/FuzzyTime`) and mollifying (`Causal/Mollify`).

The main result is `exists_fuzzy_length_bound`: in a causal spacetime (`≤` antisymmetric), the
lengths of the fuzzy chains in a compact set `K` are bounded, for `ε` small. Its proof:

* *local slope* (`exists_slope`): a short fuzzy chain starting in `K` moves its end point
  by at least `κ` times its length, since a fixed linear form is `≥ κ‖w‖` on the future causal
  vectors near a point;
* *Lyapunov estimate* (`IsTotallyNormal.isFutureTimelike_of_tendsto`): in a totally normal set,
  `Q_a = g_a(L(a, ·), L(a, ·))` has derivative `2 g(P, ·)`, `P` the radial velocity, which is
  `≤ 0` on future causal vectors where `L(a, ·)` is future timelike; along fuzzy chains `Q_a`
  can thus increase only by `o(1)` times the length, so the future side of `a` persists in the
  limit `ε → 0`, and limits of short fuzzy chains are causally related
  (`causalLE_of_tendsto`);
* *uniform causality* (`exists_causal_gap`): by antisymmetry and closedness of `≤`,
  `x ≤ y ≤ x'` with `y` away from `x` keeps `x'` away from `x`;
* *assembly*: a long chain is cut into many pieces of length about `r`; the limits of the cut
  points are `≤`-increasing and consecutive ones are `κ r / 2` apart, but two of them are close
  by pigeonhole, contradicting uniform causality.
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Set Filter Metric

variable {n : ℕ} {g : MatrixField n} {Y : E n → E n}

/-- A fuzzy step of size `ε` from `z` to `z'`: `‖z' - z‖ < ε`, and `z' - z` is within relative
distance `ε` of a future causal vector `w` at a point `x` within distance `ε` of `z`. -/
structure IsFuzzyStep (g : MatrixField n) (Y : E n → E n) (ε : ℝ) (z z' : E n) : Prop where
  lt : ‖z' - z‖ < ε
  near : ∃ x w, dist x z < ε ∧ IsFutureCausal g Y x w ∧ ‖(z' - z) - w‖ < ε * ‖z' - z‖

/-- `c 0, …, c m` is a fuzzy chain of size `ε`. -/
def IsFuzzyChain (g : MatrixField n) (Y : E n → E n) (ε : ℝ) (m : ℕ) (c : ℕ → E n) : Prop :=
  ∀ i < m, IsFuzzyStep g Y ε (c i) (c (i + 1))

theorem isFuzzyChain_iff {g : MatrixField n} {Y : E n → E n} {ε : ℝ} {m : ℕ} {c : ℕ → E n} :
    IsFuzzyChain g Y ε m c ↔
      ∀ i < m, IsFuzzyStep g Y ε (c i) (c (i + 1)) := Iff.rfl

/-- The length `∑_{i < m} ‖c (i + 1) - c i‖` of the polygon `c 0, …, c m`. -/
def chainLength (m : ℕ) (c : ℕ → E n) : ℝ := ∑ i ∈ Finset.range m, ‖c (i + 1) - c i‖

theorem chainLength_def (m : ℕ) (c : ℕ → E n) :
    chainLength m c =
      ∑ i ∈ Finset.range m, ‖c (i + 1) - c i‖ := by rfl

/-! ### Elementary properties -/

/-- A fuzzy step of size `ε` is one of every larger size. -/
theorem IsFuzzyStep.mono {ε ε' : ℝ} {z z' : E n} (h : IsFuzzyStep g Y ε z z') (hε : ε ≤ ε') :
    IsFuzzyStep g Y ε' z z' := by
  obtain ⟨x, w, hx, hw, hd⟩ := h.near
  exact ⟨h.lt.trans_le hε, x, w, hx.trans_le hε, hw,
    hd.trans_le (mul_le_mul_of_nonneg_right hε (norm_nonneg _))⟩

/-- A fuzzy step has positive length. -/
theorem IsFuzzyStep.ne {ε : ℝ} {z z' : E n} (h : IsFuzzyStep g Y ε z z') : 0 < ‖z' - z‖ := by
  obtain ⟨x, w, hx, -, hd⟩ := h.near
  by_contra h1
  have : ‖z' - z‖ = 0 := le_antisymm (not_lt.1 h1) (norm_nonneg _)
  rw [this, mul_zero] at hd
  exact (norm_nonneg _).not_gt hd

/-- A fuzzy chain of size `ε` is one of every larger size. -/
theorem IsFuzzyChain.mono {ε ε' : ℝ} {m : ℕ} {c : ℕ → E n} (h : IsFuzzyChain g Y ε m c)
    (hε : ε ≤ ε') : IsFuzzyChain g Y ε' m c :=
  fun i hi => (h i hi).mono hε

/-- A piece `c a, …, c (a + m')` of a fuzzy chain is a fuzzy chain. -/
theorem IsFuzzyChain.shift {ε : ℝ} {m : ℕ} {c : ℕ → E n} (h : IsFuzzyChain g Y ε m c)
    {a m' : ℕ} (hm : a + m' ≤ m) : IsFuzzyChain g Y ε m' fun j => c (a + j) :=
  fun i hi => by simpa [add_assoc] using h (a + i) (by omega)

/-- The polygon of one point has length `0`. -/
theorem chainLength_zero (c : ℕ → E n) : chainLength 0 c = 0 := by simp [chainLength]

/-- The length grows by the last step. -/
theorem chainLength_succ (m : ℕ) (c : ℕ → E n) :
    chainLength (m + 1) c = chainLength m c + ‖c (m + 1) - c m‖ :=
  Finset.sum_range_succ _ _

/-- Lengths are nonnegative. -/
theorem chainLength_nonneg (m : ℕ) (c : ℕ → E n) : 0 ≤ chainLength m c :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- The length of an initial piece is at most the whole length. -/
theorem chainLength_mono {a b : ℕ} (hab : a ≤ b) (c : ℕ → E n) :
    chainLength a c ≤ chainLength b c :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hab)
    fun _ _ _ => norm_nonneg _

/-- The length of the piece `c a, …, c b`. -/
theorem chainLength_shift {a b : ℕ} (hab : a ≤ b) (c : ℕ → E n) :
    chainLength (b - a) (fun j => c (a + j)) = chainLength b c - chainLength a c := by
  have h := Finset.sum_range_add (fun i => ‖c (i + 1) - c i‖) a (b - a)
  rw [Nat.add_sub_cancel' hab] at h
  simp only [chainLength, h, add_assoc]
  ring

/-- The end points are at most the length apart. -/
theorem norm_sub_le_chainLength (m : ℕ) (c : ℕ → E n) : ‖c m - c 0‖ ≤ chainLength m c := by
  induction m with
  | zero => simp [chainLength_zero]
  | succ m ih =>
    rw [chainLength_succ]
    calc ‖c (m + 1) - c 0‖ = ‖(c m - c 0) + (c (m + 1) - c m)‖ := by congr 1; abel
      _ ≤ _ := (norm_add_le _ _).trans (by linarith)

/-- Every point of the polygon is within its length of the first one. -/
theorem dist_le_chainLength {m i : ℕ} (hi : i ≤ m) (c : ℕ → E n) :
    dist (c i) (c 0) ≤ chainLength m c := by
  rw [dist_eq_norm]
  exact (norm_sub_le_chainLength i c).trans (chainLength_mono hi c)

/-! ### Compactness -/

/-- `x ↦ g_{a x}(b x, c x)` is continuous. -/
theorem Continuous.form_apply (hg : IsSpacetime g Y) {X : Type*} [TopologicalSpace X]
    {a b c : X → E n} (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) :
    Continuous fun x => form (g (a x)) (b x) (c x) :=
  (continuous_form hg).comp (ha.prodMk (hb.prodMk hc))

/-- `x ↦ g_{a x}(b x, c x)` is continuous on `s`. -/
theorem ContinuousOn.form_apply (hg : IsSpacetime g Y) {X : Type*} [TopologicalSpace X]
    {s : Set X} {a b c : X → E n} (ha : ContinuousOn a s) (hb : ContinuousOn b s)
    (hc : ContinuousOn c s) : ContinuousOn (fun x => form (g (a x)) (b x) (c x)) s :=
  (continuous_form hg).comp_continuousOn (f := fun x => (a x, b x, c x)) (ha.prodMk (hb.prodMk hc))

/-- A positive continuous function on a compact set has a positive lower bound. -/
theorem exists_pos_le_of_isCompact {X : Type*} [TopologicalSpace X] {s : Set X} (hs : IsCompact s)
    {f : X → ℝ} (hf : ContinuousOn f s) (h : ∀ x ∈ s, 0 < f x) : ∃ δ > 0, ∀ x ∈ s, δ ≤ f x := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  obtain ⟨x, hx, hmin⟩ := hs.exists_isMinOn hne hf
  exact ⟨f x, h x hx, fun y hy => hmin hy⟩

/-- Uniform causality: if `x ≤ y ≤ x'` in `K` with `‖y - x‖ ≥ κ`, then `‖x' - x‖ ≥ δ`. -/
theorem exists_causal_gap (hg : IsSpacetime g Y)
    (hanti : ∀ p q, CausalLE g Y p q → CausalLE g Y q p → p = q) {K : Set (E n)}
    (hK : IsCompact K) {κ : ℝ} (hκ : 0 < κ) :
    ∃ δ > 0, ∀ x ∈ K, ∀ y ∈ K, ∀ x' ∈ K, CausalLE g Y x y → CausalLE g Y y x' →
      κ ≤ ‖y - x‖ → δ ≤ ‖x' - x‖ := by
  have hC := Facts.isClosed_causalLE hg
  set S := (K ×ˢ K ×ˢ K) ∩ ({p : E n × E n × E n | CausalLE g Y p.1 p.2.1} ∩
    {p | CausalLE g Y p.2.1 p.2.2} ∩ {p | κ ≤ ‖p.2.1 - p.1‖})
  have h1 : IsClosed {p : E n × E n × E n | CausalLE g Y p.1 p.2.1} :=
    hC.preimage (f := fun p : E n × E n × E n => (p.1, p.2.1)) (by fun_prop)
  have h2 : IsClosed {p : E n × E n × E n | CausalLE g Y p.2.1 p.2.2} :=
    hC.preimage (f := fun p : E n × E n × E n => (p.2.1, p.2.2)) (by fun_prop)
  have h3 : IsClosed {p : E n × E n × E n | κ ≤ ‖p.2.1 - p.1‖} :=
    isClosed_le continuous_const (by fun_prop)
  have hS : IsCompact S := (hK.prod (hK.prod hK)).inter_right ((h1.inter h2).inter h3)
  obtain ⟨δ, hδ, hle⟩ := exists_pos_le_of_isCompact hS (f := fun p => ‖p.2.2 - p.1‖) (by fun_prop)
    fun p hp => by
      obtain ⟨-, ⟨h1, h2⟩, h3⟩ := hp
      simp only [mem_ofPred_eq] at h1 h2 h3
      refine norm_pos_iff.2 (sub_ne_zero.2 fun h => ?_)
      rw [h] at h2
      have := hanti _ _ h1 h2
      rw [← this, sub_self, norm_zero] at h3
      linarith
  exact ⟨δ, hδ, fun x hx y hy x' hx' h1 h2 h3 =>
    hle (x, y, x') ⟨⟨hx, hy, hx'⟩, ⟨h1, h2⟩, h3⟩⟩

/-! ### Local slope -/

/-- Near each point `x` of `K`, the linear form `w ↦ -g_x(Y x, w)` is `≥ κ‖w‖` on future causal
vectors. -/
theorem exists_cone_bound (hg : IsSpacetime g Y) {K : Set (E n)} (hK : IsCompact K) :
    ∃ r > 0, ∃ κ > 0, ∀ x ∈ K, ∀ y, dist y x < r → ∀ w, IsFutureCausal g Y y w →
      κ * ‖w‖ ≤ -form (g x) (Y x) w := by
  have hYc := hg.globallyHyperbolic.timeOrientation.continuous
  have c1 : Continuous fun p : E n × E n => form (g p.1) p.2 p.2 :=
    Continuous.form_apply hg continuous_fst continuous_snd continuous_snd
  have c2 : Continuous fun p : E n × E n => form (g p.1) p.2 (Y p.1) :=
    Continuous.form_apply hg continuous_fst continuous_snd (hYc.comp continuous_fst)
  have c3 : Continuous fun p : E n × E n => -form (g p.1) (Y p.1) p.2 :=
    (Continuous.form_apply hg continuous_fst (hYc.comp continuous_fst) continuous_snd).neg
  set D := (K ×ˢ sphere (0 : E n) 1) ∩ ({p : E n × E n | form (g p.1) p.2 p.2 ≤ 0} ∩
    {p | form (g p.1) p.2 (Y p.1) ≤ 0})
  have hD : IsCompact D := (hK.prod (isCompact_sphere 0 1)).inter_right
    ((isClosed_le c1 continuous_const).inter (isClosed_le c2 continuous_const))
  obtain ⟨κ₁, hκ₁, hD'⟩ := exists_pos_le_of_isCompact hD c3.continuousOn fun p hp => by
    obtain ⟨⟨-, hp1⟩, hp2, hp3⟩ := hp
    simp only [mem_ofPred_eq] at hp2 hp3
    have hne : p.2 ≠ 0 := by
      rintro h
      rw [mem_sphere_zero_iff_norm, h, norm_zero] at hp1
      exact zero_ne_one hp1
    have hc := isFutureCausal_of_form_nonpos hg hp2 hp3 hne
    rw [form_comm (hg.lorentzian p.1).symm]
    linarith [hc.future]
  have q1 : Continuous fun q : E n × E n × E n => q.2.1 := continuous_fst.comp continuous_snd
  have q2 : Continuous fun q : E n × E n × E n => q.2.2 := continuous_snd.comp continuous_snd
  have d1 : Continuous fun q : E n × E n × E n => form (g q.2.1) q.2.2 q.2.2 :=
    Continuous.form_apply hg q1 q2 q2
  have d2 : Continuous fun q : E n × E n × E n => form (g q.2.1) q.2.2 (Y q.2.1) :=
    Continuous.form_apply hg q1 q2 (hYc.comp q1)
  have d3 : Continuous fun q : E n × E n × E n => -form (g q.1) (Y q.1) q.2.2 :=
    (Continuous.form_apply hg continuous_fst (hYc.comp continuous_fst) q2).neg
  set C := (K ×ˢ cthickening 1 K ×ˢ sphere (0 : E n) 1) ∩
    ({q : E n × E n × E n | form (g q.2.1) q.2.2 q.2.2 ≤ 0} ∩
      {q | form (g q.2.1) q.2.2 (Y q.2.1) ≤ 0} ∩ {q | -form (g q.1) (Y q.1) q.2.2 ≤ κ₁ / 2})
  have hC : IsCompact C := (hK.prod (hK.cthickening.prod (isCompact_sphere 0 1))).inter_right
    (((isClosed_le d1 continuous_const).inter (isClosed_le d2 continuous_const)).inter
      (isClosed_le d3 continuous_const))
  obtain ⟨r₁, hr₁, hC'⟩ := exists_pos_le_of_isCompact hC
    (f := fun q : E n × E n × E n => dist q.2.1 q.1)
    ((continuous_fst.comp continuous_snd).dist continuous_fst).continuousOn fun q hq => by
      obtain ⟨⟨hq1, -, hq3⟩, ⟨hq4, hq5⟩, hq6⟩ := hq
      simp only [mem_ofPred_eq] at hq4 hq5 hq6
      refine dist_pos.2 fun h => ?_
      have := hD' (q.1, q.2.2) ⟨⟨hq1, hq3⟩, by simp only [mem_ofPred_eq]; rw [← h]; exact hq4,
        by simp only [mem_ofPred_eq]; rw [← h]; exact hq5⟩
      dsimp only at this
      linarith
  refine ⟨min r₁ 1, lt_min hr₁ one_pos, κ₁ / 2, by positivity, fun x hx y hy w hw => ?_⟩
  have hw0 : 0 < ‖w‖ := norm_pos_iff.2 hw.ne_zero
  obtain ⟨u, hu_def⟩ : ∃ u, u = ‖w‖⁻¹ • w := ⟨_, rfl⟩
  have hu : ‖u‖ = 1 := by
    rw [hu_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hw0.ne']
  by_contra hlt
  push Not at hlt
  have hlt' : -form (g x) (Y x) u ≤ κ₁ / 2 := by
    rw [hu_def, form_smul_right]
    have : -(‖w‖⁻¹ * form (g x) (Y x) w) = ‖w‖⁻¹ * -form (g x) (Y x) w := by ring
    rw [this, inv_mul_le_iff₀ hw0]
    linarith
  have hmem : (x, y, u) ∈ C := by
    simp only [C, mem_inter_iff, mem_prod, mem_ofPred_eq]
    refine ⟨⟨hx, mem_cthickening_of_dist_le y x 1 K hx
      (hy.le.trans (min_le_right _ _)), by rwa [mem_sphere_zero_iff_norm]⟩, ⟨?_, ?_⟩, hlt'⟩
    · rw [hu_def, form_smul_left, form_smul_right]
      exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 hw0.le)
        (mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 hw0.le) hw.causal)
    · rw [hu_def, form_smul_left]
      exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 hw0.le) hw.future.le
  have := hC' _ hmem
  dsimp only at this
  linarith [min_le_left r₁ 1]

/-- `|g_x(Y x, v)| ≤ B‖v‖` for `x ∈ K`. -/
theorem exists_form_bound (hg : IsSpacetime g Y) {K : Set (E n)} (hK : IsCompact K) :
    ∃ B > 0, ∀ x ∈ K, ∀ v, |form (g x) (Y x) v| ≤ B * ‖v‖ := by
  have hYc := hg.globallyHyperbolic.timeOrientation.continuous
  have c : Continuous fun p : E n × E n => form (g p.1) (Y p.1) p.2 :=
    Continuous.form_apply hg continuous_fst (hYc.comp continuous_fst) continuous_snd
  obtain ⟨C, hC⟩ := (hK.prod (isCompact_closedBall (0 : E n) 1)).exists_bound_of_continuousOn
    c.continuousOn
  refine ⟨max C 1, lt_max_of_lt_right one_pos, fun x hx v => ?_⟩
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hv0 : 0 < ‖v‖ := norm_pos_iff.2 hv
  have h := hC (x, ‖v‖⁻¹ • v) ⟨hx, by
    rw [mem_closedBall_zero_iff, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hv0.ne']⟩
  rw [Real.norm_eq_abs] at h
  dsimp only at h
  rw [form_smul_right, abs_mul, abs_inv, abs_norm, inv_mul_le_iff₀ hv0] at h
  nlinarith [le_max_left C 1]

/-- Local slope: a short fuzzy chain starting in `K` moves its end point by at least `κ` times
its length. -/
theorem exists_slope (hg : IsSpacetime g Y) {K : Set (E n)} (hK : IsCompact K) :
    ∃ ℓ > 0, ∃ κ > 0, ∃ ε₀ > 0, ∀ ε ≤ ε₀, ∀ (m : ℕ) (c : ℕ → E n), IsFuzzyChain g Y ε m c →
      c 0 ∈ K → chainLength m c ≤ ℓ → κ * chainLength m c ≤ ‖c m - c 0‖ := by
  obtain ⟨r, hr, κ, hκ, hcone⟩ := exists_cone_bound hg hK
  obtain ⟨B, hB, hbound⟩ := exists_form_bound hg hK
  refine ⟨r / 2, by positivity, κ / (2 * B), by positivity,
    min (r / 2) (κ / (2 * (κ + B))), by positivity, ?_⟩
  intro ε hε m c hc hc0 hlen
  have hεr : ε ≤ r / 2 := hε.trans (min_le_left _ _)
  have hεκ : ε * (κ + B) ≤ κ / 2 := by
    have := hε.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  set φ : E n → ℝ := fun v => -form (g (c 0)) (Y (c 0)) v with hφ
  have key : ∀ j ≤ m, κ / 2 * chainLength j c ≤ φ (c j - c 0) := by
    intro j
    induction j with
    | zero => intro _; simp [φ, chainLength_zero]
    | succ j ih =>
      intro hj
      have ih := ih (by omega)
      have hs := hc j (by omega)
      obtain ⟨x, w, hx, hw, hd⟩ := hs.near
      have hlt := hs.lt
      have hε0 : 0 ≤ ε := dist_nonneg.trans hx.le
      set Δ := c (j + 1) - c j
      have hcj : dist (c j) (c 0) ≤ r / 2 :=
        (dist_le_chainLength (by omega : j ≤ m) c).trans hlen
      have hxr : dist x (c 0) < r := by
        linarith [dist_triangle x (c j) (c 0)]
      have h1 := hcone (c 0) hc0 x hxr w hw
      have h2 := hbound (c 0) hc0 (Δ - w)
      have hsplit : φ (c (j + 1) - c 0) = φ (c j - c 0) + φ w + φ (Δ - w) := by
        have : c (j + 1) - c 0 = (c j - c 0) + (w + (Δ - w)) := by simp only [Δ]; abel
        simp only [φ, this, form_add_right]
        ring
      have hw' : ‖Δ‖ - ‖Δ - w‖ ≤ ‖w‖ := by
        have := norm_sub_norm_le Δ (Δ - w)
        simp only [sub_sub_cancel] at this
        exact this
      have h3 : φ (Δ - w) ≥ -(B * ‖Δ - w‖) := by
        simp only [φ]
        linarith [le_abs_self (form (g (c 0)) (Y (c 0)) (Δ - w))]
      have h4 : (κ + B) * ‖Δ - w‖ ≤ κ / 2 * ‖Δ‖ := by
        calc (κ + B) * ‖Δ - w‖ ≤ (κ + B) * (ε * ‖Δ‖) := by gcongr
          _ = ε * (κ + B) * ‖Δ‖ := by ring
          _ ≤ κ / 2 * ‖Δ‖ := by gcongr
      rw [chainLength_succ, hsplit]
      nlinarith
  have h1 := key m le_rfl
  have h2 := hbound (c 0) hc0 (c m - c 0)
  have h3 : φ (c m - c 0) ≤ B * ‖c m - c 0‖ := (neg_le_abs _).trans h2
  have h4 : κ * chainLength m c ≤ 2 * B * ‖c m - c 0‖ := by linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  linarith

/-! ### The Lyapunov estimate -/

namespace IsTotallyNormal

variable {W : Set (E n)} {ρ : ℝ} {L : E n × E n → E n}

/-- `Q_a = g_a(L(a, ·), L(a, ·))` is smooth on `W`. -/
theorem contDiffOn_form_inv (hg : IsSpacetime g Y) (hW : IsTotallyNormal g W ρ L) {a : E n}
    (ha : a ∈ W) : ContDiffOn ℝ ∞ (fun y => form (g a) (L (a, y)) (L (a, y))) W := by
  have hL : ContDiffOn ℝ ∞ (fun y => L (a, y)) W :=
    hW.smooth.comp (contDiffOn_const.prodMk contDiffOn_id) fun y hy => ⟨ha, hy⟩
  exact (contDiff_form hg).comp_contDiffOn (contDiffOn_const.prodMk (hL.prodMk hL))

/-- `dQ_a(w) = 2 g(P, w) ≤ 0` for `w` future causal at a point `x` with `L(a, x)` future
timelike, `P` the radial velocity (O'Neill, Lemma 5.33). -/
theorem fderiv_form_inv_nonpos (hg : IsSpacetime g Y) (hW : IsTotallyNormal g W ρ L)
    {a x w : E n} (ha : a ∈ W) (hx : x ∈ W) (hax : IsFutureTimelike g Y a (L (a, x)))
    (hw : IsFutureCausal g Y x w) :
    fderiv ℝ (fun y => form (g a) (L (a, y)) (L (a, y))) x w ≤ 0 := by
  set f := fun y => form (g a) (L (a, y)) (L (a, y))
  have hγ : HasDerivAt (fun s : ℝ => x + s • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add x
  have hγ0 : x + (0 : ℝ) • w = x := by simp
  have h1 := hW.hasDerivWithinAt_form hg ha hγ.hasDerivWithinAt (s := univ) (by rwa [hγ0])
  rw [hγ0, hasDerivWithinAt_univ] at h1
  have hdiff : DifferentiableAt ℝ f x :=
    ((hW.contDiffOn_form_inv hg ha).differentiableOn (by simp)).differentiableAt
      (hW.isOpen.mem_nhds hx)
  have hfd : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • w) := by
    rw [hγ0]; exact hdiff.hasFDerivAt
  have h2 := hfd.comp_hasDerivAt (0 : ℝ) hγ
  rw [h2.unique h1]
  have hdom := hW.inExpDomain a ha _ (hW.mem_ball a ha _ hx)
  have hP := hdom.isFutureTimelike_fderiv hg hax
  rw [hW.expMap_inv a ha _ hx] at hP
  have := hP.form_neg (hg.lorentzian x) (hg.globallyHyperbolic.timeOrientation.timelike x) hw
  linarith

/-- The Lyapunov estimate in the limit: if fuzzy chains of size `εₖ → 0` and bounded length in a
compact `K ⊆ W` run from `zₖ → z` to `z'ₖ → z'`, and `L(a, z)` is future timelike, then so is
`L(a, z')`. -/
theorem isFutureTimelike_of_tendsto (hg : IsSpacetime g Y) (hW : IsTotallyNormal g W ρ L)
    {K : Set (E n)} (hK : IsCompact K) (hKW : K ⊆ W) {Λ₀ : ℝ} {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) {m : ℕ → ℕ} {c : ℕ → ℕ → E n}
    (hc : ∀ᶠ k in atTop, IsFuzzyChain g Y (ε k) (m k) (c k))
    (hcK : ∀ᶠ k in atTop, ∀ i ≤ m k, c k i ∈ K)
    (hlen : ∀ᶠ k in atTop, chainLength (m k) (c k) ≤ Λ₀) {z z' : E n}
    (hz : Tendsto (fun k => c k 0) atTop (𝓝 z))
    (hz' : Tendsto (fun k => c k (m k)) atTop (𝓝 z')) {a : E n} (ha : a ∈ W) (hza : z ∈ W)
    (haz : IsFutureTimelike g Y a (L (a, z))) : IsFutureTimelike g Y a (L (a, z')) := by
  set f := fun y => form (g a) (L (a, y)) (L (a, y)) with hf_def
  have hf := hW.contDiffOn_form_inv hg ha
  have hLc : ContinuousOn (fun y => L (a, y)) W :=
    hW.smooth.continuousOn.comp (continuousOn_const.prodMk continuousOn_id) fun y hy => ⟨ha, hy⟩
  set U := W ∩ (fun y => L (a, y)) ⁻¹' {v | IsFutureTimelike g Y a v}
  have hU : IsOpen U := hLc.isOpen_inter_preimage hW.isOpen (isOpen_setOf_isFutureTimelike hg a)
  set q := f z
  have hq : q < 0 := haz.timelike
  set h := fun y => form (g a) (L (a, y)) (Y a)
  have hhc : ContinuousOn h W :=
    ContinuousOn.form_apply hg continuousOn_const hLc continuousOn_const
  set A := (K ∩ f ⁻¹' Iic (q / 2)) ∩ (K ∩ h ⁻¹' Iic 0)
  have hAc : IsClosed A :=
    ((hf.continuousOn.mono hKW).preimage_isClosed_of_isClosed hK.isClosed isClosed_Iic).inter
      ((hhc.mono hKW).preimage_isClosed_of_isClosed hK.isClosed isClosed_Iic)
  have hA : IsCompact A := hK.of_isClosed_subset hAc fun y hy => hy.1.1
  have memA : ∀ y ∈ K, y ∈ U → f y ≤ q / 2 → y ∈ A := fun y hy hyU hfy =>
    ⟨⟨hy, hfy⟩, hy, (show IsFutureTimelike g Y a (L (a, y)) from hyU.2).future.le⟩
  have hAU : A ⊆ U := fun y hy => by
    have hyW := hKW hy.1.1
    refine ⟨hyW, ?_⟩
    have h1 : form (g a) (L (a, y)) (L (a, y)) < 0 :=
      lt_of_le_of_lt (show f y ≤ q / 2 from hy.1.2) (by linarith)
    have hne : L (a, y) ≠ 0 := by
      intro h0
      rw [h0, form_zero_left] at h1
      exact lt_irrefl _ h1
    exact ⟨h1, (isFutureCausal_of_form_nonpos hg h1.le hy.2.2 hne).future⟩
  obtain ⟨θ₁, hθ₁, hθ₁U⟩ := hA.exists_thickening_subset_open hU hAU
  obtain ⟨θ₀, hθ₀, hθ₀W⟩ := hK.exists_cthickening_subset_open hW.isOpen hKW
  set K₂ := cthickening θ₀ K
  have hK₂ : IsCompact K₂ := hK.cthickening
  have hf' : ContinuousOn (fderiv ℝ f) K₂ :=
    (hf.continuousOn_fderiv_of_isOpen hW.isOpen (by simp)).mono hθ₀W
  obtain ⟨M, hM⟩ := hK₂.exists_bound_of_continuousOn hf'
  set η := -q / (8 * (|Λ₀| + 1))
  have hη : 0 < η := div_pos (by linarith) (by positivity)
  have hηΛ : 2 * η * |Λ₀| ≤ -q / 4 := by
    have h8 : η * (8 * (|Λ₀| + 1)) = -q := div_mul_cancel₀ _ (by positivity)
    nlinarith [abs_nonneg Λ₀]
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ :=
    Metric.uniformContinuousOn_iff.1 (hK₂.uniformContinuousOn_of_continuous hf') η hη
  set e := min θ₁ (min (θ₀ / 3) (min (δ₁ / 2) (η / (|M| + 1))))
  have he : 0 < e := by positivity
  have he1 : e ≤ θ₁ := min_le_left _ _
  have he2 : e ≤ θ₀ / 3 := (min_le_right _ _).trans (min_le_left _ _)
  have he3 : e ≤ δ₁ / 2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have he4 : e ≤ η / (|M| + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have step : ∀ ε' < e, ∀ ξ ∈ A, ∀ ξ', IsFuzzyStep g Y ε' ξ ξ' →
      ξ' ∈ U ∧ f ξ' ≤ f ξ + 2 * η * ‖ξ' - ξ‖ := by
    intro ε' hε' ξ hξ ξ' hs
    obtain ⟨x, w, hx, hw, hd⟩ := hs.near
    have hlt := hs.lt
    have hε'0 : 0 < ε' := dist_nonneg.trans_lt hx
    have hxU : x ∈ U := hθ₁U (mem_thickening_iff.2 ⟨ξ, hξ, by linarith⟩)
    have hξ'U : ξ' ∈ U := hθ₁U (mem_thickening_iff.2 ⟨ξ, hξ, by rw [dist_eq_norm]; linarith⟩)
    have hξK : ξ ∈ K := hξ.1.1
    have hball : ball x (2 * ε') ⊆ K₂ := fun y hy => by
      refine mem_cthickening_of_dist_le y ξ θ₀ K hξK ?_
      have := dist_triangle y x ξ
      rw [Metric.mem_ball] at hy
      linarith
    have hxK₂ : x ∈ K₂ := hball (mem_ball_self (by positivity))
    have hdiff : ∀ y ∈ ball x (2 * ε'), DifferentiableAt ℝ f y := fun y hy =>
      (hf.differentiableOn (by simp) y (hθ₀W (hball hy))).differentiableAt
        (hW.isOpen.mem_nhds (hθ₀W (hball hy)))
    have hbnd : ∀ y ∈ ball x (2 * ε'), ‖fderiv ℝ f y - fderiv ℝ f x‖ ≤ η := fun y hy => by
      have := hδ₁' y (hball hy) x hxK₂ (by rw [Metric.mem_ball] at hy; linarith)
      rw [dist_eq_norm] at this
      exact this.le
    have hξb : ξ ∈ ball x (2 * ε') := by rw [Metric.mem_ball, dist_comm]; linarith
    have hξ'b : ξ' ∈ ball x (2 * ε') := by
      rw [Metric.mem_ball]
      have := dist_triangle ξ' ξ x
      rw [dist_eq_norm ξ' ξ, dist_comm ξ x] at this
      linarith
    have hmv := (convex_ball x (2 * ε')).norm_image_sub_le_of_norm_fderiv_le' hdiff hbnd hξb hξ'b
    have hneg : fderiv ℝ f x w ≤ 0 :=
      hW.fderiv_form_inv_nonpos hg ha (hθ₀W hxK₂) hxU.2 hw
    have hsplit : fderiv ℝ f x (ξ' - ξ) = fderiv ℝ f x w + fderiv ℝ f x ((ξ' - ξ) - w) := by
      rw [← map_add]
      congr 1
      abel
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x hxK₂)
    have hop : fderiv ℝ f x ((ξ' - ξ) - w) ≤ M * ‖(ξ' - ξ) - w‖ := by
      have h1 := (fderiv ℝ f x).le_opNorm ((ξ' - ξ) - w)
      rw [Real.norm_eq_abs] at h1
      exact (le_abs_self _).trans (h1.trans (mul_le_mul_of_nonneg_right (hM x hxK₂)
        (norm_nonneg _)))
    have hMε : ε' * M ≤ η := by
      have h1 : ε' ≤ η / (|M| + 1) := hε'.le.trans he4
      rw [le_div_iff₀ (by positivity), abs_of_nonneg hM0] at h1
      nlinarith
    have hfin : f ξ' - f ξ - fderiv ℝ f x (ξ' - ξ) ≤ η * ‖ξ' - ξ‖ :=
      (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact hmv)
    refine ⟨hξ'U, ?_⟩
    have h5 : M * ‖(ξ' - ξ) - w‖ ≤ η * ‖ξ' - ξ‖ := by
      calc M * ‖(ξ' - ξ) - w‖ ≤ M * (ε' * ‖ξ' - ξ‖) := by gcongr
        _ = ε' * M * ‖ξ' - ξ‖ := by ring
        _ ≤ η * ‖ξ' - ξ‖ := by gcongr
    linarith
  have hzU : z ∈ U := ⟨hza, haz⟩
  have e1 : ∀ᶠ k in atTop, ε k < e := hε.eventually (gt_mem_nhds he)
  have e2 : ∀ᶠ k in atTop, c k 0 ∈ U := hz.eventually (hU.mem_nhds hzU)
  have e3 : ∀ᶠ k in atTop, f (c k 0) ≤ 3 * q / 4 :=
    ((hf.continuousOn.continuousAt (hW.isOpen.mem_nhds hza)).tendsto.comp hz).eventually
      (ge_mem_nhds (by linarith : q < 3 * q / 4))
  have hend : ∀ᶠ k in atTop, c k (m k) ∈ A := by
    filter_upwards [hc, hcK, hlen, e1, e2, e3] with k hck hcKk hlenk he1 he2 he3
    have hbd : ∀ i ≤ m k, 2 * η * chainLength i (c k) ≤ -q / 4 := fun i hi => by
      have := (chainLength_mono hi (c k)).trans (hlenk.trans (le_abs_self _))
      nlinarith [chainLength_nonneg i (c k)]
    have claim : ∀ i ≤ m k, c k i ∈ U ∧ f (c k i) ≤ f (c k 0) + 2 * η * chainLength i (c k) := by
      intro i
      induction i with
      | zero => intro _; simp [chainLength_zero, he2]
      | succ i ih =>
        intro hi
        obtain ⟨hUi, hfi⟩ := ih (by omega)
        have hAi : c k i ∈ A :=
          memA _ (hcKk i (by omega)) hUi (by linarith [hbd i (by omega)])
        obtain ⟨h1, h2⟩ := step (ε k) he1 _ hAi _ (hck i (by omega))
        refine ⟨h1, ?_⟩
        rw [chainLength_succ]
        linarith
    obtain ⟨h1, h2⟩ := claim (m k) le_rfl
    exact memA _ (hcKk _ le_rfl) h1 (by linarith [hbd (m k) le_rfl])
  exact (hAU (hAc.mem_of_tendsto hz' hend)).2

/-- Limits of short fuzzy chains are causally related: if fuzzy chains of size `εₖ → 0` and
bounded length in a compact `K ⊆ W` run from `zₖ → z` to `z'ₖ → z'`, then `z ≤ z'`. -/
theorem causalLE_of_tendsto (hg : IsSpacetime g Y) (hW : IsTotallyNormal g W ρ L)
    {K : Set (E n)} (hK : IsCompact K) (hKW : K ⊆ W) {Λ₀ : ℝ} {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) {m : ℕ → ℕ} {c : ℕ → ℕ → E n}
    (hc : ∀ᶠ k in atTop, IsFuzzyChain g Y (ε k) (m k) (c k))
    (hcK : ∀ᶠ k in atTop, ∀ i ≤ m k, c k i ∈ K)
    (hlen : ∀ᶠ k in atTop, chainLength (m k) (c k) ≤ Λ₀) {z z' : E n}
    (hz : Tendsto (fun k => c k 0) atTop (𝓝 z))
    (hz' : Tendsto (fun k => c k (m k)) atTop (𝓝 z')) : CausalLE g Y z z' := by
  have hzK : z ∈ K := hK.isClosed.mem_of_tendsto hz (hcK.mono fun k hk => hk 0 (Nat.zero_le _))
  have hz'K : z' ∈ K := hK.isClosed.mem_of_tendsto hz' (hcK.mono fun k hk => hk _ le_rfl)
  obtain ⟨p, hp, hev⟩ := hW.exists_past hg (hKW hzK)
  refine (Facts.isClosed_causalLE hg).mem_of_tendsto (hp.prodMk_nhds tendsto_const_nhds) ?_
  filter_upwards [hev] with r hr
  have h := hW.isFutureTimelike_of_tendsto hg hK hKW hε hc hcK hlen hz hz' hr.1 (hKW hzK) hr.2
  have hdom := hW.inExpDomain _ hr.1 _ (hW.mem_ball _ hr.1 _ (hKW hz'K))
  have := (hdom.chronLT hg h).causalLE
  rwa [hW.expMap_inv _ hr.1 _ (hKW hz'K)] at this

end IsTotallyNormal

/-! ### The length bound -/

/-- In a causal spacetime (`≤` antisymmetric), the fuzzy chains of small size in a compact set
have bounded length. -/
theorem exists_fuzzy_length_bound (hg : IsSpacetime g Y)
    (hanti : ∀ p q, CausalLE g Y p q → CausalLE g Y q p → p = q) {K : Set (E n)}
    (hK : IsCompact K) :
    ∃ ε > 0, ∃ Λ, ∀ (m : ℕ) (c : ℕ → E n),
      IsFuzzyChain g Y ε m c → (∀ i ≤ m, c i ∈ K) → chainLength m c ≤ Λ := by
  obtain ⟨ℓ, hℓ, κ, hκ, ε₀, hε₀, hslope⟩ := exists_slope hg hK
  choose Wf ρf Lf hxW hWf using fun x : E n => exists_isTotallyNormal hg x
  obtain ⟨δW, hδW, hleb⟩ := lebesgue_number_lemma_of_metric hK (c := Wf)
    (fun x => (hWf x).isOpen) (fun x _ => mem_iUnion.2 ⟨x, hxW x⟩)
  obtain ⟨r, hr, hrℓ, hrδ⟩ : ∃ r > 0, 3 * r / 2 ≤ ℓ ∧ 3 * r / 2 ≤ δW / 4 :=
    ⟨min ℓ (δW / 4) / 2, by positivity, by linarith [min_le_left ℓ (δW / 4)],
      by linarith [min_le_right ℓ (δW / 4)]⟩
  obtain ⟨δ₀, hδ₀, hgap⟩ := exists_causal_gap hg hanti hK (κ := κ * r / 2) (by positivity)
  obtain ⟨t, -, htfin, hcover⟩ := finite_cover_balls_of_compact hK (half_pos hδ₀)
  obtain ⟨M, hM⟩ : ∃ M, M = htfin.toFinset.card := ⟨_, rfl⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨ε, hεpos, hε0, hεr, hεt⟩ : ∃ ε : ℕ → ℝ, (∀ k, 0 < ε k) ∧ (∀ k, ε k ≤ ε₀) ∧
      (∀ k, ε k ≤ r / 2) ∧ Tendsto ε atTop (𝓝 0) := by
    refine ⟨fun k => min (1 / ((k : ℝ) + 1)) (min ε₀ (r / 2)), fun k => by positivity,
      fun k => (min_le_right _ _).trans (min_le_left _ _),
      fun k => (min_le_right _ _).trans (min_le_right _ _), ?_⟩
    exact squeeze_zero (fun k => by positivity) (fun k => min_le_left _ _)
      tendsto_one_div_add_atTop_nhds_zero_nat
  choose m c hc hcK hlen using fun k => hcon (ε k) (hεpos k) (M * r)
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℕ → ℕ,
      ∀ k i, a k i = sInf {j | (i : ℝ) * r ≤ chainLength j (c k)} := ⟨_, fun _ _ => rfl⟩
  have hin : ∀ k, ∀ i ≤ M, m k ∈ {j | (i : ℝ) * r ≤ chainLength j (c k)} := fun k i hi => by
    have : (i : ℝ) ≤ M := by exact_mod_cast hi
    exact le_of_lt (lt_of_le_of_lt (by nlinarith) (hlen k))
  have ha_mem : ∀ k, ∀ i ≤ M, (i : ℝ) * r ≤ chainLength (a k i) (c k) := fun k i hi => by
    rw [ha]
    exact Nat.sInf_mem ⟨_, hin k i hi⟩
  have ha_le : ∀ k, ∀ i ≤ M, a k i ≤ m k := fun k i hi => by
    rw [ha]
    exact Nat.sInf_le (hin k i hi)
  have ha_lt : ∀ k, ∀ i ≤ M, chainLength (a k i) (c k) < i * r + ε k := by
    intro k i hi
    rcases Nat.eq_zero_or_pos (a k i) with h0 | hpos
    · rw [h0, chainLength_zero]
      have := hεpos k
      positivity
    obtain ⟨j, hj⟩ : ∃ j, a k i = j + 1 := ⟨a k i - 1, by omega⟩
    have hjnot : j ∉ {j | (i : ℝ) * r ≤ chainLength j (c k)} :=
      Nat.notMem_of_lt_sInf (by rw [← ha]; omega)
    have hjm : j < m k := by have := ha_le k i hi; omega
    have hs := (hc k j hjm).lt
    simp only [mem_ofPred_eq, not_le] at hjnot
    rw [hj, chainLength_succ]
    linarith
  have ha_mono : ∀ k i, i + 1 ≤ M → a k i ≤ a k (i + 1) := fun k i hi => by
    rw [ha k i]
    refine Nat.sInf_le ?_
    have := ha_mem k (i + 1) hi
    simp only [mem_ofPred_eq]
    push_cast at this
    linarith
  have hpiece : ∀ k i, i + 1 ≤ M →
      r / 2 ≤ chainLength (a k (i + 1)) (c k) - chainLength (a k i) (c k) ∧
        chainLength (a k (i + 1)) (c k) - chainLength (a k i) (c k) ≤ 3 * r / 2 := by
    intro k i hi
    have h1 := ha_mem k (i + 1) hi
    have h2 := ha_lt k (i + 1) hi
    have h3 := ha_mem k i (by omega)
    have h4 := ha_lt k i (by omega)
    have h5 := hεr k
    push_cast at h1 h2
    constructor <;> nlinarith
  obtain ⟨Z, -, φ, hφ, hZ⟩ := (isCompact_univ_pi fun _ : Fin (M + 1) => hK).tendsto_subseq
    (x := fun k (i : Fin (M + 1)) => c k (a k i)) fun k i _ => hcK k _ (ha_le k i (by omega))
  obtain ⟨z, hzdef⟩ : ∃ z : ℕ → E n, ∀ i (h : i < M + 1), z i = Z ⟨i, h⟩ :=
    ⟨fun i => if h : i < M + 1 then Z ⟨i, h⟩ else 0, fun i h => by simp [h]⟩
  have hz : ∀ i ≤ M, Tendsto (fun k => c (φ k) (a (φ k) i)) atTop (𝓝 (z i)) := by
    intro i hi
    rw [hzdef i (by omega)]
    have := tendsto_pi_nhds.1 hZ ⟨i, by omega⟩
    simpa [Function.comp_def] using this
  have hzK : ∀ i ≤ M, z i ∈ K := fun i hi =>
    hK.isClosed.mem_of_tendsto (hz i hi)
      (Eventually.of_forall fun k => hcK _ _ (ha_le _ i hi))
  have hstep : ∀ i, i + 1 ≤ M → CausalLE g Y (z i) (z (i + 1))
      ∧ κ * r / 2 ≤ ‖z (i + 1) - z i‖ := by
    intro i hi
    obtain ⟨m', hm'⟩ : ∃ m' : ℕ → ℕ, ∀ k, m' k = a (φ k) (i + 1) - a (φ k) i :=
      ⟨_, fun _ => rfl⟩
    obtain ⟨c', hc'⟩ : ∃ c' : ℕ → ℕ → E n, ∀ k j, c' k j = c (φ k) (a (φ k) i + j) :=
      ⟨_, fun _ _ => rfl⟩
    have hc'fun : ∀ k, c' k = fun j => c (φ k) (a (φ k) i + j) := fun k => funext (hc' k)
    have hc'0 : ∀ k, c' k 0 = c (φ k) (a (φ k) i) := fun k => by rw [hc', add_zero]
    have hc'm : ∀ k, c' k (m' k) = c (φ k) (a (φ k) (i + 1)) := fun k => by
      rw [hc', hm', Nat.add_sub_cancel' (ha_mono _ i hi)]
    have hc'chain : ∀ k, IsFuzzyChain g Y (ε (φ k)) (m' k) (c' k) := fun k => by
      rw [hc'fun, hm']
      exact (hc (φ k)).shift (by have := ha_mono (φ k) i hi; have := ha_le (φ k) (i + 1) hi; omega)
    have hc'len : ∀ k, chainLength (m' k) (c' k) =
        chainLength (a (φ k) (i + 1)) (c (φ k)) - chainLength (a (φ k) i) (c (φ k)) := fun k => by
      rw [hc'fun, hm']
      exact chainLength_shift (ha_mono _ i hi) _
    constructor
    · obtain ⟨x, hx⟩ := hleb _ (hzK i (by omega))
      refine (hWf x).causalLE_of_tendsto hg (isCompact_closedBall (z i) (δW / 2))
        ((closedBall_subset_ball (half_lt_self hδW)).trans hx) (hεt.comp hφ.tendsto_atTop)
        (Λ₀ := 3 * r / 2) (Eventually.of_forall hc'chain) ?_
        (Eventually.of_forall fun k => by rw [hc'len]; exact (hpiece _ i hi).2)
        ((hz i (by omega)).congr fun k => (hc'0 k).symm)
        ((hz (i + 1) hi).congr fun k => (hc'm k).symm)
      filter_upwards [(hz i (by omega)).eventually (ball_mem_nhds _ (by positivity : 0 < δW / 4))]
        with k hk j hj
      rw [mem_closedBall]
      have h1 := dist_le_chainLength hj (c' k)
      rw [hc'len, hc'0] at h1
      have h2 := (hpiece (φ k) i hi).2
      linarith [dist_triangle (c' k j) (c (φ k) (a (φ k) i)) (z i)]
    · have hb : ∀ k, κ * r / 2 ≤ ‖c (φ k) (a (φ k) (i + 1)) - c (φ k) (a (φ k) i)‖ := by
        intro k
        have h0 := hpiece (φ k) i hi
        have := hslope (ε (φ k)) (hε0 _) (m' k) (c' k) (hc'chain k)
          (by rw [hc'0]; exact hcK _ _ (ha_le _ i (by omega)))
          (by rw [hc'len]; linarith)
        rw [hc'len, hc'm, hc'0] at this
        nlinarith
      exact ge_of_tendsto' (((hz (i + 1) hi).sub (hz i (by omega))).norm) hb
  have hchain : ∀ i j, i ≤ j → j ≤ M →
      CausalLE g Y (z i) (z j) := by
    intro i j hij hj
    induction j, hij using Nat.le_induction with
    | base => exact CausalLE.refl _
    | succ j hij ih => exact (ih (by omega)).trans (hstep j hj).1
  have hfar : ∀ i j, i < j → j ≤ M →
      δ₀ ≤ dist (z i) (z j) := by
    intro i j hij hj
    rw [dist_comm, dist_eq_norm]
    exact hgap _ (hzK i (by omega)) _ (hzK (i + 1) (by omega)) _ (hzK j hj)
      (hstep i (by omega)).1 (hchain (i + 1) j hij hj) (hstep i (by omega)).2
  have hcen : ∀ i : Fin (M + 1), ∃ y, y ∈ htfin.toFinset ∧ z i ∈ ball y (δ₀ / 2) := by
    intro i
    have hi : z i ∈ K := hzK i (by omega)
    obtain ⟨y, hy, hZy⟩ := mem_iUnion₂.1 (hcover hi)
    exact ⟨y, htfin.mem_toFinset.2 hy, hZy⟩
  choose f hf1 hf2 using hcen
  obtain ⟨i, -, j, -, hij, hfij⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.univ) (t := htfin.toFinset) (by simp [← hM]) (f := f) fun i _ => hf1 i
  have hd : dist (z i) (z j) < δ₀ := by
    have h1 := hf2 i
    have h2 := hf2 j
    rw [hfij, mem_ball] at h1
    rw [mem_ball] at h2
    linarith [dist_triangle_right (z i) (z j) (f j)]
  have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hij' with h | h
  · linarith [hfar i j h (by omega)]
  · linarith [hfar j i h (by omega), dist_comm (z i) (z j)]

end

end LorentzianCalderon
