module

public import LorentzianCalderon.Induction.Setup
public import LorentzianCalderon.Induction.Lift

public section

/-!
# No escape

Blueprint lemma `lem_no_escape`: if `Ψ` has the extension property `P(τ)`
(`ExtensionProperty`), then `Ψ` preserves the time orientation on `A_τ`
(`ExtensionProperty.isFutureTimelike_fderiv`) and maps `A_τ ∩ W` into `W`
(`ExtensionProperty.mapsTo_W`).

For the second part, lifts of the escaping curve are constructed on compact intervals
`[0, s]`; they stay in the compact set `{ψ ≥ ψ(q)} ∩ (W ∪ c'([0, s]))`, which gives the
continuation past the supremum of the parameters with a lift. A lift on `[0, s]` ends in `W`,
since it agrees with the escaping curve where it leaves `W`. So the escaping curve stays in the
compact set `Ψ({ψ ≥ ψ(q)} ∩ W)`, contradicting imprisonment for `g'`.
-/

namespace LorentzianCalderon

noncomputable section
open scoped ContDiff Matrix Topology
open Set Filter Matrix

variable {n : ℕ}

/-! ### Differentials and pullbacks -/

lemma D_mulVec (Ψ : E n → E n) (x w : E n) :
    D Ψ x *ᵥ w.ofLp = (fderiv ℝ Ψ x w).ofLp := by
  ext i
  rw [clm_apply_eq_sum (fderiv ℝ Ψ x) w]
  simp [D_def, mulVec, dotProduct, mul_comm]

lemma form_pullback {G G' J : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (h : G = Jᵀ * G' * J)
    (v w : E n) :
    form G v w = form G' (WithLp.toLp 2 (J *ᵥ v.ofLp)) (WithLp.toLp 2 (J *ᵥ w.ofLp)) := by
  rw [form_eq_dotProduct, form_eq_dotProduct, h, ← mulVec_mulVec, ← mulVec_mulVec,
    dotProduct_mulVec, vecMul_transpose]

lemma continuousOn_form {G : MatrixField n} {v w : E n → E n} {s : Set (E n)}
    (hG : ∀ i j, ContinuousOn (fun x => G x i j) s) (hv : ContinuousOn v s)
    (hw : ContinuousOn w s) : ContinuousOn (fun x => form (G x) (v x) (w x)) s := by
  have hc : ∀ (u : E n → E n), ContinuousOn u s → ∀ i, ContinuousOn (fun x => u x i) s :=
    fun u hu i => (EuclideanSpace.proj i : E n →L[ℝ] ℝ).continuous.comp_continuousOn hu
  simp only [form_def]
  exact continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ =>
    ((hc v hv i).mul (hG i j)).mul (hc w hw j)

namespace ExtensionProperty

variable {g g' : MatrixField n} {Y Y' : E n → E n} {ψ : E n → ℝ} {W : Set (E n)} {τ : ℝ}
  {Ψ : E n → E n}

lemma form_eq (h : ExtensionProperty g g' ψ W τ Ψ) {x : E n} (hx : x ∈ A ψ τ) (v w : E n) :
    form (g x) v w = form (g' (Ψ x)) (fderiv ℝ Ψ x v) (fderiv ℝ Ψ x w) := by
  rw [form_pullback (h.pullback x hx), D_mulVec, D_mulVec]

lemma injective_fderiv (h : ExtensionProperty g g' ψ W τ Ψ) (hg : ∀ x, IsLorentzian (g x))
    {x : E n} (hx : x ∈ A ψ τ) : Function.Injective (fderiv ℝ Ψ x) := by
  refine (injective_iff_map_eq_zero _).2 fun w hw => ?_
  have h0 : g x *ᵥ w.ofLp = 0 := by
    rw [h.pullback x hx, ← mulVec_mulVec, D_mulVec, hw]
    simp
  have := eq_zero_of_mulVec_eq_zero (hg x).det_neg.ne h0
  ext i
  simpa using congrFun this i

lemma fderiv_eq_id (h : ExtensionProperty g g' ψ W τ Ψ) (hψ : Continuous ψ) (hW : IsClosed W)
    {x : E n} (hx : x ∈ A ψ τ) (hxW : x ∉ W) : fderiv ℝ Ψ x = ContinuousLinearMap.id ℝ (E n) := by
  have hev : Ψ =ᶠ[𝓝 x] id := by
    filter_upwards [(isOpen_A hψ τ).mem_nhds hx, hW.isOpen_compl.mem_nhds hxW] with y hy hyW
    exact h.eq_self y hy hyW
  rw [hev.fderiv_eq, fderiv_id]

/-- **No escape**, first part: `Ψ` preserves the time orientation on `A_τ`. -/
theorem isFutureTimelike_fderiv (h : ExtensionProperty g g' ψ W τ Ψ) (hg : IsSpacetime g Y)
    (hg' : IsSpacetime g' Y') (hψ : Continuous ψ) (hW : IsClosed W)
    (hconn : IsPreconnected (A ψ τ)) (hne : (A ψ τ \ W).Nonempty)
    (hYY' : ∀ x ∉ W, ∀ v, IsFutureTimelike g Y x v → IsFutureTimelike g' Y' x v)
    {x : E n} (hx : x ∈ A ψ τ) {v : E n} (hv : IsFutureTimelike g Y x v) :
    IsFutureTimelike g' Y' (Ψ x) (fderiv ℝ Ψ x v) := by
  have hYt := hg.globallyHyperbolic.timeOrientation.timelike
  have hY't := hg'.globallyHyperbolic.timeOrientation.timelike
  set f : E n → ℝ := fun x => form (g' (Ψ x)) (fderiv ℝ Ψ x (Y x)) (Y' (Ψ x))
  have hU := isOpen_A hψ τ
  have hΨc : ContinuousOn Ψ (A ψ τ) := h.smooth.continuousOn
  have hf : ContinuousOn f (A ψ τ) := by
    refine continuousOn_form (fun i j => ?_) ?_ ?_
    · exact ((hg'.smooth i j).continuous.comp_continuousOn hΨc)
    · exact (h.smooth.continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply
        hg.globallyHyperbolic.timeOrientation.continuous.continuousOn
    · exact hg'.globallyHyperbolic.timeOrientation.continuous.comp_continuousOn hΨc
  have hf0 : ∀ y ∈ A ψ τ, f y ≠ 0 := fun y hy => by
    have htl : form (g' (Ψ y)) (fderiv ℝ Ψ y (Y y)) (fderiv ℝ Ψ y (Y y)) < 0 := by
      rw [← h.form_eq hy]
      exact hYt y
    exact (hg'.lorentzian _).form_ne_zero htl.le (by intro h0; rw [h0] at htl; simp at htl)
      (hY't _)
  have hneg : ∀ y ∈ A ψ τ, f y < 0 := by
    obtain ⟨y₀, hy₀, hy₀W⟩ := hne
    have hfy₀ : f y₀ < 0 := by
      simp only [f, h.fderiv_eq_id hψ hW hy₀ hy₀W, h.eq_self y₀ hy₀ hy₀W,
        ContinuousLinearMap.id_apply]
      exact (hYY' y₀ hy₀W _ ⟨hYt y₀, hYt y₀⟩).future
    intro y hy
    by_contra hfy
    obtain ⟨z, hz, hfz⟩ := hconn.intermediate_value hy₀ hy hf
      ⟨hfy₀.le, not_lt.1 hfy⟩
    exact hf0 z hz hfz
  have hu : IsFutureTimelike g' Y' (Ψ x) (fderiv ℝ Ψ x (Y x)) :=
    ⟨by rw [← h.form_eq hx]; exact hYt x, hneg x hx⟩
  refine hu.of_form_neg (hg'.lorentzian _) (hY't _) ?_ ?_
  · rw [← h.form_eq hx]
    exact hv.timelike
  · rw [← h.form_eq hx]
    exact hv.future

/-- The converse: vectors mapped to future-directed timelike vectors are future-directed
timelike. -/
theorem isFutureTimelike_of_fderiv (h : ExtensionProperty g g' ψ W τ Ψ) (hg : IsSpacetime g Y)
    (hg' : IsSpacetime g' Y') (hψ : Continuous ψ) (hW : IsClosed W)
    (hconn : IsPreconnected (A ψ τ)) (hne : (A ψ τ \ W).Nonempty)
    (hYY' : ∀ x ∉ W, ∀ v, IsFutureTimelike g Y x v → IsFutureTimelike g' Y' x v)
    {x : E n} (hx : x ∈ A ψ τ) {w : E n}
    (hw : IsFutureTimelike g' Y' (Ψ x) (fderiv ℝ Ψ x w)) : IsFutureTimelike g Y x w := by
  have hYt := hg.globallyHyperbolic.timeOrientation.timelike
  have hu := h.isFutureTimelike_fderiv hg hg' hψ hW hconn hne hYY' hx ⟨hYt x, hYt x⟩
  refine ⟨by rw [h.form_eq hx]; exact hw.timelike, ?_⟩
  rw [h.form_eq hx]
  exact hw.form_neg (hg'.lorentzian _) (hg'.globallyHyperbolic.timeOrientation.timelike _)
    hu.isFutureCausal

/-- **No escape**, second part: `Ψ (A_τ ∩ W) ⊆ W`. -/
theorem mapsTo_W (h : ExtensionProperty g g' ψ W τ Ψ) (hg : IsSpacetime g Y)
    (hg' : IsSpacetime g' Y') (hψ : IsCauchyTemporal g Y ψ) (hW : IsCompact W)
    (hconn : IsPreconnected (A ψ τ)) (hne : (A ψ τ \ W).Nonempty)
    (hYY' : ∀ x ∉ W, ∀ v, IsFutureTimelike g Y x v → IsFutureTimelike g' Y' x v)
    (hesc : ∀ x ∉ W, ∃ c : ℝ → E n, c 0 = x ∧ IsInextendibleRay (IsFutureTimelike g' Y') c ∧
      (∀ t, 0 ≤ t → c t ∉ W) ∧ Tendsto c atTop (cocompact (E n))) :
    MapsTo Ψ (A ψ τ ∩ W) W := by
  rintro q ⟨hqA, hqW⟩
  by_contra hx
  obtain ⟨c', hc'0, hray, hc'W, hc'K⟩ := hesc _ hx
  have hψc : Continuous ψ := hψ.smooth.continuous
  have hU := isOpen_A hψc τ
  have hinj : ∀ z ∈ A ψ τ, Function.Injective (fderiv ℝ Ψ z) :=
    fun z hz => h.injective_fderiv hg.lorentzian hz
  have hPQ : ∀ z ∈ A ψ τ, ∀ w, IsFutureTimelike g' Y' (Ψ z) (fderiv ℝ Ψ z w) →
      IsFutureTimelike g Y z w :=
    fun z hz w hw => h.isFutureTimelike_of_fderiv hg hg' hψc hW.isClosed hconn hne hYY' hz hw
  have hcont : ∀ s, 0 ≤ s → ContinuousOn c' (Icc 0 s) := fun s hs =>
    (hray.path (s + 1) (by linarith)).continuousOn.mono (Icc_subset_Icc le_rfl (by linarith))
  have hsup : ∀ z, ψ q ≤ ψ z → z ∈ A ψ τ := fun z hz => mem_A.2 (lt_of_lt_of_le (mem_A.1 hqA) hz)
  let IsLift : ℝ → (ℝ → E n) → Prop := fun s c => ContinuousOn c (Icc 0 s) ∧ c 0 = q ∧
    ∀ t ∈ Icc 0 s, c t ∈ A ψ τ ∧ Ψ (c t) = c' t
  have hlift_ψ : ∀ s c, IsLift s c → ∀ t ∈ Icc 0 s, ψ q ≤ ψ (c t) := by
    rintro s c ⟨hc, hc0, hcl⟩ t ht
    rcases ht.1.eq_or_lt with h0 | h0
    · rw [← h0, hc0]
    have hsub : Icc 0 t ⊆ Icc 0 s := Icc_subset_Icc le_rfl ht.2
    have hpath : IsPathOn (IsFutureTimelike g Y) 0 t c :=
      IsPathOn.of_comp hU h.smooth hinj hPQ (hray.path t h0) (hc.mono hsub)
        (fun u hu => (hcl u (hsub hu)).1) fun u hu => (hcl u (hsub hu)).2
    have := hψ.le_of_causalLE hg (causalLE_of_isPathOn
      (hpath.mono fun _ _ hv => hv.isFutureCausal))
    rwa [hc0] at this
  have hlift_W : ∀ s c, IsLift s c → ∀ t ∈ Icc 0 s, c t ∉ W → c t = c' t := by
    rintro s c ⟨-, -, hcl⟩ t ht htW
    rw [← (hcl t ht).2, h.eq_self _ (hcl t ht).1 htW]
  have hexists : ∀ s, 0 ≤ s → ∃ c, IsLift s c := by
    by_contra hcon
    push Not at hcon
    obtain ⟨b, hb0, hb⟩ := hcon
    set S := { s | ∃ c, IsLift s c } ∩ Icc 0 b
    have h0S : (0 : ℝ) ∈ S := by
      refine ⟨⟨fun _ => q, continuousOn_const, rfl, fun t ht => ?_⟩, le_rfl, hb0⟩
      obtain rfl : t = 0 := le_antisymm ht.2 ht.1
      exact ⟨hqA, hc'0.symm⟩
    have hbdd : BddAbove S := ⟨b, fun s hs => hs.2.2⟩
    set s₁ := sSup S
    have hs₁ : s₁ ∈ Icc 0 b := ⟨le_csSup hbdd h0S, csSup_le ⟨0, h0S⟩ fun s hs => hs.2.2⟩
    obtain ⟨u, -, hu, huS⟩ := exists_seq_tendsto_sSup ⟨0, h0S⟩ hbdd
    choose c hc using fun k => (huS k).1
    set z : ℕ → E n := fun k => c k (u k)
    set K := (W ∪ c' '' Icc 0 b) ∩ { z | ψ q ≤ ψ z }
    have hK : IsCompact K :=
      (hW.union ((isCompact_Icc).image_of_continuousOn (hcont b hb0))).inter_right
        (isClosed_le continuous_const hψc)
    have hzK : ∀ k, z k ∈ K := fun k => by
      have hk : u k ∈ Icc 0 (u k) := ⟨(huS k).2.1, le_rfl⟩
      refine ⟨?_, hlift_ψ _ _ (hc k) _ hk⟩
      by_cases hzW : z k ∈ W
      · exact Or.inl hzW
      · exact Or.inr ⟨u k, (huS k).2, (hlift_W _ _ (hc k) _ hk hzW).symm⟩
    obtain ⟨p, hpK, φ, hφ, hzp⟩ := hK.tendsto_subseq hzK
    have hpA : p ∈ A ψ τ := hsup p hpK.2
    have hc's₁ : Tendsto (c' ∘ u) atTop (𝓝 (c' s₁)) :=
      ((hcont b hb0) s₁ hs₁).tendsto.comp
        (tendsto_nhdsWithin_iff.2 ⟨hu, Eventually.of_forall fun k => (huS k).2⟩)
    have hΨp : Ψ p = c' s₁ := by
      have h1 : Tendsto (Ψ ∘ z ∘ φ) atTop (𝓝 (Ψ p)) :=
        ((h.smooth.continuousOn.continuousAt (hU.mem_nhds hpA)).tendsto).comp hzp
      have h2 : Ψ ∘ z ∘ φ = c' ∘ u ∘ φ := funext fun k =>
        ((hc (φ k)).2.2 _ ⟨(huS _).2.1, le_rfl⟩).2
      rw [h2] at h1
      exact tendsto_nhds_unique h1 (hc's₁.comp hφ.tendsto_atTop)
    obtain ⟨L, hL, hpL, hLU, -, -⟩ := exists_localInverse hU h.smooth hinj hpA
    have hev : ∀ᶠ t in 𝓝[Icc 0 (b + 1)] s₁, c' t ∈ L.target :=
      (hcont (b + 1) (by linarith)) s₁ ⟨hs₁.1, by linarith [hs₁.2]⟩
        (L.open_target.mem_nhds (by rw [← hΨp, ← hL]; exact L.map_source hpL))
    obtain ⟨ε, hε, hεL⟩ := Metric.mem_nhdsWithin_iff.1 hev
    have hεL' : ∀ t ∈ Icc 0 (b + 1), |t - s₁| < ε → c' t ∈ L.target := fun t ht hts =>
      hεL ⟨by rwa [Metric.mem_ball, Real.dist_eq], ht⟩
    obtain ⟨k, hk1, hk2⟩ := ((hu.comp hφ.tendsto_atTop).eventually
      (Metric.ball_mem_nhds s₁ hε)).and (hzp.eventually (L.open_source.mem_nhds hpL)) |>.exists
    simp only [Function.comp_apply] at hk1 hk2
    set t₀ := u (φ k)
    set c₀ := c (φ k)
    have ht₀ : t₀ ∈ Icc 0 b := (huS (φ k)).2
    have ht₀s₁ : t₀ ≤ s₁ := le_csSup hbdd (huS (φ k))
    have ht₀ε : s₁ - ε < t₀ := by
      rw [Real.dist_eq, abs_lt] at hk1
      linarith [hk1.1]
    set t₁ := min b (s₁ + ε / 2)
    have ht₀₁ : t₀ ≤ t₁ := le_min ht₀.2 (by linarith)
    have hc₀ := hc (φ k)
    have hc₀t₀ : L.symm (c' t₀) = c₀ t₀ := by
      rw [← (hc₀.2.2 t₀ ⟨ht₀.1, le_rfl⟩).2, ← hL, L.left_inv (by exact hk2)]
    have htgt : ∀ t ∈ Icc t₀ t₁, c' t ∈ L.target := fun t ht => by
      refine hεL' t ⟨ht₀.1.trans ht.1, by linarith [ht.2, min_le_left b (s₁ + ε / 2)]⟩ ?_
      rw [abs_lt]
      constructor <;> linarith [ht.1, ht.2, min_le_right b (s₁ + ε / 2)]
    set c₁ : ℝ → E n := fun t => if t ≤ t₀ then c₀ t else L.symm (c' t)
    have hlift₁ : IsLift t₁ c₁ := by
      refine ⟨?_, by simp only [c₁, ht₀.1, ite_true]; exact hc₀.2.1, fun t ht => ?_⟩
      · rw [← Icc_union_Icc_eq_Icc ht₀.1 ht₀₁]
        refine ContinuousOn.union_of_isClosed
          (hc₀.1.congr fun t ht => by
            simp only [c₁]
            split_ifs with h'
            · rfl
            · exact absurd ht.2 h') ?_ isClosed_Icc isClosed_Icc
        refine (L.continuousOn_symm.comp ((hcont t₁ (ht₀.1.trans ht₀₁)).mono
          (Icc_subset_Icc (ht₀.1) le_rfl)) htgt).congr fun t ht => ?_
        rcases ht.1.eq_or_lt with h' | h'
        · simp [c₁, ← h', hc₀t₀]
        · simp [c₁, not_le.2 h']
      · by_cases htt₀ : t ≤ t₀
        · simp only [c₁, htt₀, ite_true]
          exact hc₀.2.2 t ⟨ht.1, htt₀⟩
        · simp only [c₁, htt₀, ite_false]
          have := htgt t ⟨(not_le.1 htt₀).le, ht.2⟩
          refine ⟨hLU (L.map_target this), ?_⟩
          rw [← hL, L.right_inv this]
    have ht₁S : t₁ ∈ S := ⟨⟨c₁, hlift₁⟩, ht₀.1.trans ht₀₁, min_le_left _ _⟩
    have ht₁s₁ : t₁ ≤ s₁ := le_csSup hbdd ht₁S
    rcases le_total b (s₁ + ε / 2) with hb' | hb'
    · rw [show t₁ = b from min_eq_left hb'] at hlift₁
      exact hb c₁ hlift₁
    · rw [show t₁ = s₁ + ε / 2 from min_eq_right hb'] at ht₁s₁
      linarith
  have hend : ∀ s, 0 ≤ s → ∀ c, IsLift s c → c s ∈ W := by
    rintro s hs c ⟨hc, hc0, hcl⟩
    have hclosed : IsClosed ({ t | c t ∈ W } ∩ Icc 0 s) := by
      rw [inter_comm]
      exact hc.preimage_isClosed_of_isClosed isClosed_Icc hW.isClosed
    have hE : IsClosed (Icc 0 s ∩ (fun t => (c t, c' t)) ⁻¹' { p | p.1 = p.2 }) :=
      (hc.prodMk (hcont s hs)).preimage_isClosed_of_isClosed isClosed_Icc isClosed_diagonal
    refine hclosed.Icc_subset_of_forall_mem_nhdsWithin (by simpa [hc0] using hqW)
      (fun t ht => ?_) ⟨hs, le_rfl⟩
    by_contra hnot
    have hfreq : ∃ᶠ t' in 𝓝[>] t, t' ∈ Icc 0 s ∩ (fun t => (c t, c' t)) ⁻¹' { p | p.1 = p.2 } := by
      refine ((not_eventually.1 hnot).and_eventually (Ioo_mem_nhdsGT ht.2.2)).mono ?_
      rintro t' ⟨ht'W, ht'⟩
      have ht'I : t' ∈ Icc 0 s := ⟨ht.2.1.trans ht'.1.le, ht'.2.le⟩
      exact ⟨ht'I, by simpa using (hlift_W s c ⟨hc, hc0, hcl⟩ t' ht'I ht'W)⟩
    have := hE.mem_of_frequently_of_tendsto hfreq (tendsto_id.mono_left nhdsWithin_le_nhds)
    have heq : c t = c' t := this.2
    exact hc'W t ht.2.1 (heq ▸ ht.1)
  have hK : IsCompact (Ψ '' (W ∩ { z | ψ q ≤ ψ z })) :=
    (hW.inter_right (isClosed_le continuous_const hψc)).image_of_continuousOn
      (h.smooth.continuousOn.mono fun z hz => hsup z hz.2)
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.1 (hc'K.eventually hK.compl_mem_cocompact)
  set s := max t₀ 0
  obtain ⟨c, hc⟩ := hexists s (le_max_right _ _)
  have hs : s ∈ Icc 0 s := ⟨le_max_right _ _, le_rfl⟩
  refine ht₀ s (le_max_left _ _) ⟨c s, ⟨hend s (le_max_right _ _) c hc, hlift_ψ s c hc s hs⟩, ?_⟩
  exact (hc.2.2 s hs).2

end ExtensionProperty

end

end LorentzianCalderon
