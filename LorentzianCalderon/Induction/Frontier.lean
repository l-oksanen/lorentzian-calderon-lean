module

public import LorentzianCalderon.Induction.Propagation
public import LorentzianCalderon.Induction.NoEscape
public import LorentzianCalderon.Setting.SolutionCoords

public section

/-!
# Behaviour at the frontier

Blueprint, Lemma `lem_frontier`, for an immersion `v' = (v'ᵢ)` of a neighbourhood of `W` by
solutions of `□_{g'} v'ᵢ = 0` (`exists_solution_coords`) and its transfer `v = (𝒯 v'ᵢ)`.

* (a) `ExtensionProperty.frontier_tendsto`: the cluster set of `Ψ` at `q₀ ∈ Σ_τ ∩ W` (along
  `A_τ`) lies in the fibre `{p ∈ W | v'(p) = v(q₀)}` of the immersion. The neighbourhoods `B` of
  `q₀` with `B ∩ A_τ` connected are cylinders along a direction `e` with `dψ(q₀) e = 1`
  (`exists_nhds_isPreconnected_inter`), and a local left inverse of `v'`
  (`exists_leftInverse_of_injective_fderiv`) separates the cluster point `p₀` from the rest of
  the fibre.
* (b) `ExtensionProperty.frontier_eq`: the points of `O ∩ A_τ` approaching a frontier point
  `q₀` of `W` are taken on a segment `q₀ + s v`, `s > 0`, in an explicit Minkowski-timelike
  direction `v` leaving `W` (`exists_frontier_direction`).
* (c) `ExtensionProperty.frontier_extension`: `Ψ' = ϖ ∘ v` for a local left inverse `ϖ` of `v'`
  near `p₀`.
-/

namespace LorentzianCalderon

noncomputable section
open Set Filter Function Metric
open scoped ContDiff Matrix Topology

variable {n : ℕ}

/-! ### Neighbourhoods whose upper parts are connected -/

section Analysis

/-- A function whose derivative in the direction `e` is positive along a segment in direction `e`
increases along it. -/
lemma lt_of_forall_fderiv_apply_pos {ψ : E n → ℝ} (hψ : Differentiable ℝ ψ) {x e : E n}
    {a b : ℝ} (hab : a < b) (hpos : ∀ u ∈ Ioo a b, 0 < fderiv ℝ ψ (x + u • e) e) :
    ψ (x + a • e) < ψ (x + b • e) := by
  have hderiv : ∀ u, HasDerivAt (fun u : ℝ => ψ (x + u • e)) (fderiv ℝ ψ (x + u • e) e) u := by
    intro u
    have := (hψ (x + u • e)).hasFDerivAt.comp_hasDerivAt u
      (((hasDerivAt_id u).smul_const e).const_add x)
    simp only [id, one_smul] at this
    exact this
  obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope (fun u : ℝ => ψ (x + u • e))
    (fun u => fderiv ℝ ψ (x + u • e) e) hab
    (fun u _ => (hderiv u).continuousAt.continuousWithinAt) fun u _ => hderiv u
  have hpos' := hpos c hc
  rw [hc', lt_div_iff₀ (sub_pos.2 hab), zero_mul, sub_pos] at hpos'
  exact hpos'

/-- A function whose derivative in the direction `e` is positive on a convex set increases along
the lines in direction `e` within the set. -/
lemma lt_of_fderiv_apply_pos {ψ : E n → ℝ} (hψ : Differentiable ℝ ψ) {e : E n} {s : Set (E n)}
    (hs : Convex ℝ s) (hpos : ∀ y ∈ s, 0 < fderiv ℝ ψ y e) {x : E n} {a b : ℝ} (hab : a < b)
    (ha : x + a • e ∈ s) (hb : x + b • e ∈ s) : ψ (x + a • e) < ψ (x + b • e) := by
  have hs' : Convex ℝ ((fun u : ℝ => u • e) ⁻¹' ((fun y => x + y) ⁻¹' s)) :=
    (hs.translate_preimage_right x).is_linear_preimage (IsLinearMap.isLinearMap_smul' e)
  exact lt_of_forall_fderiv_apply_pos hψ hab fun u hu =>
    hpos _ (hs'.ordConnected.out ha hb (Ioo_subset_Icc_self hu))

/-- Near a point `q₀` where `dψ ≠ 0`, there are arbitrarily small neighbourhoods `B` of `q₀` with
`B ∩ {ψ > ψ q₀}` preconnected and nonempty. -/
theorem exists_nhds_isPreconnected_inter {ψ : E n → ℝ} (hψ : ContDiff ℝ 1 ψ) {q₀ : E n}
    (hq₀ : fderiv ℝ ψ q₀ ≠ 0) {N : Set (E n)} (hN : N ∈ 𝓝 q₀) :
    ∃ B ∈ 𝓝 q₀, B ⊆ N ∧ IsPreconnected (B ∩ {x | ψ q₀ < ψ x}) ∧
      (B ∩ {x | ψ q₀ < ψ x}).Nonempty := by
  set ℓ := fderiv ℝ ψ q₀
  obtain ⟨w, hw⟩ : ∃ w, ℓ w ≠ 0 := by
    by_contra! h
    exact hq₀ (ContinuousLinearMap.ext h)
  set e := (ℓ w)⁻¹ • w
  have he : ℓ e = 1 := by simp [e, hw]
  have hψd : Differentiable ℝ ψ := hψ.differentiable one_ne_zero
  have hcont : Continuous fun y => fderiv ℝ ψ y e :=
    (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  obtain ⟨R, hR, hRpos, hRN⟩ : ∃ R > 0, (∀ y ∈ ball q₀ R, 0 < fderiv ℝ ψ y e) ∧
      ball q₀ R ⊆ N := by
    have h1 : ∀ᶠ y in 𝓝 q₀, 0 < fderiv ℝ ψ y e :=
      hcont.continuousAt.eventually (lt_mem_nhds (show (0 : ℝ) < ℓ e from he ▸ one_pos))
    obtain ⟨R, hR, hRs⟩ := Metric.mem_nhds_iff.1 (h1.and hN)
    exact ⟨R, hR, fun y hy => (hRs hy).1, fun y hy => (hRs hy).2⟩
  have hmono : ∀ (x : E n) (a b : ℝ), a < b → x + a • e ∈ ball q₀ R → x + b • e ∈ ball q₀ R →
      ψ (x + a • e) < ψ (x + b • e) := fun x a b hab ha hb =>
    lt_of_fderiv_apply_pos hψd (convex_ball q₀ R) hRpos hab ha hb
  set r := R / (2 * (‖e‖ + 1))
  have hr : 0 < r := by positivity
  have hre : r * ‖e‖ < R / 2 := by
    rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [norm_nonneg e]
  set c := r / 2
  have hc0 : 0 < c := by positivity
  have hce : c * ‖e‖ < R / 2 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right (half_le_self hr.le) (norm_nonneg e)) hre
  have hcball : ∀ v : E n, ‖v‖ < R / 2 → q₀ + v + c • e ∈ ball q₀ R := fun v hv => by
    rw [mem_ball, dist_eq_norm, add_assoc, add_sub_cancel_left]
    calc ‖v + c • e‖ ≤ ‖v‖ + ‖c • e‖ := norm_add_le _ _
      _ = ‖v‖ + c * ‖e‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc0]
      _ < R := by linarith
  have hc : ψ q₀ < ψ (q₀ + c • e) := by
    have := hmono q₀ 0 c hc0 (by simpa using mem_ball_self (x := q₀) hR)
      (by simpa using hcball 0 (by rw [norm_zero]; linarith))
    simpa using this
  obtain ⟨δ₀, hδ₀, hδ₀'⟩ : ∃ δ₀ > 0, ∀ v : E n, ‖v‖ < δ₀ → ψ q₀ < ψ (q₀ + v + c • e) := by
    have hc' : Continuous fun v : E n => ψ (q₀ + v + c • e) :=
      hψd.continuous.comp (by fun_prop)
    have := hc'.continuousAt (x := 0) |>.eventually (lt_mem_nhds (by simpa using hc))
    obtain ⟨δ₀, hδ₀, h⟩ := Metric.eventually_nhds_iff.1 this
    exact ⟨δ₀, hδ₀, fun v hv => h (by simpa using hv)⟩
  set δ := min δ₀ (R / 2)
  have hδ : 0 < δ := lt_min hδ₀ (by positivity)
  set P : E n →L[ℝ] E n := ContinuousLinearMap.id ℝ (E n) - ℓ.smulRight e
  have hP : ∀ v, P v = v - ℓ v • e := fun v => rfl
  have hPe : ∀ v (u : ℝ), P (v + u • e) = P v := fun v u => by
    simp only [hP, map_add, map_smul, he, smul_eq_mul, mul_one, add_smul]
    abel
  have hℓe : ∀ v (u : ℝ), ℓ (v + u • e) = ℓ v + u := fun v u => by
    simp [he]
  have hdecomp : ∀ v, v = P v + ℓ v • e := fun v => by rw [hP, sub_add_cancel]
  set C := ℓ ⁻¹' ball 0 r ∩ P ⁻¹' ball 0 δ
  set H := {v : E n | c ≤ ℓ v}
  set B := (fun x => x + -q₀) ⁻¹' C
  have hmemB : ∀ x, x ∈ B ↔ |ℓ (x - q₀)| < r ∧ ‖P (x - q₀)‖ < δ := fun x => by
    simp [B, C, ← sub_eq_add_neg]
  have hBo : IsOpen B :=
    ((isOpen_ball.preimage ℓ.continuous).inter (isOpen_ball.preimage P.continuous)).preimage
      (by fun_prop)
  have hq₀B : q₀ ∈ B := by
    rw [hmemB]
    simp [hr, hδ]
  have hBball : B ⊆ ball q₀ R := by
    intro x hx
    rw [hmemB] at hx
    rw [mem_ball, dist_eq_norm]
    calc ‖x - q₀‖ = ‖P (x - q₀) + ℓ (x - q₀) • e‖ := by rw [← hdecomp]
      _ ≤ ‖P (x - q₀)‖ + ‖ℓ (x - q₀) • e‖ := norm_add_le _ _
      _ = ‖P (x - q₀)‖ + |ℓ (x - q₀)| * ‖e‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ < R / 2 + R / 2 := by
          refine add_lt_add_of_lt_of_le (lt_of_lt_of_le hx.2 (min_le_right _ _)) ?_
          exact le_trans (mul_le_mul_of_nonneg_right hx.1.le (norm_nonneg e)) hre.le
      _ = R := by ring
  have hCconv : Convex ℝ C :=
    ((convex_ball 0 r).linear_preimage ℓ.toLinearMap).inter
      ((convex_ball 0 δ).linear_preimage P.toLinearMap)
  set Up := (fun x => x + -q₀) ⁻¹' (C ∩ H)
  have hUpconv : Convex ℝ Up :=
    (hCconv.inter (convex_halfSpace_ge ℓ.toLinearMap.isLinear c)).translate_preimage_left (-q₀)
  have hmemUp : ∀ x, x ∈ Up ↔ x ∈ B ∧ c ≤ ℓ (x - q₀) := fun x => by
    simp [Up, B, H, ← sub_eq_add_neg]
  have hUpA : Up ⊆ {x | ψ q₀ < ψ x} := by
    intro x hx
    rw [hmemUp] at hx
    obtain ⟨hxB, hxc⟩ := hx
    have hxB' := (hmemB x).1 hxB
    set v := P (x - q₀)
    set s := ℓ (x - q₀)
    have hx : x = (q₀ + v) + s • e := by
      rw [add_assoc, ← hdecomp, add_sub_cancel]
    have h1 : ψ q₀ < ψ (q₀ + v + c • e) := hδ₀' v (lt_of_lt_of_le hxB'.2 (min_le_left _ _))
    rcases hxc.eq_or_lt with h | h
    · show ψ q₀ < ψ x
      rw [hx, ← h]
      exact h1
    · show ψ q₀ < ψ x
      rw [hx]
      exact h1.trans (hmono (q₀ + v) c s h
        (hcball v (lt_of_lt_of_le hxB'.2 (min_le_right _ _))) (hx ▸ hBball hxB))
  have hxs : q₀ + c • e ∈ Up := by
    rw [hmemUp, hmemB]
    simp only [add_sub_cancel_left, map_smul, he, smul_eq_mul, mul_one]
    refine ⟨⟨?_, ?_⟩, le_rfl⟩
    · rw [abs_of_pos hc0]
      exact half_lt_self hr
    · have hPe0 : P e = 0 := by simpa using hPe 0 1
      rw [hPe0, smul_zero, norm_zero]
      exact hδ
  refine ⟨B, hBo.mem_nhds hq₀B, hBball.trans hRN, ?_, ⟨q₀ + c • e, ((hmemUp _).1 hxs).1, hUpA hxs⟩⟩
  refine isPreconnected_of_forall (q₀ + c • e) fun y hy => ?_
  obtain ⟨hyB, hyA⟩ := hy
  have hyB' := (hmemB y).1 hyB
  set t := max 0 (c - ℓ (y - q₀))
  have ht : 0 ≤ t := le_max_left _ _
  set seg := (fun u : ℝ => y + u • e) '' Icc 0 t
  have hsegB : ∀ u ∈ Icc 0 t, y + u • e ∈ B := by
    intro u hu
    rw [hmemB, add_sub_right_comm, hℓe, hPe]
    refine ⟨abs_lt.2 ⟨by linarith [(abs_lt.1 hyB'.1).1, hu.1], ?_⟩, hyB'.2⟩
    have hu2 : ℓ (y - q₀) + u ≤ max (ℓ (y - q₀)) c := by
      rcases le_total c (ℓ (y - q₀)) with h | h
      · have : t = 0 := max_eq_left (by linarith)
        rw [this] at hu
        linarith [hu.2, le_max_left (ℓ (y - q₀)) c]
      · have : t = c - ℓ (y - q₀) := max_eq_right (by linarith)
        rw [this] at hu
        linarith [hu.2, le_max_right (ℓ (y - q₀)) c]
    exact lt_of_le_of_lt hu2 (max_lt (abs_lt.1 hyB'.1).2 (half_lt_self hr))
  have hseg : seg ⊆ B ∩ {x | ψ q₀ < ψ x} := by
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨hsegB u hu, ?_⟩
    rcases hu.1.eq_or_lt with h | h
    · simpa [← h] using hyA
    · have := hmono y 0 u h (by simpa using hBball hyB) (hBball (hsegB u hu))
      simp only [zero_smul, add_zero] at this
      exact lt_trans hyA this
  have hyt : y + t • e ∈ Up := by
    rw [hmemUp]
    refine ⟨hsegB t ⟨ht, le_rfl⟩, ?_⟩
    rw [add_sub_right_comm, hℓe]
    linarith [le_max_right 0 (c - ℓ (y - q₀))]
  refine ⟨seg ∪ Up, union_subset hseg (subset_inter (fun x hx => ((hmemUp x).1 hx).1) hUpA),
    Or.inr hxs, Or.inl ⟨0, ⟨le_rfl, ht⟩, by simp⟩, ?_⟩
  exact (isPreconnected_Icc.image _ (by fun_prop)).union (y + t • e) ⟨t, ⟨ht, le_rfl⟩, rfl⟩ hyt
    hUpconv.isPreconnected

/-- A point of a level set `{ψ = τ}` with `dψ ≠ 0` lies in the closure of `{ψ > τ}`. -/
lemma mem_closure_A {ψ : E n → ℝ} (hψ : ContDiff ℝ 1 ψ) {x : E n} (hx : fderiv ℝ ψ x ≠ 0)
    {τ : ℝ} (hxτ : ψ x = τ) : x ∈ closure (A ψ τ) := by
  rw [mem_closure_iff_nhds]
  intro N hN
  obtain ⟨B, -, hBN, -, y, hyB, hy⟩ := exists_nhds_isPreconnected_inter hψ hx hN
  exact ⟨y, hBN hyB, by rw [mem_A, ← hxτ]; exact hy⟩

/-- A smooth map with injective differential at `p` has a smooth left inverse near `p`. -/
theorem exists_leftInverse_of_injective_fderiv {m : ℕ} {V : E n → (Fin m → ℝ)}
    (hV : ContDiff ℝ ∞ V) {p : E n} (hp : Injective (fderiv ℝ V p)) :
    ∃ (U : Set (E n)) (𝒩 : Set (Fin m → ℝ)) (ϖ : (Fin m → ℝ) → E n), IsOpen U ∧ p ∈ U ∧
      IsOpen 𝒩 ∧ MapsTo V U 𝒩 ∧ ContDiffOn ℝ ∞ ϖ 𝒩 ∧ ∀ x ∈ U, ϖ (V x) = x := by
  obtain ⟨π₀, hπ₀⟩ := (fderiv ℝ V p : E n →ₗ[ℝ] (Fin m → ℝ)).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 hp)
  set π : (Fin m → ℝ) →L[ℝ] E n := LinearMap.toContinuousLinearMap π₀
  set f : E n → E n := fun x => π (V x)
  have hf : ContDiff ℝ ∞ f := π.contDiff.comp hV
  have hfd : ∀ x, fderiv ℝ f x = π.comp (fderiv ℝ V x) := fun x =>
    (π.hasFDerivAt.comp x ((hV.differentiable (by simp)) x).hasFDerivAt).fderiv
  have hfp : fderiv ℝ f p = ContinuousLinearMap.id ℝ (E n) := by
    ext1 v
    rw [hfd]
    exact LinearMap.congr_fun hπ₀ v
  set U₀ := (fun x => fderiv ℝ f x) ⁻¹' range ((↑) : (E n ≃L[ℝ] E n) → E n →L[ℝ] E n)
  have hU₀ : IsOpen U₀ :=
    ContinuousLinearEquiv.isOpen.preimage (hf.continuous_fderiv (by simp))
  have hpU₀ : p ∈ U₀ := ⟨ContinuousLinearEquiv.refl ℝ (E n), by simp only [hfp]; rfl⟩
  have hinj : ∀ z ∈ U₀, Injective (fderiv ℝ f z) := by
    rintro z ⟨L, hL⟩
    simp only at hL
    rw [← hL]
    exact L.injective
  obtain ⟨φ, hφ, hpφ, -, hsmooth, -⟩ := exists_localInverse hU₀ hf.contDiffOn hinj hpU₀
  have hφx : ∀ x, φ x = π (V x) := fun x => by rw [hφ]
  refine ⟨φ.source, π ⁻¹' φ.target, fun y => φ.symm (π y), φ.open_source, hpφ,
    φ.open_target.preimage π.continuous, fun x hx => ?_, ?_, fun x hx => ?_⟩
  · have := φ.map_source hx
    rwa [hφx] at this
  · exact hsmooth.comp π.contDiff.contDiffOn (mapsTo_preimage _ _)
  · simp only
    rw [← hφx, φ.left_inv hx]

/-- A cluster point of `u` along `l` lies in every closed set in which `u` eventually lies. -/
lemma MapClusterPt.mem_of_isClosed {α X : Type*} [TopologicalSpace X] {l : Filter α}
    {u : α → X} {x : X} {F : Set X} (hx : MapClusterPt x l u) (hF : IsClosed F)
    (hev : ∀ᶠ a in l, u a ∈ F) : x ∈ F := by
  by_contra h
  obtain ⟨a, ha1, ha2⟩ := ((hx.frequently (hF.isOpen_compl.mem_nhds h)).and_eventually hev).exists
  exact ha1 ha2

end Analysis

/-! ### Directions leaving `W` at its frontier -/

/-- At a frontier point `q₀` of `W`, a Minkowski-timelike direction `v` with `v⁰ = 1` leads into
`O`. -/
theorem exists_frontier_direction {T : ℝ} (hn : 0 < n) {q₀ : E n} (hq : q₀ ∈ frontier (W n T)) :
    ∃ v : E n, v 0 = 1 ∧ form (minkowski n) v v < 0 ∧ ∀ s : ℝ, 0 < s → q₀ + s • v ∈ O n T := by
  have hint : q₀ ∉ interior (W n T) := hq.2
  set S := {x : E n | ‖spatial x‖ < √n ∧ -T - 2 * (√n - ‖spatial x‖) < x 0 ∧ x 0 < T}
  have h0 : Continuous fun x : E n => x 0 := by fun_prop
  have hs : Continuous fun x : E n => ‖spatial x‖ := spatial.continuous.norm
  have hSo : IsOpen S :=
    (isOpen_lt hs continuous_const).inter ((isOpen_lt (by fun_prop) h0).inter
      (isOpen_lt h0 continuous_const))
  have hSW : S ⊆ W n T := fun x hx => mem_W.2 ⟨hx.1.le, hx.2.1.le, hx.2.2.le⟩
  have hq₀S : q₀ ∉ S := fun h => hint (interior_maximal hSW hSo h)
  obtain ⟨e, he, hxe⟩ := exists_unit_smul_eq hn (spatial q₀)
  refine ⟨spacetimePoint 1 ((3 / 4 : ℝ) • e), spacetimePoint_zero _ _, ?_,
    fun s hs => mem_O.2 fun hW => ?_⟩
  · rw [form_minkowski_self]
    simp [norm_smul, he]
    norm_num
  · have hsp : spatial (q₀ + s • spacetimePoint 1 ((3 / 4 : ℝ) • e)) =
        (‖spatial q₀‖ + 3 * s / 4) • e := by
      rw [map_add, map_smul, spatial_spacetimePoint, smul_smul, add_smul, ← hxe]
      ring_nf
    have hnorm : ‖spatial (q₀ + s • spacetimePoint 1 ((3 / 4 : ℝ) • e))‖ =
        ‖spatial q₀‖ + 3 * s / 4 := by
      rw [hsp, norm_smul, he, mul_one, Real.norm_of_nonneg (by positivity)]
    obtain ⟨h1, h2, h3⟩ := mem_W.1 hW
    rw [hnorm] at h1 h2
    simp only [PiLp.add_apply, PiLp.smul_apply, spacetimePoint_zero, smul_eq_mul,
      mul_one] at h2 h3
    exact hq₀S ⟨by linarith, by linarith, by linarith⟩

/-! ### The frontier -/

namespace ExtensionProperty

variable {T : ℝ} {g g' : MatrixField n} {Y Y' : E n → E n} {ψ : E n → ℝ} {τ : ℝ}
  {Ψ : E n → E n} {Φ : ℝ → E n → E n}

/-- **No escape** (`lem_no_escape`) in the setting of the induction: `Ψ (A_τ ∩ W) ⊆ W`. -/
theorem mapsTo_W_of_admissible (hP : ExtensionProperty g g' ψ (W n T) τ Ψ)
    (hgA : IsAdmissibleMetric n T g) (hg'A : IsAdmissibleMetric n T g')
    (hg : IsSpacetime g Y) (hg' : IsSpacetime g' Y')
    (hY : ∀ x ∉ M0 n T, form (g x) (EuclideanSpace.single 0 1) (Y x) < 0)
    (hY' : ∀ x ∉ M0 n T, form (g' x) (EuclideanSpace.single 0 1) (Y' x) < 0)
    (hψ : IsCauchyTemporal g Y ψ) (hΦ : Continuous fun p : ℝ × E n => Φ p.1 p.2)
    (hΦ0 : ∀ x, Φ 0 x = x) (hΦψ : ∀ t x, ψ (Φ t x) = ψ x + t) :
    MapsTo Ψ (A ψ τ ∩ W n T) (W n T) := by
  have hψc := hψ.smooth.continuous
  refine hP.mapsTo_W hg hg' hψ isCompact_W (isConnected_A hψc hΦ hΦ0 hΦψ τ).isPreconnected
    (nonempty_A_diff hψc hΦψ isCompact_W τ) (fun x hx v hv => ?_) fun x hx => ?_
  · have hxM : x ∉ M0 n T := fun h => hx (M0_subset_W h)
    exact (isFutureTimelike_iff_of_minkowski (hg'A.minkowski_exterior x hxM)
      (hg'.globallyHyperbolic.timeOrientation.timelike x) (hY' x hxM)).2
      ((isFutureTimelike_iff_of_minkowski (hgA.minkowski_exterior x hxM)
        (hg.globallyHyperbolic.timeOrientation.timelike x) (hY x hxM)).1 hv)
  · simpa only [mem_O] using exists_isInextendibleRay_subset_O (by have := hg.two_le; omega)
      hg'.globallyHyperbolic.timeOrientation hg'A.minkowski_exterior hY' (mem_O.2 hx)

/-- **Behaviour at the frontier** (blueprint, `lem_frontier`(a)): for `q₀ ∈ Σ_τ ∩ W`, `Ψ(q)`
converges to some `p₀ ∈ W` as `q → q₀` in `A_τ`, and `v'(p₀) = v(q₀)` for the immersion
`v' = (v'ᵢ)` and its transfer `v = (𝒯 v'ᵢ)`. -/
theorem frontier_tendsto (hP : ExtensionProperty g g' ψ (W n T) τ Ψ)
    (hgA : IsAdmissibleMetric n T g) (hg'A : IsAdmissibleMetric n T g')
    (hg : IsSpacetime g Y) (hg' : IsSpacetime g' Y')
    (hY : ∀ x ∉ M0 n T, form (g x) (EuclideanSpace.single 0 1) (Y x) < 0)
    (hY' : ∀ x ∉ M0 n T, form (g' x) (EuclideanSpace.single 0 1) (Y' x) < 0)
    (hC : CauchyDataSubset n T g g') (hψ : IsCauchyTemporal g Y ψ)
    (hΦ : Continuous fun p : ℝ × E n => Φ p.1 p.2) (hΦ0 : ∀ x, Φ 0 x = x)
    (hΦψ : ∀ t x, ψ (Φ t x) = ψ x + t) {m : ℕ} {v' : Fin m → E n → ℝ}
    (hv' : ∀ i, ContDiff ℝ ∞ (v' i)) (hbox' : ∀ i x, box g' (v' i) x = 0)
    (himm : ∀ x ∈ W n T, Injective (fderiv ℝ (fun y i => v' i y) x)) {q₀ : E n}
    (hq₀ : ψ q₀ = τ) (hq₀W : q₀ ∈ W n T) :
    ∃ p₀ ∈ W n T, Tendsto Ψ (𝓝[A ψ τ] q₀) (𝓝 p₀) ∧
      ∀ i, v' i p₀ = transfer n T g (v' i) q₀ := by
  set V' : E n → Fin m → ℝ := fun y i => v' i y
  set V : E n → Fin m → ℝ := fun y i => transfer n T g (v' i) y
  have hV'c : Continuous V' := continuous_pi fun i => (hv' i).continuous
  have hVc : Continuous V := continuous_pi fun i =>
    (transfer_spec hgA hg'A hg hg' hY hY' hC (hv' i) (hbox' i)).1.continuous
  have hVV : ∀ q ∈ A ψ τ, V q = V' (Ψ q) := fun q hq => funext fun i =>
    hP.transfer_eq_comp hgA hg'A hg hg' hY hY' hC hψ (hv' i) (hbox' i) q hq
  have hΨc : ContinuousOn Ψ (A ψ τ) := hP.smooth.continuousOn
  have hmaps := hP.mapsTo_W_of_admissible hgA hg'A hg hg' hY hY' hψ hΦ hΦ0 hΦψ
  have hdψ : fderiv ℝ ψ q₀ ≠ 0 := fun h =>
    fderiv_apply_unitNormal_ne_zero hg hψ q₀ (by rw [h]; rfl)
  have hψ1 : ContDiff ℝ 1 ψ := hψ.smooth.of_le (by simp)
  have hbasis : ∀ N ∈ 𝓝 q₀, ∃ B ∈ 𝓝 q₀, B ⊆ N ∧ IsPreconnected (B ∩ A ψ τ) ∧
      (B ∩ A ψ τ).Nonempty := by
    intro N hN
    obtain ⟨B, hB, hBN, h1, h2⟩ := exists_nhds_isPreconnected_inter hψ1 hdψ hN
    rw [hq₀] at h1 h2
    exact ⟨B, hB, hBN, (by simpa only [A_def] using h1), (by simpa only [A_def] using h2)⟩
  have hne : (𝓝[A ψ τ] q₀).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1 (mem_closure_A hψ1 hdψ hq₀)
  have hev : ∀ N ∈ 𝓝 q₀, ∀ᶠ q in 𝓝[A ψ τ] q₀, Ψ q ∈ W n T ∪ N := by
    intro N hN
    filter_upwards [nhdsWithin_le_nhds hN, self_mem_nhdsWithin] with q hqN hqA
    by_cases hqW : q ∈ W n T
    · exact Or.inl (hmaps ⟨hqA, hqW⟩)
    · rw [hP.eq_self q hqA hqW]
      exact Or.inr hqN
  set K := W n T ∪ closedBall q₀ 1
  have hK : IsCompact K := isCompact_W.union (isCompact_closedBall _ _)
  have hevK : ∀ᶠ q in 𝓝[A ψ τ] q₀, Ψ q ∈ K := hev _ (closedBall_mem_nhds q₀ one_pos)
  have hcl : ∀ x, MapClusterPt x (𝓝[A ψ τ] q₀) Ψ → x ∈ W n T ∧ V' x = V q₀ := by
    intro x hx
    constructor
    · by_contra hxW
      have hxq : x ≠ q₀ := fun h => hxW (h ▸ hq₀W)
      obtain ⟨u₁, u₂, hu₁, hu₂, hxu₁, hqu₂, hdisj⟩ := t2_separation hxq
      have h1 := hx.frequently (inter_mem (hu₁.mem_nhds hxu₁)
        (isClosed_W.isOpen_compl.mem_nhds hxW))
      obtain ⟨q, ⟨hq1, hq1'⟩, hq2⟩ := (h1.and_eventually (hev u₂ (hu₂.mem_nhds hqu₂))).exists
      rcases hq2 with h | h
      · exact hq1' h
      · exact disjoint_left.1 hdisj hq1 h
    · by_contra hne'
      obtain ⟨u₁, u₂, hu₁, hu₂, hxu₁, hqu₂, hdisj⟩ := t2_separation hne'
      have h1 := hx.frequently (hV'c.continuousAt.preimage_mem_nhds (hu₁.mem_nhds hxu₁))
      have h2 : ∀ᶠ q in 𝓝[A ψ τ] q₀, V q ∈ u₂ :=
        (hVc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) (hu₂.mem_nhds hqu₂)
      obtain ⟨q, hq1, hq2, hqA⟩ := (h1.and_eventually (h2.and self_mem_nhdsWithin)).exists
      rw [hVV q hqA] at hq2
      exact disjoint_left.1 hdisj hq1 hq2
  obtain ⟨p₀, -, hp₀⟩ := hK.exists_mapClusterPt (f := 𝓝[A ψ τ] q₀) (u := Ψ)
    (le_principal_iff.2 hevK)
  obtain ⟨hp₀W, hp₀V⟩ := hcl p₀ hp₀
  obtain ⟨U, -, ϖ, hUo, hp₀U, -, -, -, hϖ⟩ :=
    exists_leftInverse_of_injective_fderiv (contDiff_pi.2 hv') (himm p₀ hp₀W)
  have hinjU : InjOn V' U := fun x hx y hy hxy =>
    (hϖ x hx).symm.trans ((congrArg ϖ hxy).trans (hϖ y hy))
  obtain ⟨O, hOo, hp₀O, hOU, -⟩ := exists_open_between_and_isCompact_closure
    (isCompact_singleton (x := p₀)) hUo (singleton_subset_iff.2 hp₀U)
  have hp₀O' : p₀ ∈ O := singleton_subset_iff.1 hp₀O
  have hclp : ∀ x, MapClusterPt x (𝓝[A ψ τ] q₀) Ψ → x ∈ closure O → x = p₀ :=
    fun x hx hxO => hinjU (hOU hxO) hp₀U (by rw [(hcl x hx).2, hp₀V])
  have hFc : IsClosed (O ∪ (closure O)ᶜ)ᶜ :=
    (hOo.union isClosed_closure.isOpen_compl).isClosed_compl
  have hev2 : ∀ᶠ q in 𝓝[A ψ τ] q₀, Ψ q ∈ O ∪ (closure O)ᶜ := by
    by_contra hcon
    rw [not_eventually] at hcon
    have hne2 := frequently_iff_neBot.1 hcon
    obtain ⟨x, -, hx⟩ := hK.exists_mapClusterPt
      (f := 𝓝[A ψ τ] q₀ ⊓ 𝓟 {q | ¬ Ψ q ∈ O ∪ (closure O)ᶜ}) (u := Ψ)
      (le_principal_iff.2 (mem_inf_of_left hevK))
    have hxF := MapClusterPt.mem_of_isClosed hx hFc (mem_inf_of_right (mem_principal_self _))
    simp only [mem_compl_iff, mem_union, not_or, not_not] at hxF
    exact hxF.1 (hclp x (hx.mono inf_le_left) hxF.2 ▸ hp₀O')
  have hevO : ∀ᶠ q in 𝓝[A ψ τ] q₀, Ψ q ∈ O := by
    obtain ⟨N, hN, hNsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hev2
    obtain ⟨B, hB, hBN, hBc, -⟩ := hbasis N hN
    have hsub : Ψ '' (B ∩ A ψ τ) ⊆ O ∪ (closure O)ᶜ := by
      rintro _ ⟨q, hq, rfl⟩
      exact hNsub ⟨hBN hq.1, hq.2⟩
    have hmeet : (Ψ '' (B ∩ A ψ τ) ∩ O).Nonempty := by
      obtain ⟨q, hqO, hqB, hqA⟩ := ((hp₀.frequently (hOo.mem_nhds hp₀O')).and_eventually
        ((show ∀ᶠ q in 𝓝[A ψ τ] q₀, q ∈ B from nhdsWithin_le_nhds hB).and
          self_mem_nhdsWithin)).exists
      exact ⟨Ψ q, ⟨q, ⟨hqB, hqA⟩, rfl⟩, hqO⟩
    have hdisj : Disjoint O (closure O)ᶜ := disjoint_compl_right.mono_left subset_closure
    have hsubO := (hBc.image Ψ (hΨc.mono inter_subset_right)).subset_left_of_subset_union hOo
      isClosed_closure.isOpen_compl hdisj hsub hmeet
    filter_upwards [nhdsWithin_le_nhds hB, self_mem_nhdsWithin] with q hqB hqA
    exact hsubO ⟨q, ⟨hqB, hqA⟩, rfl⟩
  refine ⟨p₀, hp₀W, hK.tendsto_nhds_of_unique_mapClusterPt hevK fun x _ hx => ?_,
    fun i => congrFun hp₀V i⟩
  exact hclp x hx (MapClusterPt.mem_of_isClosed hx isClosed_closure
    (hevO.mono fun q hq => subset_closure hq))

/-- **Behaviour at the frontier** (blueprint, `lem_frontier`(b)): at a frontier point `q₀` of
`W` on `Σ_τ`, the limit of `Ψ` is `q₀`. -/
theorem frontier_eq (hP : ExtensionProperty g g' ψ (W n T) τ Ψ)
    (hgA : IsAdmissibleMetric n T g) (hg : IsSpacetime g Y)
    (hY : ∀ x ∉ M0 n T, form (g x) (EuclideanSpace.single 0 1) (Y x) < 0)
    (hψ : IsCauchyTemporal g Y ψ) {q₀ p₀ : E n} (hq₀ : ψ q₀ = τ)
    (hfr : q₀ ∈ frontier (W n T)) (hlim : Tendsto Ψ (𝓝[A ψ τ] q₀) (𝓝 p₀)) : p₀ = q₀ := by
  obtain ⟨v, hv0, hvη, hvO⟩ := exists_frontier_direction (by have := hg.two_le; omega) hfr
  set c : ℝ → E n := fun s => q₀ + s • v
  have hψd : Differentiable ℝ ψ := hψ.smooth.differentiable (by simp)
  have hcA : ∀ s : ℝ, 0 < s → c s ∈ A ψ τ := by
    intro s hs
    have := lt_of_forall_fderiv_apply_pos hψd (x := q₀) (e := v) hs fun u hu => by
      have hxM : q₀ + u • v ∉ M0 n T := fun h => mem_O.1 (hvO u hu.1) (M0_subset_W h)
      have hfut : IsFutureTimelike g Y (q₀ + u • v) v :=
        (isFutureTimelike_iff_of_minkowski (hgA.minkowski_exterior _ hxM)
          (hg.globallyHyperbolic.timeOrientation.timelike _) (hY _ hxM)).2
          ⟨hvη, by rw [hv0]; exact one_pos⟩
      exact hψ.fderiv_pos hg hfut.isFutureCausal
    simpa [c, hq₀] using this
  have hc0 : Tendsto c (𝓝[>] 0) (𝓝 q₀) := by
    have : Continuous c := by fun_prop
    exact (this.tendsto' 0 q₀ (by simp [c])).mono_left nhdsWithin_le_nhds
  have hc : Tendsto c (𝓝[>] 0) (𝓝[A ψ τ] q₀) :=
    tendsto_nhdsWithin_iff.2 ⟨hc0, eventually_nhdsWithin_of_forall fun s hs => hcA s hs⟩
  refine tendsto_nhds_unique (hlim.comp hc) (hc0.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
  exact (hP.eq_self _ (hcA s hs) (mem_O.1 (hvO s hs))).symm

/-- **Behaviour at the frontier** (blueprint, `lem_frontier`(c)): near `q₀ ∈ Σ_τ ∩ W`, `Ψ`
extends to a smooth map `Ψ̂ = ϖ ∘ v` (with a local left inverse `ϖ` of the immersion `v'` near
`p₀`) which pulls `g'` back to `g` on `{ψ ≥ τ}`, and `dΨ̂(q₀)` is invertible. -/
theorem frontier_extension (hP : ExtensionProperty g g' ψ (W n T) τ Ψ)
    (hgA : IsAdmissibleMetric n T g) (hg'A : IsAdmissibleMetric n T g')
    (hg : IsSpacetime g Y) (hg' : IsSpacetime g' Y')
    (hY : ∀ x ∉ M0 n T, form (g x) (EuclideanSpace.single 0 1) (Y x) < 0)
    (hY' : ∀ x ∉ M0 n T, form (g' x) (EuclideanSpace.single 0 1) (Y' x) < 0)
    (hC : CauchyDataSubset n T g g') (hψ : IsCauchyTemporal g Y ψ) {m : ℕ}
    {v' : Fin m → E n → ℝ} (hv' : ∀ i, ContDiff ℝ ∞ (v' i))
    (hbox' : ∀ i x, box g' (v' i) x = 0)
    (himm : ∀ x ∈ W n T, Injective (fderiv ℝ (fun y i => v' i y) x)) {q₀ p₀ : E n}
    (hq₀ : ψ q₀ = τ) (hp₀W : p₀ ∈ W n T) (hlim : Tendsto Ψ (𝓝[A ψ τ] q₀) (𝓝 p₀))
    (hp₀V : ∀ i, v' i p₀ = transfer n T g (v' i) q₀) :
    ∃ B : Set (E n), IsOpen B ∧ q₀ ∈ B ∧ ∃ Ψ' : E n → E n, ContDiffOn ℝ ∞ Ψ' B ∧
      Ψ' q₀ = p₀ ∧ (∀ q ∈ B ∩ A ψ τ, Ψ' q = Ψ q) ∧
      (∀ x ∈ B, τ ≤ ψ x → g x = (D Ψ' x)ᵀ * g' (Ψ' x) * D Ψ' x) ∧ (D Ψ' q₀).det ≠ 0 := by
  set V' : E n → Fin m → ℝ := fun y i => v' i y
  set V : E n → Fin m → ℝ := fun y i => transfer n T g (v' i) y
  have hVs : ContDiff ℝ ∞ V := contDiff_pi.2 fun i =>
    (transfer_spec hgA hg'A hg hg' hY hY' hC (hv' i) (hbox' i)).1
  have hVV : ∀ q ∈ A ψ τ, V q = V' (Ψ q) := fun q hq => funext fun i =>
    hP.transfer_eq_comp hgA hg'A hg hg' hY hY' hC hψ (hv' i) (hbox' i) q hq
  obtain ⟨U, 𝒩, ϖ, hUo, hp₀U, h𝒩o, hmapsU, hϖs, hϖ⟩ :=
    exists_leftInverse_of_injective_fderiv (contDiff_pi.2 hv') (himm p₀ hp₀W)
  have hVq₀ : V q₀ = V' p₀ := funext fun i => (hp₀V i).symm
  obtain ⟨u, huo, hq₀u, huA⟩ := mem_nhdsWithin.1 (hlim (hUo.mem_nhds hp₀U))
  set B := u ∩ V ⁻¹' 𝒩
  have hBo : IsOpen B := huo.inter (h𝒩o.preimage hVs.continuous)
  have hq₀B : q₀ ∈ B := ⟨hq₀u, by rw [mem_preimage, hVq₀]; exact hmapsU hp₀U⟩
  set Ψ' : E n → E n := fun x => ϖ (V x)
  have hΨ' : ContDiffOn ℝ ∞ Ψ' B := hϖs.comp hVs.contDiffOn fun x hx => hx.2
  have hagree : ∀ q ∈ B ∩ A ψ τ, Ψ' q = Ψ q := fun q hq => by
    simp only [Ψ']
    rw [hVV q hq.2]
    exact hϖ _ (huA ⟨hq.1.1, hq.2⟩)
  have hΨ'q₀ : Ψ' q₀ = p₀ := by
    simp only [Ψ']
    rw [hVq₀]
    exact hϖ p₀ hp₀U
  have hBA : IsOpen (B ∩ A ψ τ) := hBo.inter (isOpen_A hψ.smooth.continuous τ)
  have hpullA : ∀ x ∈ B ∩ A ψ τ, g x = (D Ψ' x)ᵀ * g' (Ψ' x) * D Ψ' x := by
    intro x hx
    have heq : Ψ' =ᶠ[𝓝 x] Ψ := eventually_of_mem (hBA.mem_nhds hx) hagree
    have hD : D Ψ' x = D Ψ x := by ext i j; simp only [D_def, heq.fderiv_eq]
    rw [hD, hagree x hx]
    exact hP.pullback x hx.2
  set t := B ∩ {x | τ ≤ ψ x}
  have hts : t ⊆ closure (B ∩ A ψ τ) := by
    rintro x ⟨hxB, hxτ⟩
    rcases (show τ ≤ ψ x from hxτ).lt_or_eq with h | h
    · exact subset_closure ⟨hxB, (mem_A.2 h)⟩
    · have hdψ : fderiv ℝ ψ x ≠ 0 := fun h' =>
        fderiv_apply_unitNormal_ne_zero hg hψ x (by rw [h']; rfl)
      exact hBo.inter_closure ⟨hxB, mem_closure_A (hψ.smooth.of_le (by simp)) hdψ h.symm⟩
  have hcont : ContinuousOn (fun x => (D Ψ' x)ᵀ * g' (Ψ' x) * D Ψ' x) t := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hfd : Continuous fun x : t => fderiv ℝ Ψ' x :=
      continuousOn_iff_continuous_domRestrict.1
        ((hΨ'.continuousOn_fderiv_of_isOpen hBo (by simp)).mono inter_subset_left)
    have hDc : Continuous fun x : t => D Ψ' x := continuous_matrix fun i j => by
      simp only [D_def]
      exact (EuclideanSpace.proj i : E n →L[ℝ] ℝ).continuous.comp (hfd.clm_apply continuous_const)
    have hΨc : Continuous fun x : t => Ψ' x :=
      continuousOn_iff_continuous_domRestrict.1 (hΨ'.continuousOn.mono inter_subset_left)
    have hg'c : Continuous fun x : t => g' (Ψ' x) :=
      continuous_matrix fun i j => (hg'.smooth i j).continuous.comp hΨc
    exact (hDc.matrix_transpose.matrix_mul hg'c).matrix_mul hDc
  have hgc : ContinuousOn g t :=
    (continuous_matrix fun i j => (hg.smooth i j).continuous).continuousOn
  have hpull : EqOn g (fun x => (D Ψ' x)ᵀ * g' (Ψ' x) * D Ψ' x) t :=
    EqOn.of_subset_closure hpullA hgc hcont
      (fun x hx => ⟨hx.1, show τ ≤ ψ x from le_of_lt (mem_A.1 hx.2)⟩) hts
  refine ⟨B, hBo, hq₀B, Ψ', hΨ', hΨ'q₀, hagree, fun x hxB hxτ => hpull ⟨hxB, hxτ⟩, ?_⟩
  exact det_ne_zero_of_pullback (hpull ⟨hq₀B, hq₀.ge⟩) (hg.det_ne_zero q₀)

/-- **Behaviour at the frontier** (blueprint, Lemma `lem_frontier`), for an immersion
`v' = (v'ᵢ)` on `W` by solutions of `□_{g'} v'ᵢ = 0` (as given by `exists_solution_coords`) and
its transfer `v = (𝒯 v'ᵢ)`: for `q₀ ∈ Σ_τ ∩ W`,
(a) `Ψ(q) → p₀ ∈ W` as `q → q₀` in `A_τ`, and `v'(p₀) = v(q₀)`;
(b) `p₀ = q₀` if `q₀ ∈ ∂W`;
(c) `Ψ` has a smooth extension `Ψ'` near `q₀`, pulling `g'` back to `g` on `{ψ ≥ τ}`, with
`dΨ'(q₀)` invertible. -/
theorem frontier (hP : ExtensionProperty g g' ψ (W n T) τ Ψ)
    (hgA : IsAdmissibleMetric n T g) (hg'A : IsAdmissibleMetric n T g')
    (hg : IsSpacetime g Y) (hg' : IsSpacetime g' Y')
    (hY : ∀ x ∉ M0 n T, form (g x) (EuclideanSpace.single 0 1) (Y x) < 0)
    (hY' : ∀ x ∉ M0 n T, form (g' x) (EuclideanSpace.single 0 1) (Y' x) < 0)
    (hC : CauchyDataSubset n T g g') (hψ : IsCauchyTemporal g Y ψ)
    (hΦ : Continuous fun p : ℝ × E n => Φ p.1 p.2) (hΦ0 : ∀ x, Φ 0 x = x)
    (hΦψ : ∀ t x, ψ (Φ t x) = ψ x + t) {m : ℕ} {v' : Fin m → E n → ℝ}
    (hv' : ∀ i, ContDiff ℝ ∞ (v' i)) (hbox' : ∀ i x, box g' (v' i) x = 0)
    (himm : ∀ x ∈ W n T, Injective (fderiv ℝ (fun y i => v' i y) x)) {q₀ : E n}
    (hq₀ : ψ q₀ = τ) (hq₀W : q₀ ∈ W n T) :
    ∃ p₀ ∈ W n T, Tendsto Ψ (𝓝[A ψ τ] q₀) (𝓝 p₀) ∧
      (∀ i, v' i p₀ = transfer n T g (v' i) q₀) ∧
      (q₀ ∈ frontier (W n T) → p₀ = q₀) ∧
      ∃ B : Set (E n), IsOpen B ∧ q₀ ∈ B ∧ ∃ Ψ' : E n → E n, ContDiffOn ℝ ∞ Ψ' B ∧
        Ψ' q₀ = p₀ ∧ (∀ q ∈ B ∩ A ψ τ, Ψ' q = Ψ q) ∧
        (∀ x ∈ B, τ ≤ ψ x → g x = (D Ψ' x)ᵀ * g' (Ψ' x) * D Ψ' x) ∧ (D Ψ' q₀).det ≠ 0 := by
  obtain ⟨p₀, hp₀W, hlim, hp₀V⟩ := hP.frontier_tendsto hgA hg'A hg hg' hY hY' hC hψ hΦ hΦ0 hΦψ
    hv' hbox' himm hq₀ hq₀W
  exact ⟨p₀, hp₀W, hlim, hp₀V, fun hfr => hP.frontier_eq hgA hg hY hψ hq₀ hfr hlim,
    hP.frontier_extension hgA hg'A hg hg' hY hY' hC hψ hv' hbox' himm hq₀ hp₀W hlim hp₀V⟩

end ExtensionProperty

end

end LorentzianCalderon
