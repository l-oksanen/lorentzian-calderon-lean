module

public import LorentzianCalderon.Induction.FrontierTransport
public import LorentzianCalderon.Induction.Setup

public section

/-!
# The amplitude across the frontier

Blueprint `lem_ind_amplitude`, the jets and Borel's lemma. Above the frontier the wave `u_s` is
`B♮(·, φ - s)` for the family `B♮(x, r) = c(r) u(φ(x) - r, x)`, with a cut-off `c` equal to `1`
on the relevant values of `r`. Its jets at `r = 0` solve the transport hierarchy above the
frontier; they are extended across it by `exists_hierarchy` and summed by Borel's lemma, and the
result is glued to `B♮` above a level `ℓ` (`IsFrontierAmplitude`).
-/

namespace LorentzianCalderon

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

variable {n : ℕ} {g : MatrixField n} {Y : E n → E n} {ψ φ : E n → ℝ}

variable (g) in
/-- An amplitude on `O` across the frontier, which agrees with the wave `u` above the level `ℓ`:
`B` is smooth, its remainder `R` vanishes to infinite order at `r = 0`, `B(·, 0)` solves the
transport equation, `B(·, φ - s) = u_s` near the points above `ℓ`, and `B(·, 0) > 0` where
`|φ| < η₂`. -/
structure IsFrontierAmplitude (ψ φ : E n → ℝ) (u : ℝ → E n → ℝ) (O : Set (E n)) (η₂ ℓ : ℝ)
    (B : E n → ℝ → ℝ) : Prop where
  smooth : ContDiffOn ℝ ∞ (fun q : E n × ℝ => B q.1 q.2) (O ×ˢ univ)
  flat : ∀ k, ∀ x ∈ O, iteratedDeriv k (amplitudeRemainder g φ B x) 0 = 0
  transport : ∀ x ∈ O,
    2 * -coform g x (d φ x) (d (fun y => B y 0) x) + B x 0 * box g φ x = 0
  top : ∀ s ∈ Ioo (-η₂) η₂, ∀ x ∈ O, ℓ < ψ x → (fun y => B y (φ y - s)) =ᶠ[𝓝 x] u s
  pos : ∀ x ∈ O, |φ x| < η₂ → 0 < B x 0


/-! ### Calculus on the line -/

theorem iteratedDeriv_zero_fun (k : ℕ) (r : ℝ) : iteratedDeriv k (fun _ : ℝ => (0 : ℝ)) r = 0 := by
  rw [iteratedDeriv_eq_iterate, Function.iterate_fixed (by simp)]

/-- A smooth function vanishing on `(0, ε)` vanishes to infinite order at `0`. -/
theorem iteratedDeriv_eq_zero_of_eqOn_Ioo {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {ε : ℝ}
    (hε : 0 < ε) (h0 : ∀ r ∈ Ioo 0 ε, f r = 0) (k : ℕ) : iteratedDeriv k f 0 = 0 := by
  have hc : Continuous (iteratedDeriv k f) := hf.continuous_iteratedDeriv k (by simp)
  have hEq : EqOn (iteratedDeriv k f) (iteratedDeriv k fun _ => (0 : ℝ)) (Ioo 0 ε) :=
    (show EqOn f (fun _ => (0 : ℝ)) (Ioo 0 ε) from h0).iteratedDeriv_of_isOpen isOpen_Ioo k
  have hmem : (0 : ℝ) ∈ closure (Ioo 0 ε) := by
    rw [closure_Ioo hε.ne]
    exact left_mem_Icc.2 hε.le
  exact (isClosed_eq hc continuous_const).closure_subset_iff.2
    (fun r hr => by rw [mem_ofPred_eq, hEq hr, iteratedDeriv_zero_fun]) hmem

theorem iteratedDeriv_eq_zero_of_eventuallyEq {f : ℝ → ℝ} (hf : f =ᶠ[𝓝 0] fun _ => 0)
    (k : ℕ) : iteratedDeriv k f 0 = 0 := by
  rw [hf.iteratedDeriv_eq k, iteratedDeriv_zero_fun]

/-! ### The family `B♮(x, r) = c(r) u(φ(x) - r, x)` -/

/-- Near a point where `c = 1` at `φ(x) - s`, the wave of `B♮` is `u_s`. -/
theorem cutoffFamily_eventuallyEq {c : ℝ → ℝ} {u : ℝ → E n → ℝ} {x : E n}
    (hφx : ContinuousAt φ x) {s : ℝ} (hc : c =ᶠ[𝓝 (φ x - s)] 1) :
    (fun y => c (φ y - s) * u (φ y - (φ y - s)) y) =ᶠ[𝓝 x] u s := by
  filter_upwards [(hφx.sub continuousAt_const).eventually hc] with y hy
  have h1 : c (φ y - s) = 1 := hy
  simp [h1]

theorem contDiffOn_cutoffFamily {U O : Set (E n)} (hU : IsOpen U) (hOU : O ⊆ U)
    (hφ : ContDiffOn ℝ ∞ φ U) {η : ℝ} {u : ℝ → E n → ℝ}
    (hu : ContDiffOn ℝ ∞ (fun p : ℝ × E n => u p.1 p.2) (Ioo (-η) η ×ˢ U)) {c : ℝ → ℝ}
    (hc : ContDiff ℝ ∞ c) (hP1 : ∀ x ∈ O, ∀ r ∈ tsupport c, φ x - r ∈ Ioo (-η) η) :
    ContDiffOn ℝ ∞ (fun q : E n × ℝ => c q.2 * u (φ q.1 - q.2) q.1) (O ×ˢ univ) := by
  intro q hq
  refine ContDiffAt.contDiffWithinAt ?_
  by_cases hr : q.2 ∈ tsupport c
  · have h1 : ContDiffAt ℝ ∞ (fun q : E n × ℝ => (φ q.1 - q.2, q.1)) q :=
      (((hφ.contDiffAt (hU.mem_nhds (hOU hq.1))).comp q contDiffAt_fst).sub
        contDiffAt_snd).prodMk contDiffAt_fst
    have h2 : ContDiffAt ℝ ∞ (fun p : ℝ × E n => u p.1 p.2) (φ q.1 - q.2, q.1) :=
      hu.contDiffAt ((isOpen_Ioo.prod hU).mem_nhds ⟨hP1 q.1 hq.1 q.2 hr, hOU hq.1⟩)
    exact (hc.contDiffAt.comp q contDiffAt_snd).mul
      (ContDiffAt.comp (f := fun q : E n × ℝ => (φ q.1 - q.2, q.1)) q h2 h1)
  · have hev : (fun q : E n × ℝ => c q.2 * u (φ q.1 - q.2) q.1) =ᶠ[𝓝 q] fun _ => 0 := by
      filter_upwards [(continuous_snd.tendsto q).eventually
        (notMem_tsupport_iff_eventuallyEq.1 hr)] with p hp
      simp [show c p.2 = 0 from hp]
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-- **The jets above the frontier.** When `c = 1` near `0`, the jets of `B♮` at `r = 0` solve
the transport hierarchy above the frontier, with positive leading term. -/
theorem cutoffFamily_jets (hg : IsSpacetime g Y) {U O : Set (E n)}
    (hφ : IsFutureEikonal g Y φ U) (hO : IsOpen O) (hOU : O ⊆ U) {η τ : ℝ}
    {u a b : ℝ → E n → ℝ}
    (hu : ContDiffOn ℝ ∞ (fun p : ℝ × E n => u p.1 p.2) (Ioo (-η) η ×ˢ U)) {c : ℝ → ℝ}
    (hc : ContDiff ℝ ∞ c) (hP1 : ∀ x ∈ O, ∀ r ∈ tsupport c, φ x - r ∈ Ioo (-η) η)
    (hc1 : c =ᶠ[𝓝 0] 1)
    (hbox : ∀ s ∈ Ioo (-η) η, ∀ x ∈ U ∩ A ψ τ, box g (u s) x = (φ x - s) * a s x)
    (ha0 : ∀ s ∈ Ioo (-η) η, ∀ x ∈ U ∩ A ψ τ, s < φ x → a s x = 0)
    (htr : ∀ s ∈ Ioo (-η) η, ∀ x ∈ U ∩ A ψ τ,
      2 * -coform g x (d φ x) (d (u s) x) + u s x * box g φ x = (φ x - s) * b s x)
    (hpos : ∀ s ∈ Ioo (-η) η, ∀ x ∈ U ∩ A ψ τ, φ x = s → 0 < u s x) {x : E n}
    (hx : x ∈ O) (hxA : τ < ψ x) :
    (∀ k, 2 * -coform g x (d φ x)
        (d (fun y => iteratedDeriv (k + 1) (fun r => c r * u (φ y - r) y) 0) x) +
      iteratedDeriv (k + 1) (fun r => c r * u (φ x - r) x) 0 * box g φ x =
        -box g (fun y => iteratedDeriv k (fun r => c r * u (φ y - r) y) 0) x) ∧
    2 * -coform g x (d φ x) (d (fun y => iteratedDeriv 0 (fun r => c r * u (φ y - r) y) 0) x) +
      iteratedDeriv 0 (fun r => c r * u (φ x - r) x) 0 * box g φ x = 0 ∧
    0 < iteratedDeriv 0 (fun r => c r * u (φ x - r) x) 0 := by
  set Bn : E n → ℝ → ℝ := fun y r => c r * u (φ y - r) y with hBn_def
  have hBn : ContDiffOn ℝ ∞ (fun q : E n × ℝ => Bn q.1 q.2) (O ×ˢ univ) :=
    contDiffOn_cutoffFamily hφ.isOpen hOU hφ.smooth hu hc hP1
  have hφO : ContDiffOn ℝ ∞ φ O := hφ.smooth.mono hOU
  have heik : ∀ y ∈ O, coform g y (d φ y) (d φ y) = 0 := fun y hy => hφ.eikonal y (hOU hy)
  have hxU : x ∈ U ∩ A ψ τ := ⟨hOU hx, (mem_A.2 hxA)⟩
  have hφx : ContinuousAt φ x := (hφ.smooth.continuousOn.continuousAt (hφ.isOpen.mem_nhds hxU.1))
  have hc0 : c 0 = 1 := hc1.eq_of_nhds
  have hφη : φ x ∈ Ioo (-η) η := by
    simpa using hP1 x hx 0 (subset_tsupport _ (by simp [hc0]))
  obtain ⟨ε₁, hε₁, hball⟩ := Metric.eventually_nhds_iff.1 hc1
  have hflat : ∀ k, iteratedDeriv k (amplitudeRemainder g φ Bn x) 0 = 0 := by
    have hR : ContDiff ℝ ∞ (amplitudeRemainder g φ Bn x) :=
      (SmoothFamily.remainder hg.smooth hg.det_ne_zero hO (smoothFamily_iff.2 hBn) hφO).slice hx
    refine iteratedDeriv_eq_zero_of_eqOn_Ioo hR (ε := min ε₁ (φ x + η))
      (lt_min hε₁ (by linarith [hφη.1])) fun r hr => ?_
    set s := φ x - r
    have hs : s ∈ Ioo (-η) η := ⟨by linarith [hr.2.trans_le (min_le_right _ _)],
      by linarith [hr.1, hφη.2]⟩
    have hev : c =ᶠ[𝓝 (φ x - s)] 1 := by
      have hrs : φ x - s = r := by simp [s]
      rw [hrs]
      filter_upwards [Metric.isOpen_ball.mem_nhds (show r ∈ Metric.ball (0 : ℝ) ε₁ by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hr.1]
        exact hr.2.trans_le (min_le_left _ _))] with t ht
      exact hball ht
    have h1 := box_comp_sub_eq hg.smooth hg.symm hg.det_ne_zero hO hBn hφO heik s hx
    rw [box_congr (cutoffFamily_eventuallyEq hφx hev), hbox s hs x hxU,
      ha0 s hs x hxU (by simp [s, hr.1]), mul_zero] at h1
    rw [show r = φ x - s by simp [s], ← h1]
  refine ⟨fun k => ?_, ?_, ?_⟩
  · have h := iteratedDeriv_amplitudeRemainder (φ := φ) hg.smooth hg.det_ne_zero hO hBn
      (b := fun k y => iteratedDeriv k (Bn y) 0) (fun _ _ _ => rfl) k hx
    rw [hflat k] at h
    simp only [hBn_def] at h ⊢
    linarith
  · have hev : c =ᶠ[𝓝 (φ x - φ x)] 1 := by rwa [sub_self]
    have h1 := coform_d_comp_sub hO hBn hφO heik (φ x) hx
    rw [d_congr (cutoffFamily_eventuallyEq hφx hev), sub_self] at h1
    have h2 := htr (φ x) hφη x hxU
    simp only [iteratedDeriv_zero, hBn_def, sub_self, sub_zero, hc0, one_mul, zero_mul] at h1 h2 ⊢
    rw [← h1]
    exact h2
  · simpa [hc0] using hpos (φ x) hφη x hxU rfl

/-- **Borel's lemma and gluing**: jets `b` on `O` solving the transport hierarchy and equal to
those of `B♮` above the frontier are the jets of an amplitude equal to `B♮` above the level `ℓ`. -/
theorem exists_isFrontierAmplitude_of_jets (hg : IsSpacetime g Y)
    (hψ : IsCauchyTemporal g Y ψ) {U O : Set (E n)} (hφ : IsFutureEikonal g Y φ U)
    (hO : IsOpen O) (hOU : O ⊆ U) {η η₂ τ ℓ : ℝ} (hℓ : τ < ℓ) {u : ℝ → E n → ℝ}
    (hu : ContDiffOn ℝ ∞ (fun p : ℝ × E n => u p.1 p.2) (Ioo (-η) η ×ˢ U)) {c : ℝ → ℝ}
    (hc : ContDiff ℝ ∞ c) (hP1 : ∀ x ∈ O, ∀ r ∈ tsupport c, φ x - r ∈ Ioo (-η) η)
    (hP2 : ∀ s ∈ Ioo (-η₂) η₂, ∀ x ∈ O, c =ᶠ[𝓝 (φ x - s)] 1) {b : ℕ → E n → ℝ}
    (hb : ∀ k, ContDiffOn ℝ ∞ (b k) O)
    (htr0 : ∀ x ∈ O, 2 * -coform g x (d φ x) (d (b 0) x) + b 0 x * box g φ x = 0)
    (htrs : ∀ k, ∀ x ∈ O,
      2 * -coform g x (d φ x) (d (b (k + 1)) x) + b (k + 1) x * box g φ x = -box g (b k) x)
    (hjet : ∀ k, ∀ x ∈ O, τ < ψ x → iteratedDeriv k (fun r => c r * u (φ x - r) x) 0 = b k x)
    (hpos : ∀ x ∈ O, |φ x| < η₂ → 0 < b 0 x) :
    ∃ B : E n → ℝ → ℝ, IsFrontierAmplitude g ψ φ u O η₂ ℓ B := by
  set Bn : E n → ℝ → ℝ := fun y r => c r * u (φ y - r) y with hBn_def
  have hBn : ContDiffOn ℝ ∞ (fun q : E n × ℝ => Bn q.1 q.2) (O ×ˢ univ) :=
    contDiffOn_cutoffFamily hφ.isOpen hOU hφ.smooth hu hc hP1
  obtain ⟨B₂, hB₂, hB₂b, -⟩ := Facts.borel hO hb
  set κ : ℝ → ℝ := fun t => Real.smoothTransition ((t - τ) / (ℓ - τ)) with hκ_def
  have hℓτ : 0 < ℓ - τ := sub_pos.2 hℓ
  have hκ : ContDiff ℝ ∞ κ :=
    Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)
  have hκ0 : ∀ t, t ≤ τ → κ t = 0 := fun t ht =>
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hℓτ.le)
  have hκ1 : ∀ t, ℓ ≤ t → κ t = 1 := fun t ht =>
    Real.smoothTransition.one_of_one_le ((one_le_div hℓτ).2 (by linarith))
  set B : E n → ℝ → ℝ := fun y r => κ (ψ y) * Bn y r + (1 - κ (ψ y)) * B₂ y r with hB_def
  have hκψ : ContDiffOn ℝ ∞ (fun q : E n × ℝ => κ (ψ q.1)) (O ×ˢ univ) :=
    (hκ.comp (hψ.smooth.comp contDiff_fst)).contDiffOn
  have hB : ContDiffOn ℝ ∞ (fun q : E n × ℝ => B q.1 q.2) (O ×ˢ univ) :=
    (hκψ.mul hBn).add ((contDiffOn_const.sub hκψ).mul hB₂)
  have hBnf : SmoothFamily O Bn := (smoothFamily_iff.2 hBn)
  have hB₂f : SmoothFamily O B₂ := (smoothFamily_iff.2 hB₂)
  have hjets : ∀ k, ∀ x ∈ O, iteratedDeriv k (B x) 0 = b k x := by
    intro k x hx
    have h1 : ContDiffAt ℝ k (Bn x) 0 := ((hBnf.slice hx).of_le (by simp)).contDiffAt
    have h2 : ContDiffAt ℝ k (B₂ x) 0 := ((hB₂f.slice hx).of_le (by simp)).contDiffAt
    have hBx : B x = fun r => κ (ψ x) * Bn x r + (1 - κ (ψ x)) * B₂ x r := rfl
    rw [hBx, iteratedDeriv_fun_add (contDiffAt_const.mul h1)
      (contDiffAt_const.mul h2), iteratedDeriv_const_mul _ h1,
      iteratedDeriv_const_mul _ h2, hB₂b k x hx]
    by_cases hxτ : τ < ψ x
    · rw [hjet k x hx hxτ]
      ring
    · rw [hκ0 _ (not_lt.1 hxτ)]
      ring
  have hB0 : ∀ x ∈ O, B x 0 = b 0 x := fun x hx => by simpa using hjets 0 x hx
  refine ⟨B, {
    smooth := hB
    flat := fun k x hx => by
      rw [iteratedDeriv_amplitudeRemainder (φ := φ) hg.smooth hg.det_ne_zero hO hB hjets k hx,
        mul_comm (box g φ x), add_assoc, htrs k x hx, add_neg_cancel]
    transport := fun x hx => by
      rw [d_congr (eventually_of_mem (hO.mem_nhds hx) hB0), hB0 x hx]
      exact htr0 x hx
    top := fun s hs x hx hxℓ => by
      have hφx : ContinuousAt φ x :=
        hφ.smooth.continuousOn.continuousAt (hφ.isOpen.mem_nhds (hOU hx))
      filter_upwards [hO.mem_nhds hx, (hψ.smooth.continuous.tendsto x).eventually
        (lt_mem_nhds hxℓ), cutoffFamily_eventuallyEq (u := u) hφx (hP2 s hs x hx)]
        with y hyO hyℓ hyu
      rw [← hyu]
      simp only [hB_def, hκ1 _ hyℓ.le, hBn_def]
      ring
    pos := fun x hx hxη => by
      rw [hB0 x hx]
      exact hpos x hx hxη }⟩

/-- **The amplitude across the frontier**: on a neighbourhood `O` of `q₀`, for every level
`ℓ > τ` there is an amplitude agreeing with `u` above `ℓ`. -/
theorem exists_isFrontierAmplitude (hg : IsSpacetime g Y) (hψ : IsCauchyTemporal g Y ψ)
    {τ : ℝ} {q₀ : E n} (hq₀ : ψ q₀ = τ) {U : Set (E n)}
    (hφ : IsFutureEikonal g Y φ U) (hq₀U : q₀ ∈ U) {η : ℝ} (hη : 0 < η)
    {u a b : ℝ → E n → ℝ}
    (hu : ContDiffOn ℝ ∞ (fun p : ℝ × E n => u p.1 p.2) (Ioo (-η) η ×ˢ U))
    (hbox : ∀ s ∈ Ioo (-η) η, ∀ x ∈ U ∩ A ψ τ, box g (u s) x = (φ x - s) * a s x)
    (ha0 : ∀ s ∈ Ioo (-η) η, ∀ x ∈ U ∩ A ψ τ, s < φ x → a s x = 0)
    (htr : ∀ s ∈ Ioo (-η) η, ∀ x ∈ U ∩ A ψ τ,
      2 * -coform g x (d φ x) (d (u s) x) + u s x * box g φ x = (φ x - s) * b s x)
    (hpos : ∀ s ∈ Ioo (-η) η, ∀ x ∈ U ∩ A ψ τ, φ x = s → 0 < u s x) :
    ∃ (O : Set (E n)) (η₂ : ℝ), IsOpen O ∧ q₀ ∈ O ∧ O ⊆ U ∧ 0 < η₂ ∧ η₂ ≤ η ∧
      ∀ ℓ, τ < ℓ → ∃ B : E n → ℝ → ℝ, IsFrontierAmplitude g ψ φ u O η₂ ℓ B := by
  have hφc : ContinuousOn φ U := hφ.smooth.continuousOn
  by_cases hφ₀ : |φ q₀| < η / 4
  · set T₀ := U ∩ φ ⁻¹' Ioo (-(η / 4)) (η / 4)
    have hT₀ : IsOpen T₀ := hφc.isOpen_inter_preimage hφ.isOpen isOpen_Ioo
    have hφT : IsFutureEikonal g Y φ T₀ :=
      ⟨hT₀, hφ.smooth.mono inter_subset_left, fun x hx => hφ.eikonal x hx.1,
        fun x hx => hφ.d_ne_zero x hx.1, fun x hx => hφ.future x hx.1⟩
    have hq₀T : q₀ ∈ T₀ := ⟨hq₀U, abs_lt.1 hφ₀⟩
    obtain ⟨Zh, X, p, τ₀, hD, hτ₀, hq₀B, hp, hp0, hpZ⟩ := exists_flowBox_eikonal hg hψ hφT hq₀T
    set O := boxSet T₀ ψ Zh τ₀
    have hO : IsOpen O := hD.isOpen_boxSet τ₀
    have hOT : O ⊆ T₀ := FlowBoxData.boxSet_subset τ₀
    have hOU : O ⊆ U := hOT.trans inter_subset_left
    let cb : ContDiffBump (0 : ℝ) := ⟨η / 2, 5 * η / 8, by positivity, by linarith⟩
    have hc : ContDiff ℝ ∞ (cb : ℝ → ℝ) := cb.contDiff
    have hP1 : ∀ x ∈ O, ∀ r ∈ tsupport (cb : ℝ → ℝ), φ x - r ∈ Ioo (-η) η := by
      intro x hx r hr
      rw [cb.tsupport_eq, Metric.mem_closedBall, Real.dist_eq, sub_zero] at hr
      have h1 : φ x ∈ Ioo (-(η / 4)) (η / 4) := (hOT hx).2
      have h2 := abs_le.1 hr
      simp only [cb] at h2
      exact ⟨by linarith [h1.1, h1.2, h2.1, h2.2], by linarith [h1.1, h1.2, h2.1, h2.2]⟩
    have hone : ∀ t, |t| < η / 2 → (cb : ℝ → ℝ) =ᶠ[𝓝 t] 1 := fun t ht => by
      filter_upwards [Metric.isOpen_ball.mem_nhds (show t ∈ Metric.ball (0 : ℝ) (η / 2) by
        rwa [Metric.mem_ball, Real.dist_eq, sub_zero])] with r hr
      exact cb.one_of_mem_closedBall (Metric.ball_subset_closedBall hr)
    have hP2 : ∀ s ∈ Ioo (-(η / 4)) (η / 4), ∀ x ∈ O, (cb : ℝ → ℝ) =ᶠ[𝓝 (φ x - s)] 1 :=
      fun s hs x hx => by
        have h1 : φ x ∈ Ioo (-(η / 4)) (η / 4) := (hOT hx).2
        exact hone _ (abs_lt.2 ⟨by linarith [h1.1, hs.2], by linarith [h1.2, hs.1]⟩)
    have hc1 : (cb : ℝ → ℝ) =ᶠ[𝓝 0] 1 := hone 0 (by simp; positivity)
    set bj : ℕ → E n → ℝ := fun k y => iteratedDeriv k (fun r => cb r * u (φ y - r) y) 0
    have hBn : ContDiffOn ℝ ∞ (fun q : E n × ℝ => cb q.2 * u (φ q.1 - q.2) q.1) (O ×ˢ univ) :=
      contDiffOn_cutoffFamily hφ.isOpen hOU hφ.smooth hu hc hP1
    have hbj : ∀ k, ContDiffOn ℝ ∞ (bj k) O := fun k =>
      (smoothFamily_iff.1
        (iteratedDeriv_family (B := fun y r => cb r * u (φ y - r) y) hO
          (smoothFamily_iff.2 hBn) k)).comp
        (contDiff_id.prodMk contDiff_const).contDiffOn
        fun y hy => ⟨hy, mem_univ _⟩
    have hjets := fun x (hx : x ∈ O) (hxA : τ < ψ x) =>
      cutoffFamily_jets hg hφ hO hOU hu hc hP1 hc1 hbox ha0 htr hpos hx hxA
    obtain ⟨bk, hbk, hbk0, hbks, hbkeq, hbkpos⟩ := exists_hierarchy hg hφT hD hp hp0 hpZ
      (ℓ := τ) (by rwa [← hq₀]) (bn := bj) hbj (fun x hx hxA => (hjets x hx hxA).2.1)
      (fun k x hx hxA => (hjets x hx hxA).1 k)
      (fun x hx hxτ => (hjets x hx (by rw [hxτ, ← hq₀]; exact hτ₀)).2.2)
    refine ⟨O, η / 4, hO, hq₀B, hOU, by positivity, by linarith, fun ℓ hℓ => ?_⟩
    exact exists_isFrontierAmplitude_of_jets hg hψ hφ hO hOU hℓ hu hc hP1 hP2 hbk hbk0 hbks
      (fun k x hx hxA => (hbkeq k x hx hxA).symm) fun x hx _ => hbkpos x hx
  · set φ₀ := φ q₀
    set O := U ∩ φ ⁻¹' Ioo (φ₀ - η / 16) (φ₀ + η / 16)
    have hO : IsOpen O := hφc.isOpen_inter_preimage hφ.isOpen isOpen_Ioo
    have hOU : O ⊆ U := inter_subset_left
    let cb : ContDiffBump φ₀ := ⟨η / 8, 3 * η / 16, by positivity, by linarith⟩
    have hc : ContDiff ℝ ∞ (cb : ℝ → ℝ) := cb.contDiff
    have hP1 : ∀ x ∈ O, ∀ r ∈ tsupport (cb : ℝ → ℝ), φ x - r ∈ Ioo (-η) η := by
      intro x hx r hr
      rw [cb.tsupport_eq, Metric.mem_closedBall, Real.dist_eq] at hr
      have h1 : φ x ∈ Ioo (φ₀ - η / 16) (φ₀ + η / 16) := hx.2
      have h2 := abs_le.1 hr
      simp only [cb] at h2
      exact ⟨by linarith [h1.1, h1.2, h2.1, h2.2], by linarith [h1.1, h1.2, h2.1, h2.2]⟩
    have hP2 : ∀ s ∈ Ioo (-(η / 16)) (η / 16), ∀ x ∈ O, (cb : ℝ → ℝ) =ᶠ[𝓝 (φ x - s)] 1 := by
      intro s hs x hx
      have h1 : φ x ∈ Ioo (φ₀ - η / 16) (φ₀ + η / 16) := hx.2
      filter_upwards [Metric.isOpen_ball.mem_nhds (show φ x - s ∈ Metric.ball φ₀ (η / 8) by
        rw [Metric.mem_ball, Real.dist_eq]
        exact abs_lt.2 ⟨by linarith [h1.1, hs.2], by linarith [h1.2, hs.1]⟩)] with r hr
      exact cb.one_of_mem_closedBall (Metric.ball_subset_closedBall hr)
    have hc0 : (cb : ℝ → ℝ) =ᶠ[𝓝 0] 0 := by
      refine notMem_tsupport_iff_eventuallyEq.1 fun h => ?_
      rw [cb.tsupport_eq, Metric.mem_closedBall, Real.dist_eq, zero_sub, abs_neg] at h
      simp only [cb] at h
      exact hφ₀ (by linarith)
    refine ⟨O, η / 16, hO, ⟨hq₀U, by simp only [mem_preimage, mem_Ioo]; constructor <;> linarith⟩,
      hOU, by positivity, by linarith, fun ℓ hℓ => ?_⟩
    refine exists_isFrontierAmplitude_of_jets hg hψ hφ hO hOU hℓ hu hc hP1 hP2
      (b := fun _ _ => 0) (fun _ => contDiffOn_const) (fun x _ => by simp [d_def, coform_def])
      (fun k x _ => by simp [d_def, coform_def, box_def]) (fun k x _ _ => ?_) fun x hx hxη => ?_
    · refine iteratedDeriv_eq_zero_of_eventuallyEq ?_ k
      filter_upwards [hc0] with r hr
      simp [show cb r = 0 from hr]
    · have h1 : φ x ∈ Ioo (φ₀ - η / 16) (φ₀ + η / 16) := hx.2
      exact absurd hφ₀ (not_not.2 (by
        rw [abs_lt] at hxη ⊢
        exact ⟨by linarith [h1.1, h1.2, hxη.1], by linarith [h1.1, h1.2, hxη.2]⟩))

end

end LorentzianCalderon
