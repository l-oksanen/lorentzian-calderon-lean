module

public import LorentzianCalderon.Induction.FrontierJets
public import LorentzianCalderon.Induction.FrontierLens
public import LorentzianCalderon.Induction.Propagation

public section

/-!
# The amplitude of the `g`-waves near a frontier point

Blueprint, Lemmas `lem_ind_amplitude` and `lem_ind_frontier_wave`: near `q₀ ∈ Σ_τ`, a
distribution `U_s = G^ret F_s` with `□ U_s = 0`, which is a one-sided wave `u_s H(φ - s)` with the
conormal properties above `Σ_τ` and vanishes on `{φ < s}`, is a one-sided wave with the conormal
properties on a neighbourhood of `q₀` (`exists_wave_of_frontier`).

The amplitude `B` across the frontier comes from `exists_isFrontierAmplitude`; it agrees with `u`
above a level `ℓ > τ`, and `ũ_s = B(·, φ - s)` satisfies `□(ũ_s H(φ - s)) = R_+(·, φ - s)` with a
smooth `R_+`. The correction is `v_s = G^adv(ζ R_+(·, φ - s))` for a cut-off `ζ`, which vanishes
above `ℓ` since `R_+(·, φ - s)` does. The duality argument uses `P = κ(ψ) G^ret h` for a test
function `h` near `q₀`, where `κ(ψ)` cuts off above `ℓ`, and the small lens `J⁺(K) ∩ {ψ ≤ c}` for
a small ball `K` around `q₀` (`IsCauchyTemporal.exists_causalFutureSet_inter_le_subset`,
`lem_ind_small_lens`); the commutator term lives above `ℓ`, where `U_s = ũ_s H(φ - s)` and
`v_s = 0`.
-/

namespace LorentzianCalderon

noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped ContDiff Topology

variable {n : ℕ} {g : MatrixField n} {Y : E n → E n} {ψ : E n → ℝ}

/-! ### Agreement of functionals with functions -/

theorem continuous_mul_of_continuousOn_of_tsupport {f h : E n → ℝ} {W : Set (E n)}
    (hW : IsOpen W) (hf : ContinuousOn f W) (hh : Continuous h) (hhW : tsupport h ⊆ W) :
    Continuous fun x => f x * h x := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  by_cases hx : x ∈ W
  · exact (hf.continuousAt (hW.mem_nhds hx)).mul hh.continuousAt
  · have hev : (fun y => f y * h y) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 fun h' => hx (hhW h')] with y hy
      simp [hy]
    exact continuousAt_const.congr hev.symm

/-- Two functions continuous on an open set `W` with which a functional agrees on `W` are equal
there. -/
theorem AgreesOn.eqOn_of_continuousOn (hgs : ∀ i j, ContDiff ℝ ∞ fun x => g x i j)
    (hdet : ∀ x, (g x).det ≠ 0) {U : (E n → ℝ) → ℝ} {f f' : E n → ℝ} {W : Set (E n)}
    (hW : IsOpen W) (hf : ContinuousOn f W) (hf' : ContinuousOn f' W) (h₁ : AgreesOn g U f W)
    (h₂ : AgreesOn g U f' W) : ∀ x ∈ W, f x = f' x := by
  set ρ : E n → ℝ := fun x => √|(g x).det|
  have hρ : Continuous ρ := (contDiff_sqrt_abs_det hgs hdet).continuous
  have hρpos : ∀ x, 0 < ρ x := fun x => Real.sqrt_pos.2 (abs_pos.2 (hdet x))
  have key := eqOn_zero_of_integral_mul_eq_zero_of_continuousOn hW
    (φ := fun x => (f x - f' x) * ρ x) ((hf.sub hf').mul hρ.continuousOn)
    fun h hh hhc hhW => by
      have hi : ∀ {k : E n → ℝ}, ContinuousOn k W → Integrable fun x => k x * h x * ρ x :=
        fun {k} hk => integrable_of_eq_zero_off
          ((continuous_mul_of_continuousOn_of_tsupport hW hk hh.continuous hhW).mul hρ) hhc
          fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx]
      have e : ∫ x, h x * ((f x - f' x) * ρ x) =
          (∫ x, f x * h x * ρ x) - ∫ x, f' x * h x * ρ x := by
        rw [← integral_sub (hi hf) (hi hf')]
        congr 1
        funext x
        ring
      rw [e, ← (agreesOn_iff.1 h₁) h hh hhc hhW, ← (agreesOn_iff.1 h₂) h hh hhc hhW, sub_self]
  intro x hx
  have := (mul_eq_zero.1 (key x hx)).resolve_right (hρpos x).ne'
  linarith

/-- Agreement only depends on the function almost everywhere on `W`. -/
theorem AgreesOn.congr_ae {U : (E n → ℝ) → ℝ} {f f' : E n → ℝ} {W : Set (E n)}
    (h : AgreesOn g U f W) (hff' : ∀ᵐ x, x ∈ W → f x = f' x) : AgreesOn g U f' W := by
  refine agreesOn_iff.2 fun k hk hkc hkW => ?_
  rw [(agreesOn_iff.1 h) k hk hkc hkW]
  refine integral_congr_ae ?_
  filter_upwards [hff'] with x hx
  by_cases hxW : x ∈ W
  · rw [hx hxW]
  · simp [image_eq_zero_of_notMem_tsupport fun h' => hxW (hkW h')]

/-! ### The duality argument -/

/-- **The wave near the frontier point** from an amplitude across the frontier (blueprint,
`lem_ind_frontier_wave`). Here `J⁺(B(q₀, r₀)) ∩ {ψ ≤ c₂} ⊆ O`, and the amplitude agrees with `u`
above the level `ℓ < c₁ < c₂`. -/
theorem exists_wave_of_isFrontierAmplitude (hg : IsSpacetime g Y) (hψ : IsCauchyTemporal g Y ψ)
    {τ : ℝ} {q₀ : E n} (hq₀ : ψ q₀ = τ) {U : Set (E n)} {φ : E n → ℝ}
    (hφ : IsFutureEikonal g Y φ U) {η : ℝ}
    {F : ℝ → (E n → ℝ) → ℝ} {K : ℝ → Set (E n)}
    (hF : ∀ s ∈ Ioo (-η) η, IsSource (F s) (K s))
    (hKU : ∀ s ∈ Ioo (-η) η, Disjoint U (K s))
    {u a : ℝ → E n → ℝ}
    (hu : ContDiffOn ℝ ∞ (fun p : ℝ × E n => u p.1 p.2) (Ioo (-η) η ×ˢ U))
    (hbox : ∀ s ∈ Ioo (-η) η, ∀ x ∈ U ∩ A ψ τ, box g (u s) x = (φ x - s) * a s x)
    (ha0 : ∀ s ∈ Ioo (-η) η, ∀ x ∈ U ∩ A ψ τ, s < φ x → a s x = 0)
    (hagree : ∀ s ∈ Ioo (-η) η,
      AgreesOn g (retardedS g Y (F s)) ({x | s ≤ φ x}.indicator (u s)) (U ∩ A ψ τ))
    (hvan : ∀ s ∈ Ioo (-η) η, VanishesOn (retardedS g Y (F s)) (U ∩ {x | φ x < s}))
    {O : Set (E n)} (hO : IsOpen O) (hOU : O ⊆ U) {η₂ ℓ c₁ c₂ r₀ : ℝ}
    (hη₂ : 0 < η₂) (hη₂η : η₂ ≤ η) (hℓ : τ < ℓ) (hc₁ : ℓ < c₁) (hc₂ : c₁ < c₂) (hr₀ : 0 < r₀)
    (hKc : causalFutureSet g Y (closedBall q₀ r₀) ∩ {x | ψ x ≤ c₂} ⊆ O)
    (hKcc : IsCompact (causalFutureSet g Y (closedBall q₀ r₀) ∩ {x | ψ x ≤ c₂}))
    {B : E n → ℝ → ℝ} (hB : IsFrontierAmplitude g ψ φ u O η₂ ℓ B) :
    ∃ (V : Set (E n)) (η₃ : ℝ) (w a₂ b₂ : ℝ → E n → ℝ), IsOpen V ∧ q₀ ∈ V ∧ V ⊆ U ∧
      0 < η₃ ∧ η₃ ≤ η ∧
      ContDiffOn ℝ ∞ (fun p : ℝ × E n => w p.1 p.2) (Ioo (-η₃) η₃ ×ˢ V) ∧
      (∀ s ∈ Ioo (-η₃) η₃,
        AgreesOn g (retardedS g Y (F s)) ({x | s ≤ φ x}.indicator (w s)) V) ∧
      (∀ s ∈ Ioo (-η₃) η₃, ∀ x ∈ V ∩ A ψ τ, s ≤ φ x → w s x = u s x) ∧
      (∀ s ∈ Ioo (-η₃) η₃, ∀ x ∈ V, φ x = s → 0 < w s x) ∧
      ContDiffOn ℝ ∞ (fun p : ℝ × E n => a₂ p.1 p.2) (Ioo (-η₃) η₃ ×ˢ V) ∧
      ContDiffOn ℝ ∞ (fun p : ℝ × E n => b₂ p.1 p.2) (Ioo (-η₃) η₃ ×ˢ V) ∧
      (∀ s ∈ Ioo (-η₃) η₃, ∀ x ∈ V, box g (w s) x = (φ x - s) * a₂ s x) ∧
      (∀ s ∈ Ioo (-η₃) η₃, ∀ x ∈ V, s < φ x → a₂ s x = 0) ∧
      (∀ s ∈ Ioo (-η₃) η₃, ∀ x ∈ V,
        2 * -coform g x (d φ x) (d (w s) x) + w s x * box g φ x = (φ x - s) * b₂ s x) := by
  set ρ : E n → ℝ := fun x => √|(g x).det| with hρ_def
  have hρ : ContDiff ℝ ∞ ρ := contDiff_sqrt_abs_det hg.smooth hg.det_ne_zero
  have hφO : ContDiffOn ℝ ∞ φ O := hφ.smooth.mono hOU
  have heik : ∀ x ∈ O, coform g x (d φ x) (d φ x) = 0 := fun x hx => hφ.eikonal x (hOU hx)
  have hdφ : ∀ x ∈ O, d φ x ≠ 0 := fun x hx => hφ.d_ne_zero x (hOU hx)
  have hsη : ∀ s ∈ Ioo (-η₂) η₂, s ∈ Ioo (-η) η := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hnull : ∀ s, ∀ᵐ x, x ∉ O ∩ φ ⁻¹' {s} := fun s =>
    measure_eq_zero_iff_ae_notMem.1 (volume_inter_level_eq_zero hO (hφO.of_le (by simp))
      (fun x hx => hφ.fderiv_ne_zero (hOU hx)) s)
  set Kc := causalFutureSet g Y (closedBall q₀ r₀) ∩ {x | ψ x ≤ c₂}
  obtain ⟨ζ, hζ, -, hζc, hζO, hζ1⟩ := exists_cutoff hKcc hO hKc
  set R := amplitudeRemainder g φ B
  have hR : ContDiffOn ℝ ∞ (fun q : E n × ℝ => R q.1 q.2) (O ×ˢ univ) :=
    contDiffOn_amplitudeRemainder hg.smooth hg.det_ne_zero hO hB.smooth hφO
  have hRp : ContDiffOn ℝ ∞ (fun q : E n × ℝ => if 0 < q.2 then R q.1 q.2 else 0)
      (O ×ˢ univ) := contDiffOn_ite_pos_of_flat hR hO hB.flat
  set f := remainderSource φ ζ R
  have hf : ContDiff ℝ ∞ (fun p : ℝ × E n => f p.1 p.2) := by
    simp only [f, remainderSource_def]
    exact contDiff_mul_param (f := fun s x => if 0 < φ x - s then R x (φ x - s) else 0) hO hζ hζO
      (contDiffOn_comp_sub (B := fun x r => if 0 < r then R x r else 0) hφO hRp)
  have hfs : ∀ s, ContDiff ℝ ∞ (f s) := fun s => hf.comp (contDiff_const.prodMk contDiff_id)
  have hfc : ∀ s, HasCompactSupport (f s) := fun s =>
    HasCompactSupport.intro hζc fun x hx =>
      notMem_support.1 fun h => hx (support_remainderSource_subset s h)
  set v : ℝ → E n → ℝ := fun s => advanced g Y (f s)
  have hv : ContDiff ℝ ∞ (fun p : ℝ × E n => v p.1 p.2) :=
    contDiff_advanced_param hg hf hζc fun s => support_remainderSource_subset s
  have hvs : ∀ s, ContDiff ℝ ∞ (v s) := fun _ => contDiff_advanced
  have hboxv : ∀ s x, box g (v s) x = f s x := fun s x => box_advanced hg (hfs s) (hfc s) x
  set ut : ℝ → E n → ℝ := fun s y => B y (φ y - s)
  have hut : ContDiffOn ℝ ∞ (fun p : ℝ × E n => ut p.1 p.2) (univ ×ˢ O) :=
    contDiffOn_comp_sub hφO hB.smooth
  have huts : ∀ s, ContDiffOn ℝ ∞ (ut s) O := fun s =>
    hut.comp (contDiff_const.prodMk contDiff_id).contDiffOn fun _ hx => ⟨mem_univ _, hx⟩
  have hboxut : ∀ s, ∀ x ∈ O, box g (ut s) x = R x (φ x - s) := fun s x hx =>
    box_comp_sub_eq hg.smooth hg.symm hg.det_ne_zero hO hB.smooth hφO heik s hx
  have htrut : ∀ s, ∀ x ∈ O, φ x = s →
      2 * -coform g x (d φ x) (d (ut s) x) + ut s x * box g φ x = 0 := by
    intro s x hx hxs
    have hc := coform_d_comp_sub hO hB.smooth hφO heik s hx
    simp only [ut]
    rw [hc, hxs, sub_self]
    exact hB.transport x hx
  have hftop : ∀ s ∈ Ioo (-η₂) η₂, ∀ x, ℓ < ψ x → f s x = 0 := by
    intro s hs x hx
    by_cases hxO : x ∈ O
    · have hxA : x ∈ U ∩ A ψ τ := ⟨hOU hxO, mem_A.2 (hℓ.trans hx)⟩
      have hR0 : R x (φ x - s) = (φ x - s) * a s x := by
        rw [← hboxut s x hxO, box_congr (hB.top s hs x hxO hx), hbox s (hsη s hs) x hxA]
      simp only [f, remainderSource_def]
      split_ifs with h
      · rw [hR0, ha0 s (hsη s hs) x hxA (by linarith), mul_zero, mul_zero]
      · rw [mul_zero]
    · simp [f, remainderSource_def, image_eq_zero_of_notMem_tsupport fun h => hxO (hζO h)]
  have hvtop : ∀ s ∈ Ioo (-η₂) η₂, ∀ y, ℓ < ψ y → v s y = 0 := by
    intro s hs y hy
    by_contra hv0
    obtain ⟨p, hp, hyp⟩ := mem_causalPastSet.1 (support_advanced_subset hv0)
    have hts : tsupport (f s) ⊆ {x | ψ x ≤ ℓ} :=
      closure_minimal (fun x hx => by
        by_contra h
        exact hx (hftop s hs x (not_le.1 h))) (isClosed_le hψ.smooth.continuous continuous_const)
    exact absurd ((hψ.le_of_causalLE hg (mem_causalPast.1 hyp)).trans (hts hp)) (not_le.2 hy)
  set V := ball q₀ r₀ ∩ {x | ψ x < c₁}
  have hVo : IsOpen V := isOpen_ball.inter (isOpen_lt hψ.smooth.continuous continuous_const)
  have hq₀V : q₀ ∈ V := ⟨mem_ball_self hr₀, by
    simp only [mem_ofPred_eq]
    linarith⟩
  have hVKc : V ⊆ Kc := fun x hx =>
    ⟨subset_causalFutureSet _ (ball_subset_closedBall hx.1), (le_of_lt hx.2).trans hc₂.le⟩
  have hVO : V ⊆ O := hVKc.trans hKc
  have hζV : ∀ x ∈ V, ζ =ᶠ[𝓝 x] 1 := fun x hx => hζ1 x (hVKc hx)
  have hint : ∀ s, ∀ q : E n → ℝ, ContDiff ℝ ∞ q → HasCompactSupport q → tsupport q ⊆ O →
      Integrable fun x => ({x | s < φ x}.indicator (ut s) x - v s x) * q x * ρ x := by
    intro s q hq hqc hqO
    have h1 := integrable_indicator_mul hO hφO.continuousOn (huts s) hq hqc hqO s hρ.continuous
    have h2 : Integrable fun x => v s x * q x * ρ x :=
      integrable_of_eq_zero_off (((hvs s).continuous.mul hq.continuous).mul hρ.continuous) hqc
        fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx]
    refine (h1.sub h2).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    ring
  have hmain : ∀ s ∈ Ioo (-η₂) η₂, AgreesOn g (retardedS g Y (F s))
      (fun x => {x | s < φ x}.indicator (ut s) x - v s x) V := by
    intro s hs
    refine agreesOn_iff.2 fun h hh hhc hhV => ?_
    have hs' := hsη s hs
    set χ := retarded g Y h
    set κ : ℝ → ℝ := fun t => Real.smoothTransition ((c₂ - t) / (c₂ - c₁))
    have hκ : ContDiff ℝ ∞ κ :=
      Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const _)
    have hκ1 : ∀ t, t ≤ c₁ → κ t = 1 := fun t ht =>
      Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ (by linarith)]; linarith)
    have hκ0 : ∀ t, c₂ ≤ t → κ t = 0 := fun t ht =>
      Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith)
        (by linarith))
    set P : E n → ℝ := fun x => κ (ψ x) * χ x
    have hP : ContDiff ℝ ∞ P := (hκ.comp hψ.smooth).mul contDiff_retarded
    set S := causalFutureSet g Y (tsupport h)
    have hSc : IsClosed S := isClosed_causalFutureSet hg hhc
    have hhS : tsupport h ⊆ S := subset_causalFutureSet _
    have hSKc : S ∩ {x | ψ x ≤ c₂} ⊆ Kc := fun x hx =>
      ⟨causalFutureSet_mono (hhV.trans fun y hy => ball_subset_closedBall hy.1) hx.1, hx.2⟩
    have hPsupp : tsupport P ⊆ S ∩ {x | ψ x ≤ c₂} := by
      refine closure_minimal (fun x hx => ⟨?_, ?_⟩)
        (hSc.inter (isClosed_le hψ.smooth.continuous continuous_const))
      · exact support_retarded_subset (right_ne_zero_of_mul hx)
      · by_contra hlt
        exact hx (by simp [P, hκ0 _ (le_of_lt (not_le.1 hlt))])
    have hPKc : tsupport P ⊆ Kc := hPsupp.trans hSKc
    have hPc : HasCompactSupport P := hKcc.of_isClosed_subset (isClosed_tsupport _) hPKc
    have hPO : tsupport P ⊆ O := hPKc.trans hKc
    set E' : E n → ℝ := fun x => box g P x - h x
    have hE' : ContDiff ℝ ∞ E' := (contDiff_box hg.smooth hg.det_ne_zero hP).sub hh
    have hE'c : HasCompactSupport E' := (hasCompactSupport_box (g := g) hPc).sub hhc
    have hE'1 : ∀ x, ψ x < c₁ → E' x = 0 := by
      intro x hx
      have hev : P =ᶠ[𝓝 x] χ := by
        filter_upwards [(hψ.smooth.continuous.isOpen_preimage _ isOpen_Iio).mem_nhds
          (show x ∈ ψ ⁻¹' Iio c₁ from hx)] with y hy
        simp [P, hκ1 _ (le_of_lt hy)]
      simp only [E']
      rw [box_congr hev, box_retarded hg hh hhc, sub_self]
    have hE'2 : ∀ x, x ∉ S → E' x = 0 := by
      intro x hx
      have hev : P =ᶠ[𝓝 x] 0 := by
        filter_upwards [retarded_eventuallyEq_zero hx] with y hy
        simp [P, χ, hy]
      simp only [E']
      rw [box_eq_zero_of_eventuallyEq hev,
        image_eq_zero_of_notMem_tsupport fun h' => hx (hhS h'), sub_self]
    have hE'3 : ∀ x, c₂ < ψ x → E' x = 0 := by
      intro x hx
      have hev : P =ᶠ[𝓝 x] 0 := by
        filter_upwards [(hψ.smooth.continuous.isOpen_preimage _ isOpen_Ioi).mem_nhds
          (show x ∈ ψ ⁻¹' Ioi c₂ from hx)] with y hy
        simp [P, hκ0 _ (le_of_lt hy)]
      have hxh : x ∉ tsupport h := fun h' => by
        have := (hhV h').2
        simp only [mem_ofPred_eq] at this
        linarith
      simp only [E']
      rw [box_eq_zero_of_eventuallyEq hev, image_eq_zero_of_notMem_tsupport hxh, sub_self]
    have hE'Top : tsupport E' ⊆ (O ∩ {x | ℓ < ψ x}) ∩ Kc := by
      have hsub : tsupport E' ⊆ S ∩ ({x | c₁ ≤ ψ x} ∩ {x | ψ x ≤ c₂}) := by
        refine closure_minimal (fun x hx => ?_) (hSc.inter
          ((isClosed_le continuous_const hψ.smooth.continuous).inter
            (isClosed_le hψ.smooth.continuous continuous_const)))
        exact ⟨by_contra fun h' => hx (hE'2 x h'),
          by_contra fun h' => hx (hE'1 x (not_le.1 h')),
          by_contra fun h' => hx (hE'3 x (not_le.1 h'))⟩
      intro x hx
      obtain ⟨hxS, hx1, hx2⟩ := hsub hx
      have hxKc : x ∈ Kc := hSKc ⟨hxS, hx2⟩
      have hx1' : c₁ ≤ ψ x := hx1
      exact ⟨⟨hKc hxKc, show ℓ < ψ x by linarith⟩, hxKc⟩
    have hFP : F s P = 0 := by
      refine (hF s hs').eq_zero P hP ?_
      have hKP : K s ⊆ (tsupport P)ᶜ := fun y hy hyP =>
        Set.disjoint_left.1 (hKU s hs') (hOU (hPO hyP)) hy
      filter_upwards [(isClosed_tsupport P).isOpen_compl.mem_nhdsSet.2 hKP] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    have hsum : retardedS g Y (F s) (box g P) =
        retardedS g Y (F s) h + retardedS g Y (F s) E' := by
      rw [← (hF s hs').retardedS_map_add hg hh hhc hE' hE'c]
      congr 1
      funext x
      simp [E']
    have h1 : retardedS g Y (F s) (box g P) = 0 := by
      simp only [retardedS_def]
      rw [advanced_box hg hP hPc, hFP]
    have h3 : retardedS g Y (F s) E' =
        ∫ x, ({x | s < φ x}.indicator (ut s) x - v s x) * E' x * ρ x := by
      rw [agreesOn_iff.1 (hagree s hs') E' hE' hE'c fun x hx =>
        ⟨hOU (hE'Top hx).1.1, mem_A.2 (hℓ.trans (hE'Top hx).1.2)⟩]
      refine integral_congr_ae ?_
      filter_upwards [hnull s] with x hx
      by_cases hxE : x ∈ tsupport E'
      · obtain ⟨⟨hxO, hxℓ⟩, -⟩ := hE'Top hxE
        have hut_eq : ut s x = u s x := (hB.top s hs x hxO hxℓ).eq_of_nhds
        have hφs : φ x ≠ s := fun h' => hx ⟨hxO, h'⟩
        rw [hvtop s hs x hxℓ, sub_zero]
        rcases lt_or_gt_of_ne hφs with hlt | hgt
        · simp [not_le.2 hlt, not_lt.2 hlt.le]
        · simp [hgt.le, hgt, hut_eq, hρ_def]
      · simp [image_eq_zero_of_notMem_tsupport hxE]
    have hjump := integral_indicator_mul_box_eq hg.smooth hg.symm hg.det_ne_zero hO (huts s)
      hφO hP hPc hPO heik hdφ (s := s) fun x hx hxs => htrut s x (hPO hx) hxs
    have hJ2 : ∫ x, {x | s < φ x}.indicator (box g (ut s)) x * P x * ρ x =
        ∫ x, f s x * P x * ρ x := by
      congr 1
      funext x
      by_cases hxP : x ∈ tsupport P
      · have hxO := hPO hxP
        have hζx : ζ x = 1 := (hζ1 x (hPKc hxP)).eq_of_nhds
        simp only [f, remainderSource_def, hζx, one_mul, indicator_apply, mem_ofPred_eq, sub_pos]
        split_ifs <;> simp [hboxut s x hxO]
      · simp [image_eq_zero_of_notMem_tsupport hxP]
    have hgreen : ∫ x, v s x * box g P x * ρ x = ∫ x, f s x * P x * ρ x := by
      rw [integral_mul_box_comm_of_isCompact hg.smooth hg.symm hg.det_ne_zero (hvs s) hP
        (hPc.isCompact.of_isClosed_subset ((isClosed_tsupport _).inter (isClosed_tsupport _))
          inter_subset_right)]
      congr 1
      funext x
      rw [hboxv]
      ring
    have h4 : ∫ x, ({x | s < φ x}.indicator (ut s) x - v s x) * box g P x * ρ x = 0 := by
      have hi1 := integrable_indicator_mul hO hφO.continuousOn (huts s)
        (contDiff_box hg.smooth hg.det_ne_zero hP) (hasCompactSupport_box (g := g) hPc)
        ((tsupport_box_subset P).trans hPO) s hρ.continuous
      have hi2 : Integrable fun x => v s x * box g P x * ρ x :=
        integrable_of_eq_zero_off (((hvs s).continuous.mul
          (continuous_box hg.smooth hg.det_ne_zero hP)).mul hρ.continuous)
          (hasCompactSupport_box (g := g) hPc) fun x hx => by
            simp [image_eq_zero_of_notMem_tsupport hx]
      calc ∫ x, ({x | s < φ x}.indicator (ut s) x - v s x) * box g P x * ρ x =
            (∫ x, {x | s < φ x}.indicator (ut s) x * box g P x * ρ x) -
              ∫ x, v s x * box g P x * ρ x := by
            rw [← integral_sub hi1 hi2]
            congr 1
            funext x
            ring
        _ = 0 := by rw [hjump, hJ2, hgreen, sub_self]
    have hiP := hint s (box g P) (contDiff_box hg.smooth hg.det_ne_zero hP)
      (hasCompactSupport_box (g := g) hPc) ((tsupport_box_subset P).trans hPO)
    have hih := hint s h hh hhc (hhV.trans hVO)
    have hrel : (fun x => ({x | s < φ x}.indicator (ut s) x - v s x) * E' x * ρ x) =
        fun x => ({x | s < φ x}.indicator (ut s) x - v s x) * box g P x * ρ x -
          ({x | s < φ x}.indicator (ut s) x - v s x) * h x * ρ x := by
      funext x
      simp only [E']
      ring
    have hUh : retardedS g Y (F s) h = -retardedS g Y (F s) E' := by linarith
    rw [hUh, h3, hrel, integral_sub hiP hih, h4]
    ring
  have hvlt : ∀ s ∈ Ioo (-η₂) η₂, ∀ x ∈ V, φ x < s → v s x = 0 := by
    intro s hs x hx hxs
    have hW : IsOpen (V ∩ φ ⁻¹' Iio s) :=
      (hφO.continuousOn.mono hVO).isOpen_inter_preimage hVo isOpen_Iio
    have h1 : AgreesOn g (retardedS g Y (F s)) (fun y => -v s y) (V ∩ φ ⁻¹' Iio s) :=
      ((hmain s hs).mono inter_subset_left).congr fun y hy => by
        simp [not_lt.2 (le_of_lt (show φ y < s from hy.2))]
    have h2 : AgreesOn g (retardedS g Y (F s)) 0 (V ∩ φ ⁻¹' Iio s) :=
      vanishesOn_iff_agreesOn_zero.1 ((hvan s (hsη s hs)).mono fun y hy =>
        ⟨hOU (hVO hy.1), hy.2⟩)
    have := AgreesOn.eqOn_of_continuousOn hg.smooth hg.det_ne_zero hW
      (hvs s).continuous.neg.continuousOn continuousOn_const h1 h2 x ⟨hx, hxs⟩
    have h3 : -v s x = 0 := this
    exact neg_eq_zero.1 h3
  have hveq : ∀ s ∈ Ioo (-η₂) η₂, ∀ x ∈ V, φ x = s →
      v s x = 0 ∧ fderiv ℝ (v s) x = 0 := by
    intro s hs x hx hxs
    have hxO := hVO hx
    have hcl : x ∈ closure (V ∩ {y | φ y < φ x}) :=
      mem_closure_lt_of_fderiv_ne_zero (hVo.mem_nhds hx)
        ((hφO.contDiffAt (hO.mem_nhds hxO)).differentiableAt (by simp))
        (hφ.fderiv_ne_zero (hOU hxO))
    rw [hxs] at hcl
    have hW : IsOpen (V ∩ {y | φ y < s}) :=
      (hφO.continuousOn.mono hVO).isOpen_inter_preimage hVo isOpen_Iio
    have h0 : ∀ y ∈ V ∩ {y | φ y < s}, v s y = 0 := fun y hy => hvlt s hs y hy.1 hy.2
    exact ⟨(isClosed_eq (hvs s).continuous continuous_const).closure_subset_iff.2 h0 hcl,
      (isClosed_eq ((hvs s).continuous_fderiv (by simp)) continuous_const).closure_subset_iff.2
        (fun y hy => fderiv_eq_zero_of_isOpen hW h0 hy) hcl⟩
  set w : ℝ → E n → ℝ := fun s x => ζ x * ut s x - v s x
  have hw : ContDiff ℝ ∞ (fun p : ℝ × E n => w p.1 p.2) :=
    (contDiff_mul_param hO hζ hζO hut).sub hv
  have hwloc : ∀ s, ∀ x ∈ V, w s =ᶠ[𝓝 x] fun y => ut s y - v s y := fun s x hx => by
    filter_upwards [hζV x hx] with y hy
    simp [w, hy]
  have hwval : ∀ s, ∀ x ∈ V, w s x = ut s x - v s x := fun s x hx => (hwloc s x hx).eq_of_nhds
  have hagreeV : ∀ s ∈ Ioo (-η₂) η₂,
      AgreesOn g (retardedS g Y (F s)) ({x | s ≤ φ x}.indicator (w s)) V := by
    intro s hs
    refine (hmain s hs).congr_ae ?_
    filter_upwards [hnull s] with x hx hxV
    have hφs : φ x ≠ s := fun h' => hx ⟨hVO hxV, h'⟩
    rcases lt_or_gt_of_ne hφs with hlt | hgt
    · simp [not_lt.2 hlt.le, not_le.2 hlt, hvlt s hs x hxV hlt]
    · simp [hgt, hgt.le, hwval s x hxV]
  obtain ⟨η₃, hη₃def⟩ : ∃ η₃ : ℝ, η₃ = η₂ / 2 := ⟨_, rfl⟩
  have hη₃ : 0 < η₃ := by rw [hη₃def]; positivity
  have hsη₃ : ∀ s ∈ Ioo (-η₃) η₃, s ∈ Ioo (-η₂) η₂ := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hη₃η : η₃ ≤ η := by linarith
  have hRs : ContDiffOn ℝ ∞ (fun p : ℝ × E n =>
      R p.2 (φ p.2 - p.1) - if 0 < φ p.2 - p.1 then R p.2 (φ p.2 - p.1) else 0) (univ ×ˢ V) :=
    ((contDiffOn_comp_sub hφO hR).sub (contDiffOn_comp_sub
      (B := fun x r => if 0 < r then R x r else 0) hφO hRp)).mono (prod_mono subset_rfl hVO)
  obtain ⟨a₂, ha₂, hfa⟩ := exists_eq_sub_mul_of_eq_zero hVo (hφO.mono hVO)
    (f := fun s x => R x (φ x - s) - if 0 < φ x - s then R x (φ x - s) else 0) hRs
    fun x hx => by
      have h0 := hB.flat 0 x (hVO hx)
      simp only [iteratedDeriv_zero] at h0
      simp only [sub_self, lt_irrefl, ite_false, sub_zero]
      exact h0
  have hboxw : ∀ s, ∀ x ∈ V,
      box g (w s) x = R x (φ x - s) - if 0 < φ x - s then R x (φ x - s) else 0 := by
    intro s x hx
    have hxO := hVO hx
    rw [box_congr (hwloc s x hx), box_sub_of_contDiffOn hg.smooth hg.det_ne_zero hO (huts s)
      (hvs s).contDiffOn hxO, hboxut s x hxO, hboxv]
    simp [f, remainderSource_def, (hζV x hx).eq_of_nhds]
  have hcoef : ContDiffOn ℝ ∞ (fun p : ℝ × E n =>
      2 * -coform g p.2 (d φ p.2) (d (w p.1) p.2) + w p.1 p.2 * box g φ p.2) (univ ×ˢ V) := by
    have hsnd : MapsTo (fun p : ℝ × E n => p.2) (univ ×ˢ V) U := fun p hp => hOU (hVO hp.2)
    have hdφ' : ∀ j, ContDiffOn ℝ ∞ (fun p : ℝ × E n => d φ p.2 j) (univ ×ˢ V) := fun j =>
      (contDiffOn_d hφ.isOpen hφ.smooth j).comp contDiff_snd.contDiffOn hsnd
    have hbφ : ContDiffOn ℝ ∞ (fun p : ℝ × E n => box g φ p.2) (univ ×ˢ V) :=
      (contDiffOn_box hg.smooth hg.det_ne_zero hφ.isOpen hφ.smooth).comp
        contDiff_snd.contDiffOn hsnd
    simp only [coform_def]
    refine (contDiffOn_const.mul (ContDiffOn.neg (ContDiffOn.sum fun j _ =>
      ContDiffOn.sum fun k _ => ?_))).add (hw.contDiffOn.mul hbφ)
    exact ((((contDiff_inv_apply hg.smooth hg.det_ne_zero j k).comp contDiff_snd).contDiffOn.mul
      (hdφ' j)).mul (contDiff_d_param hw k).contDiffOn)
  obtain ⟨β, hβ, hβ1, hβ0⟩ : ∃ β : ℝ → ℝ, ContDiff ℝ ∞ β ∧ (∀ s ∈ Ioo (-η₃) η₃, β s = 1) ∧
      ∀ s, η₂ ≤ |s| → β s = 0 := by
    let bump : ContDiffBump (0 : ℝ) := ⟨η₂ / 2, 3 * η₂ / 4, by positivity, by linarith⟩
    refine ⟨bump, bump.contDiff, fun s hs => bump.one_of_mem_closedBall ?_, fun s hs => ?_⟩
    · rw [mem_closedBall, Real.dist_eq, sub_zero, abs_le]
      show -(η₂ / 2) ≤ s ∧ s ≤ η₂ / 2
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    · refine bump.zero_of_le_dist ?_
      rw [Real.dist_eq, sub_zero]
      show 3 * η₂ / 4 ≤ |s|
      linarith
  obtain ⟨b₂, hb₂, hfb⟩ := exists_eq_sub_mul_of_eq_zero hVo (hφO.mono hVO)
    (f := fun s x => β s * (2 * -coform g x (d φ x) (d (w s) x) + w s x * box g φ x))
    ((hβ.comp contDiff_fst).contDiffOn.mul hcoef) fun x hx => by
      by_cases hφx : |φ x| < η₂
      · have hs : φ x ∈ Ioo (-η₂) η₂ := ⟨by linarith [neg_abs_le (φ x)],
          by linarith [le_abs_self (φ x)]⟩
        obtain ⟨hv0, hdv0⟩ := hveq (φ x) hs x hx rfl
        have hxO := hVO hx
        have hdiff : DifferentiableAt ℝ (ut (φ x)) x :=
          ((huts (φ x)).contDiffAt (hO.mem_nhds hxO)).differentiableAt (by simp)
        have hd : d (w (φ x)) x = d (ut (φ x)) x := by
          funext j
          rw [d_congr (hwloc _ x hx), d_sub hdiff ((hvs _).differentiable (by simp) x)]
          simp [d_def, hdv0]
        rw [hd, hwval _ x hx, hv0, sub_zero, htrut (φ x) x hxO rfl, mul_zero]
      · rw [hβ0 _ (not_lt.1 hφx), zero_mul]
  refine ⟨V, η₃, w, a₂, b₂, hVo, hq₀V, hVO.trans hOU, hη₃, hη₃η,
    hw.contDiffOn, fun s hs => hagreeV s (hsη₃ s hs), ?_, ?_,
    ha₂.mono (prod_mono (subset_univ _) subset_rfl),
    hb₂.mono (prod_mono (subset_univ _) subset_rfl),
    fun s _ x hx => by rw [hboxw s x hx, hfa s x hx], ?_, ?_⟩
  · intro s hs x hx hxs
    have hs₂ := hsη₃ s hs
    have hs' := hsη s hs₂
    have hus : ContinuousOn (u s) U :=
      (hu.comp (contDiff_const.prodMk contDiff_id).contDiffOn fun y hy => ⟨hs', hy⟩).continuousOn
    have hVA : IsOpen (V ∩ A ψ τ) := hVo.inter (isOpen_A hψ.smooth.continuous τ)
    have hW : IsOpen ((V ∩ A ψ τ) ∩ φ ⁻¹' Ioi s) :=
      (hφO.continuousOn.mono fun y hy => hVO hy.1).isOpen_inter_preimage hVA isOpen_Ioi
    have h1 : AgreesOn g (retardedS g Y (F s)) (w s) ((V ∩ A ψ τ) ∩ φ ⁻¹' Ioi s) :=
      ((hagreeV s hs₂).mono fun y hy => hy.1.1).congr fun y hy =>
        indicator_of_mem (show y ∈ {x | s ≤ φ x} from (le_of_lt (show s < φ y from hy.2) : s ≤ φ y)) (w s)
    have h2 : AgreesOn g (retardedS g Y (F s)) (u s) ((V ∩ A ψ τ) ∩ φ ⁻¹' Ioi s) :=
      ((hagree s hs').mono fun y hy => ⟨hOU (hVO hy.1.1), hy.1.2⟩).congr fun y hy =>
        indicator_of_mem (show y ∈ {x | s ≤ φ x} from (le_of_lt (show s < φ y from hy.2) : s ≤ φ y)) (u s)
    have heq := AgreesOn.eqOn_of_continuousOn hg.smooth hg.det_ne_zero hW
      ((hw.comp (contDiff_const.prodMk contDiff_id)).continuous.continuousOn)
      (hus.mono fun y hy => hOU (hVO hy.1.1)) h1 h2
    rcases hxs.lt_or_eq with hlt | heqs
    · exact heq x ⟨hx, hlt⟩
    · have hxO := hVO hx.1
      have hcl : x ∈ closure ((V ∩ A ψ τ) ∩ {y | (-φ) y < (-φ) x}) :=
        mem_closure_lt_of_fderiv_ne_zero (hVA.mem_nhds hx)
          ((hφO.contDiffAt (hO.mem_nhds hxO)).differentiableAt (by simp)).neg
          (by
            rw [fderiv_neg]
            exact neg_ne_zero.2 (hφ.fderiv_ne_zero (hOU hxO)))
      have hcont : ContinuousAt (fun y => w s y - u s y) x :=
        (hw.comp (contDiff_const.prodMk contDiff_id)).continuous.continuousAt.sub
          (hus.continuousAt (hφ.isOpen.mem_nhds (hOU hxO)))
      by_contra hne
      have hne' : w s x - u s x ≠ 0 := sub_ne_zero.2 hne
      obtain ⟨y, hy, hyW⟩ := mem_closure_iff_nhds.1 hcl _ (hcont.eventually_ne hne')
      refine hy (sub_eq_zero.2 (heq y ⟨hyW.1, ?_⟩))
      have : -φ y < -φ x := hyW.2
      show s < φ y
      linarith
  · intro s hs x hx hxs
    have hs₂ := hsη₃ s hs
    rw [hwval s x hx, (hveq s hs₂ x hx hxs).1, sub_zero]
    simp only [ut, hxs, sub_self]
    exact hB.pos x (hVO hx) (by rw [hxs]; exact abs_lt.2 ⟨hs₂.1, hs₂.2⟩)
  · intro s hs x hx hxs
    have h1 := hfa s x hx
    simp only [sub_pos.2 hxs, ite_true, sub_self] at h1
    exact (mul_eq_zero.1 h1.symm).resolve_left (sub_ne_zero.2 (ne_of_gt hxs))
  · intro s hs x hx
    have h1 := hfb s x hx
    rw [hβ1 s hs, one_mul] at h1
    exact h1

/-- **The amplitude** (`lem_ind_frontier_wave`): the amplitude across the frontier
(`exists_isFrontierAmplitude`) and the duality argument (`exists_wave_of_isFrontierAmplitude`)
on a small lens above `q₀`. -/
theorem exists_wave_of_frontier (hg : IsSpacetime g Y) (hψ : IsCauchyTemporal g Y ψ)
    {τ : ℝ} {q₀ : E n} (hq₀ : ψ q₀ = τ) {U : Set (E n)} {φ : E n → ℝ}
    (hφ : IsFutureEikonal g Y φ U) (hq₀U : q₀ ∈ U) {η : ℝ} (hη : 0 < η)
    {F : ℝ → (E n → ℝ) → ℝ} {K : ℝ → Set (E n)}
    (hF : ∀ s ∈ Ioo (-η) η, IsSource (F s) (K s))
    (hKU : ∀ s ∈ Ioo (-η) η, Disjoint U (K s))
    {u a b : ℝ → E n → ℝ}
    (hu : ContDiffOn ℝ ∞ (fun p : ℝ × E n => u p.1 p.2) (Ioo (-η) η ×ˢ U))
    (hbox : ∀ s ∈ Ioo (-η) η, ∀ x ∈ U ∩ A ψ τ, box g (u s) x = (φ x - s) * a s x)
    (ha0 : ∀ s ∈ Ioo (-η) η, ∀ x ∈ U ∩ A ψ τ, s < φ x → a s x = 0)
    (htr : ∀ s ∈ Ioo (-η) η, ∀ x ∈ U ∩ A ψ τ,
      2 * -coform g x (d φ x) (d (u s) x) + u s x * box g φ x = (φ x - s) * b s x)
    (hpos : ∀ s ∈ Ioo (-η) η, ∀ x ∈ U ∩ A ψ τ, φ x = s → 0 < u s x)
    (hagree : ∀ s ∈ Ioo (-η) η,
      AgreesOn g (retardedS g Y (F s)) ({x | s ≤ φ x}.indicator (u s)) (U ∩ A ψ τ))
    (hvan : ∀ s ∈ Ioo (-η) η, VanishesOn (retardedS g Y (F s)) (U ∩ {x | φ x < s})) :
    ∃ (V : Set (E n)) (η₂ : ℝ) (w a₂ b₂ : ℝ → E n → ℝ), IsOpen V ∧ q₀ ∈ V ∧ V ⊆ U ∧
      0 < η₂ ∧ η₂ ≤ η ∧
      ContDiffOn ℝ ∞ (fun p : ℝ × E n => w p.1 p.2) (Ioo (-η₂) η₂ ×ˢ V) ∧
      (∀ s ∈ Ioo (-η₂) η₂,
        AgreesOn g (retardedS g Y (F s)) ({x | s ≤ φ x}.indicator (w s)) V) ∧
      (∀ s ∈ Ioo (-η₂) η₂, ∀ x ∈ V ∩ A ψ τ, s ≤ φ x → w s x = u s x) ∧
      (∀ s ∈ Ioo (-η₂) η₂, ∀ x ∈ V, φ x = s → 0 < w s x) ∧
      ContDiffOn ℝ ∞ (fun p : ℝ × E n => a₂ p.1 p.2) (Ioo (-η₂) η₂ ×ˢ V) ∧
      ContDiffOn ℝ ∞ (fun p : ℝ × E n => b₂ p.1 p.2) (Ioo (-η₂) η₂ ×ˢ V) ∧
      (∀ s ∈ Ioo (-η₂) η₂, ∀ x ∈ V, box g (w s) x = (φ x - s) * a₂ s x) ∧
      (∀ s ∈ Ioo (-η₂) η₂, ∀ x ∈ V, s < φ x → a₂ s x = 0) ∧
      (∀ s ∈ Ioo (-η₂) η₂, ∀ x ∈ V,
        2 * -coform g x (d φ x) (d (w s) x) + w s x * box g φ x = (φ x - s) * b₂ s x) := by
  obtain ⟨O, η₂, hO, hq₀O, hOU, hη₂, hη₂η, hBex⟩ :=
    exists_isFrontierAmplitude hg hψ hq₀ hφ hq₀U hη hu hbox ha0 htr hpos
  obtain ⟨r₀, hr₀, c, hc, hKc, hKcc⟩ :=
    hψ.exists_causalFutureSet_inter_le_subset hg (hO.mem_nhds hq₀O)
  rw [hq₀] at hc
  obtain ⟨B, hB⟩ := hBex (τ + (c - τ) / 4) (by linarith)
  exact exists_wave_of_isFrontierAmplitude hg hψ hq₀ hφ hF hKU hu hbox ha0 hagree hvan hO hOU
    hη₂ hη₂η (by linarith) (show τ + (c - τ) / 4 < τ + (c - τ) / 2 by linarith)
    (show τ + (c - τ) / 2 < c by linarith) hr₀ hKc hKcc hB

end

end LorentzianCalderon
