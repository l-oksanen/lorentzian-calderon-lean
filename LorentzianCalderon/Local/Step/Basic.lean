module

public import LorentzianCalderon.Local.Step.Hyp
public import LorentzianCalderon.Local.MatrixCalculus
public import LorentzianCalderon.Induction.Propagation
public import LorentzianCalderon.Waves.Calculus

public section

/-!
# The local continuation step: basic objects

The conformal factor `κ = (n + 1)⁻¹ g'_{αβ}(Ψ) g(dΨ^α, dΨ^β)`, the comparison coefficients
`ḡ`, `θ̄` of `Comparison.lean` for this `κ`, and the differences `φ̄_a = φ_a - φ'_a ∘ Ψ`,
`w̄_{a,s} = u_{a,s} - u'_{a,s} ∘ Ψ`; smoothness of these, and calculus for functions smooth in
`(s, x)`.
-/

namespace LorentzianCalderon

noncomputable section
open Set Matrix Filter
open scoped ContDiff Topology

variable {n : ℕ} {ι : Type*}

section Calculus

theorem contDiffOn_d2_of_isOpen {V : Set (E n)} (hV : IsOpen V) {u : E n → ℝ}
    (hu : ContDiffOn ℝ ∞ u V) (i j : Fin (n + 1)) : ContDiffOn ℝ ∞ (fun y => d2 u y i j) V :=
  by simpa only [d2_def] using contDiffOn_d hV (contDiffOn_d hV hu j) i

theorem contDiffOn_coord {V : Set (E n)} {Ψ : E n → E n} (hΨ : ContDiffOn ℝ ∞ Ψ V)
    (α : Fin (n + 1)) : ContDiffOn ℝ ∞ (fun y => Ψ y α) V :=
  contDiffOn_euclidean.mp hΨ α

/-- Partial derivatives in `x` of a function smooth in `(s, x)` are smooth in `(s, x)`. -/
theorem contDiffOn_param_d {W : Set (ℝ × E n)} (hW : IsOpen W) {U : ℝ → E n → ℝ}
    (hU : ContDiffOn ℝ ∞ (fun p : ℝ × E n => U p.1 p.2) W) (k : Fin (n + 1)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E n => d (U p.1) p.2 k) W := by
  have h1 : ContDiffOn ℝ ∞ (fun p : ℝ × E n =>
      fderiv ℝ (fun p : ℝ × E n => U p.1 p.2) p (0, EuclideanSpace.single k 1)) W :=
    (hU.fderiv_of_isOpen hW (by simp)).clm_apply contDiffOn_const
  refine h1.congr fun p hp => ?_
  exact d_param_eq ((hU.contDiffAt (hW.mem_nhds hp)).differentiableAt (by simp)) k

theorem contDiffOn_param_d2 {W : Set (ℝ × E n)} (hW : IsOpen W) {U : ℝ → E n → ℝ}
    (hU : ContDiffOn ℝ ∞ (fun p : ℝ × E n => U p.1 p.2) W) (i j : Fin (n + 1)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E n => d2 (U p.1) p.2 i j) W := by
  simpa only [d2_def] using contDiffOn_param_d (U := fun s z => d (U s) z j) hW
    (contDiffOn_param_d hW hU j) i

theorem contDiffOn_slice {J : Set ℝ} {V : Set (E n)} {U : ℝ → E n → ℝ}
    (hU : ContDiffOn ℝ ∞ (fun p : ℝ × E n => U p.1 p.2) (J ×ˢ V)) {s : ℝ} (hs : s ∈ J) :
    ContDiffOn ℝ ∞ (U s) V :=
  hU.comp (contDiffOn_const.prodMk contDiffOn_id) fun _ hx => ⟨hs, hx⟩

end Calculus

section MatrixAlgebra

/-- `Σ_{αβ} A_{αβ} (A⁻¹)_{αβ} = n + 1` for a symmetric invertible matrix. -/
theorem sum_mul_inv_apply {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hA : Aᵀ = A)
    (hdet : A.det ≠ 0) : ∑ α, ∑ β, A α β * A⁻¹ α β = n + 1 := by
  have h := mul_nonsing_inv A hdet.isUnit
  have : ∀ α, ∑ β, A α β * A⁻¹ α β = (A * A⁻¹ᵀ) α α := fun α => by
    simp [mul_apply]
  have hinv : A⁻¹ᵀ = A⁻¹ := by rw [transpose_nonsing_inv, hA]
  simp only [this, hinv, h, one_apply_eq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  push_cast; ring

end MatrixAlgebra

namespace StepData

variable (S : StepData n ι)

/-- The conformal factor `κ = (n + 1)⁻¹ g'_{αβ}(Ψ) g(dΨ^α, dΨ^β)`. -/
def κ (x : E n) : ℝ :=
  (n + 1 : ℝ)⁻¹ * ∑ α, ∑ β, S.g' (S.Ψ x) α β *
    ∑ j, ∑ k, (S.g x)⁻¹ j k * d (fun y => S.Ψ y α) x j * d (fun y => S.Ψ y β) x k

/-- `ḡ^{αβ}` for the conformal factor `κ`. -/
def gb (x : E n) (α β : Fin (n + 1)) : ℝ := gbar S.g S.g' S.Ψ S.κ x α β

theorem gb_def (x : E n) (α β : Fin (n + 1)) :
    S.gb x α β =
      gbar S.g S.g' S.Ψ S.κ x α β := by rfl

/-- `θ̄^k` for the conformal factor `κ`. -/
def θb (x : E n) (k : Fin (n + 1)) : ℝ := θbar S.g S.g' S.Ψ S.κ x k

theorem θb_def (x : E n) (k : Fin (n + 1)) :
    S.θb x k =
      θbar S.g S.g' S.Ψ S.κ x k := by rfl

/-- `φ̄_a = φ_a - φ'_a ∘ Ψ`. -/
def φb (a : ι) (x : E n) : ℝ := S.φ a x - S.φ' a (S.Ψ x)

theorem φb_def (a : ι) (x : E n) :
    S.φb a x =
      S.φ a x - S.φ' a (S.Ψ x) := by rfl

theorem φb_eq (a : ι) : S.φb a = fun x => S.φ a x - S.φ' a (S.Ψ x) := by rfl

/-- `w̄_{a,s} = u_{a,s} - u'_{a,s} ∘ Ψ`. -/
def wb (a : ι) (s : ℝ) (x : E n) : ℝ := S.u a s x - S.u' a s (S.Ψ x)

theorem wb_def (a : ι) (s : ℝ) (x : E n) :
    S.wb a s x =
      S.u a s x - S.u' a s (S.Ψ x) := by rfl

theorem wb_eq (a : ι) (s : ℝ) : S.wb a s = fun x => S.u a s x - S.u' a s (S.Ψ x) := by rfl

variable {S}

/-- `ḡ` is trace free for `g'(Ψ)`. -/
theorem sum_g'_mul_gb (hS : S.Hyp) (x : E n) :
    ∑ α, ∑ β, S.g' (S.Ψ x) α β * S.gb x α β = 0 := by
  have h := sum_mul_inv_apply (hS.lorentzian_g' (S.Ψ x)).symm
    (hS.lorentzian_g' (S.Ψ x)).det_neg.ne
  simp only [gb, gbar_def, mul_sub, Finset.sum_sub_distrib]
  have e : ∑ α, ∑ β, S.g' (S.Ψ x) α β * (S.κ x * (S.g' (S.Ψ x))⁻¹ α β) =
      S.κ x * ∑ α, ∑ β, S.g' (S.Ψ x) α β * (S.g' (S.Ψ x))⁻¹ α β := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [e, h, κ]
  have : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- Under the pullback condition, `κ = 1`. -/
theorem κ_eq_one (hS : S.Hyp) {x : E n} (hx : x ∈ S.V)
    (hpull : S.g x = (D S.Ψ x)ᵀ * S.g' (S.Ψ x) * D S.Ψ x) : S.κ x = 1 := by
  have hΨ : DifferentiableAt ℝ S.Ψ x :=
    ((hS.smooth_Ψ.contDiffAt (hS.isOpen_V.mem_nhds hx)).differentiableAt (by simp))
  have hJ : (D S.Ψ x).det ≠ 0 :=
    det_ne_zero_of_pullback hpull (hS.lorentzian_g x).det_neg.ne
  have h0 := gbar_eq_zero (κ := fun _ => 1) hΨ hJ hpull rfl
  have h1 : ∀ α β, ∑ j, ∑ k, (S.g x)⁻¹ j k * d (fun y => S.Ψ y α) x j *
      d (fun y => S.Ψ y β) x k = (S.g' (S.Ψ x))⁻¹ α β := fun α β => by
    have := h0 α β
    simp only [gbar_def, one_mul, sub_eq_zero] at this
    exact this
  simp only [κ, h1]
  rw [sum_mul_inv_apply (hS.lorentzian_g' (S.Ψ x)).symm (hS.lorentzian_g' (S.Ψ x)).det_neg.ne]
  have : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp


section Smooth

variable (hS : S.Hyp)
include hS

theorem Hyp.det_ne_zero (x : E n) : (S.g x).det ≠ 0 := (hS.lorentzian_g x).det_neg.ne

theorem Hyp.det_ne_zero' (x : E n) : (S.g' x).det ≠ 0 := (hS.lorentzian_g' x).det_neg.ne

theorem Hyp.contDiffOn_g'Ψ (α β : Fin (n + 1)) :
    ContDiffOn ℝ ∞ (fun x => S.g' (S.Ψ x) α β) S.V :=
  (hS.smooth_g' α β).comp_contDiffOn hS.smooth_Ψ

theorem Hyp.contDiffOn_g'Ψ_inv (α β : Fin (n + 1)) :
    ContDiffOn ℝ ∞ (fun x => (S.g' (S.Ψ x))⁻¹ α β) S.V :=
  (contDiff_inv_apply hS.smooth_g' hS.det_ne_zero' α β).comp_contDiffOn hS.smooth_Ψ

theorem Hyp.contDiffOn_dΨ (α j : Fin (n + 1)) :
    ContDiffOn ℝ ∞ (fun x => d (fun y => S.Ψ y α) x j) S.V :=
  contDiffOn_d hS.isOpen_V (contDiffOn_coord hS.smooth_Ψ α) j

theorem Hyp.contDiffOn_g_inv (j k : Fin (n + 1)) :
    ContDiffOn ℝ ∞ (fun x => (S.g x)⁻¹ j k) S.V :=
  (contDiff_inv_apply hS.smooth_g hS.det_ne_zero j k).contDiffOn

theorem Hyp.contDiffOn_κ : ContDiffOn ℝ ∞ S.κ S.V :=
  contDiffOn_const.mul (ContDiffOn.sum fun α _ => ContDiffOn.sum fun β _ =>
    (hS.contDiffOn_g'Ψ α β).mul (ContDiffOn.sum fun j _ => ContDiffOn.sum fun k _ =>
      ((hS.contDiffOn_g_inv j k).mul (hS.contDiffOn_dΨ α j)).mul (hS.contDiffOn_dΨ β k)))

theorem Hyp.contDiffOn_gb (α β : Fin (n + 1)) : ContDiffOn ℝ ∞ (fun x => S.gb x α β) S.V := by
  simp only [gb, gbar_def]
  exact (ContDiffOn.sum fun j _ => ContDiffOn.sum fun k _ =>
      ((hS.contDiffOn_g_inv j k).mul (hS.contDiffOn_dΨ α j)).mul (hS.contDiffOn_dΨ β k)).sub
    (hS.contDiffOn_κ.mul (hS.contDiffOn_g'Ψ_inv α β))

theorem Hyp.contDiffOn_θb (k : Fin (n + 1)) : ContDiffOn ℝ ∞ (fun x => S.θb x k) S.V := by
  simp only [θb, θbar_def]
  refine (contDiffOn_box hS.smooth_g hS.det_ne_zero hS.isOpen_V
    (contDiffOn_coord hS.smooth_Ψ k)).neg.add (hS.contDiffOn_κ.mul ?_)
  exact (contDiff_box hS.smooth_g' hS.det_ne_zero' (contDiff_coordinate k)).comp_contDiffOn
    hS.smooth_Ψ

theorem Hyp.contDiffOn_φ'Ψ (a : ι) : ContDiffOn ℝ ∞ (fun x => S.φ' a (S.Ψ x)) S.V :=
  (hS.eikonal' a).smooth.comp hS.smooth_Ψ hS.mapsTo_Ψ

theorem Hyp.contDiffOn_φb (a : ι) : ContDiffOn ℝ ∞ (S.φb a) S.V :=
  (hS.eikonal a).smooth.sub (hS.contDiffOn_φ'Ψ a)

theorem Hyp.isOpen_JV : IsOpen (S.J ×ˢ S.V) := hS.isOpen_J.prod hS.isOpen_V

theorem Hyp.isOpen_JV' : IsOpen (S.J ×ˢ S.V') := hS.isOpen_J.prod hS.isOpen_V'

theorem Hyp.contDiffOn_u'Ψ (a : ι) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E n => S.u' a p.1 (S.Ψ p.2)) (S.J ×ˢ S.V) :=
  (hS.smooth_u' a).comp (contDiffOn_fst.prodMk (hS.smooth_Ψ.comp contDiffOn_snd
    fun _ hp => hp.2)) fun _ hp => ⟨hp.1, hS.mapsTo_Ψ hp.2⟩

theorem Hyp.contDiffOn_wb (a : ι) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E n => S.wb a p.1 p.2) (S.J ×ˢ S.V) :=
  (hS.smooth_u a).sub (hS.contDiffOn_u'Ψ a)

end Smooth

end StepData

end

end LorentzianCalderon
