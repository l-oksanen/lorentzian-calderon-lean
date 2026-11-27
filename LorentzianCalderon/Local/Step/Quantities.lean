module

public import LorentzianCalderon.Local.Step.Pointwise
public import LorentzianCalderon.Local.Step.Compact

public section

/-!
# The local continuation step: the quantities of Steps 1–3

The pointwise quantities whose weighted `L²` norms on the lens enter the absorption argument
(`absorb`): `|ḡ|²`, `|θ̄|²` (squared `ℓ¹` norms), `φ̄_a²`, `|dφ̄_a|²`, `(□_g φ̄_a)²`,
`T_a² = (θ̄^k (∂_k φ'_a) ∘ Ψ)²`, `(T_a - □_g φ̄_a)²`, and, on the fronts `s = φ_a(x)`,
`Z_a w̄_{a,s}` and `w̄_{a,s}`. All are continuous on `V`.
-/

namespace LorentzianCalderon

noncomputable section
open Set Matrix Filter
open scoped ContDiff Topology

variable {n : ℕ} {ι : Type*}

namespace StepData

variable (S : StepData n ι)

/-- `(Σ_{αβ} |ḡ^{αβ}|)²`. -/
def Gq (x : E n) : ℝ := (∑ α, ∑ β, |S.gb x α β|) ^ 2

theorem Gq_def (x : E n) :
    S.Gq x =
      (∑ α, ∑ β, |S.gb x α β|) ^ 2 := by rfl

/-- `(Σ_k |θ̄^k|)²`. -/
def Θq (x : E n) : ℝ := (∑ k, |S.θb x k|) ^ 2

theorem Θq_def (x : E n) :
    S.Θq x =
      (∑ k, |S.θb x k|) ^ 2 := by rfl

/-- `φ̄_a²`. -/
def Pq (a : ι) (x : E n) : ℝ := S.φb a x ^ 2

theorem Pq_def (a : ι) (x : E n) :
    S.Pq a x =
      S.φb a x ^ 2 := by rfl

/-- `|dφ̄_a|²` (sup norm of the components). -/
def Qq (a : ι) (x : E n) : ℝ := ‖d (S.φb a) x‖ ^ 2

theorem Qq_def (a : ι) (x : E n) :
    S.Qq a x =
      ‖d (S.φb a) x‖ ^ 2 := by rfl

/-- `(□_g φ̄_a)²`. -/
def Rq (a : ι) (x : E n) : ℝ := box S.g (S.φb a) x ^ 2

theorem Rq_def (a : ι) (x : E n) :
    S.Rq a x =
      box S.g (S.φb a) x ^ 2 := by rfl

/-- `T_a = θ̄^k (∂_k φ'_a) ∘ Ψ`. -/
def T (a : ι) (x : E n) : ℝ := ∑ k, S.θb x k * d (S.φ' a) (S.Ψ x) k

theorem T_def (a : ι) (x : E n) :
    S.T a x =
      ∑ k, S.θb x k * d (S.φ' a) (S.Ψ x) k := by rfl

/-- `T_a²`. -/
def Tq (a : ι) (x : E n) : ℝ := S.T a x ^ 2

theorem Tq_def (a : ι) (x : E n) :
    S.Tq a x =
      S.T a x ^ 2 := by rfl

/-- `(T_a - □_g φ̄_a)²`. -/
def Mq (a : ι) (x : E n) : ℝ := (S.T a x - box S.g (S.φb a) x) ^ 2

theorem Mq_def (a : ι) (x : E n) :
    S.Mq a x =
      (S.T a x - box S.g (S.φb a) x) ^ 2 := by rfl

/-- `g(dφ_a, dw̄_{a,s})` at `s = φ_a(x)`, that is `-Z_a w̄_{a,s}`. -/
def Zq (a : ι) (x : E n) : ℝ := coform S.g x (d (S.φ a) x) (d (S.wb a (S.φ a x)) x)

theorem Zq_def (a : ι) (x : E n) :
    S.Zq a x =
      coform S.g x (d (S.φ a) x) (d (S.wb a (S.φ a x)) x) := by rfl

/-- `|Z_a w̄_{a,s}|² + σ² w̄_{a,s}²` at `s = φ_a(x)`. -/
def Wq (a : ι) (σ : ℝ) (x : E n) : ℝ := S.Zq a x ^ 2 + σ ^ 2 * S.wb a (S.φ a x) x ^ 2

theorem Wq_def (a : ι) (σ : ℝ) (x : E n) :
    S.Wq a σ x =
      S.Zq a x ^ 2 + σ ^ 2 * S.wb a (S.φ a x) x ^ 2 := by rfl

theorem Gq_nonneg (x : E n) : 0 ≤ S.Gq x := by
  rw [Gq_def]; positivity

theorem Θq_nonneg (x : E n) : 0 ≤ S.Θq x := by
  rw [Θq_def]; positivity

theorem Pq_nonneg (a : ι) (x : E n) : 0 ≤ S.Pq a x := by
  rw [Pq_def]; positivity

theorem Qq_nonneg (a : ι) (x : E n) : 0 ≤ S.Qq a x := by
  rw [Qq_def]; positivity

theorem Rq_nonneg (a : ι) (x : E n) : 0 ≤ S.Rq a x := by
  rw [Rq_def]; positivity

theorem Tq_nonneg (a : ι) (x : E n) : 0 ≤ S.Tq a x := by
  rw [Tq_def]; positivity

theorem Mq_nonneg (a : ι) (x : E n) : 0 ≤ S.Mq a x := by
  rw [Mq_def]; positivity

theorem Wq_nonneg (a : ι) (σ : ℝ) (x : E n) : 0 ≤ S.Wq a σ x := by
  rw [Wq_def]; positivity

variable {S} (hS : S.Hyp)
include hS

theorem Hyp.mapsTo_φ (a : ι) : MapsTo (fun x => (S.φ a x, x)) S.V (S.J ×ˢ S.V) :=
  fun x hx => ⟨hS.mem_J a x hx, hx⟩

theorem Hyp.mapsTo_φΨ (a : ι) : MapsTo (fun x => (S.φ a x, S.Ψ x)) S.V (S.J ×ˢ S.V') :=
  fun x hx => ⟨hS.mem_J a x hx, hS.mapsTo_Ψ hx⟩

theorem Hyp.mapsTo_idΨ : MapsTo (fun p : ℝ × E n => (p.1, S.Ψ p.2)) (S.J ×ˢ S.V) (S.J ×ˢ S.V') :=
  fun _ hp => ⟨hp.1, hS.mapsTo_Ψ hp.2⟩

theorem Hyp.continuousOn_φ (a : ι) : ContinuousOn (S.φ a) S.V := (hS.eikonal a).smooth.continuousOn

theorem Hyp.continuousOn_Ψ : ContinuousOn S.Ψ S.V := hS.smooth_Ψ.continuousOn

theorem Hyp.continuousOn_pφ (a : ι) : ContinuousOn (fun x => (S.φ a x, x)) S.V :=
  (hS.continuousOn_φ a).prodMk continuousOn_id

theorem Hyp.continuousOn_pφΨ (a : ι) : ContinuousOn (fun x => (S.φ a x, S.Ψ x)) S.V :=
  (hS.continuousOn_φ a).prodMk hS.continuousOn_Ψ

theorem Hyp.continuousOn_pidΨ : ContinuousOn (fun p : ℝ × E n => (p.1, S.Ψ p.2)) (S.J ×ˢ S.V) :=
  continuousOn_fst.prodMk (hS.continuousOn_Ψ.comp continuousOn_snd fun _ hp => hp.2)

theorem Hyp.continuousOn_comp_Ψ {f : E n → ℝ} (hf : ContinuousOn f S.V') :
    ContinuousOn (fun x => f (S.Ψ x)) S.V :=
  hf.comp hS.continuousOn_Ψ hS.mapsTo_Ψ

theorem Hyp.continuousOn_d {f : E n → ℝ} (hf : ContDiffOn ℝ ∞ f S.V) (k : Fin (n + 1)) :
    ContinuousOn (fun x => d f x k) S.V :=
  (contDiffOn_d hS.isOpen_V hf k).continuousOn

theorem Hyp.continuousOn_d' {f : E n → ℝ} (hf : ContDiffOn ℝ ∞ f S.V') (k : Fin (n + 1)) :
    ContinuousOn (fun z => d f z k) S.V' :=
  (contDiffOn_d hS.isOpen_V' hf k).continuousOn

theorem Hyp.continuousOn_norm_d {f : E n → ℝ} (hf : ContDiffOn ℝ ∞ f S.V) :
    ContinuousOn (fun x => ‖d f x‖) S.V :=
  (continuousOn_pi.2 fun k => hS.continuousOn_d hf k).norm

theorem Hyp.continuousOn_box {f : E n → ℝ} (hf : ContDiffOn ℝ ∞ f S.V) :
    ContinuousOn (box S.g f) S.V :=
  (contDiffOn_box hS.smooth_g hS.det_ne_zero hS.isOpen_V hf).continuousOn

theorem Hyp.continuousOn_box' {f : E n → ℝ} (hf : ContDiffOn ℝ ∞ f S.V') :
    ContinuousOn (box S.g' f) S.V' :=
  (contDiffOn_box hS.smooth_g' hS.det_ne_zero' hS.isOpen_V' hf).continuousOn

theorem Hyp.continuousOn_param {U : ℝ → E n → ℝ}
    (hU : ContDiffOn ℝ ∞ (fun p : ℝ × E n => U p.1 p.2) (S.J ×ˢ S.V)) (a : ι) :
    ContinuousOn (fun x => U (S.φ a x) x) S.V :=
  hU.continuousOn.comp (hS.continuousOn_pφ a) (hS.mapsTo_φ a)

theorem Hyp.continuousOn_param_d {U : ℝ → E n → ℝ}
    (hU : ContDiffOn ℝ ∞ (fun p : ℝ × E n => U p.1 p.2) (S.J ×ˢ S.V)) (a : ι)
    (k : Fin (n + 1)) : ContinuousOn (fun x => d (U (S.φ a x)) x k) S.V :=
  (contDiffOn_param_d hS.isOpen_JV hU k).continuousOn.comp (hS.continuousOn_pφ a)
    (hS.mapsTo_φ a)

theorem Hyp.continuousOn_param'_Ψ {U : ℝ → E n → ℝ}
    (hU : ContinuousOn (fun p : ℝ × E n => U p.1 p.2) (S.J ×ˢ S.V')) (a : ι) :
    ContinuousOn (fun x => U (S.φ a x) (S.Ψ x)) S.V :=
  hU.comp (hS.continuousOn_pφΨ a) (hS.mapsTo_φΨ a)

theorem Hyp.continuousOn_param'_d_Ψ {U : ℝ → E n → ℝ}
    (hU : ContDiffOn ℝ ∞ (fun p : ℝ × E n => U p.1 p.2) (S.J ×ˢ S.V')) (a : ι)
    (k : Fin (n + 1)) : ContinuousOn (fun x => d (U (S.φ a x)) (S.Ψ x) k) S.V :=
  (contDiffOn_param_d hS.isOpen_JV' hU k).continuousOn.comp (hS.continuousOn_pφΨ a)
    (hS.mapsTo_φΨ a)

theorem Hyp.continuousOn_Gq : ContinuousOn S.Gq S.V :=
  (continuousOn_finsetSum _ fun α _ => continuousOn_finsetSum _ fun β _ =>
    (hS.contDiffOn_gb α β).continuousOn.abs).pow 2

theorem Hyp.continuousOn_Θq : ContinuousOn S.Θq S.V :=
  (continuousOn_finsetSum _ fun k _ => (hS.contDiffOn_θb k).continuousOn.abs).pow 2

theorem Hyp.continuousOn_Pq (a : ι) : ContinuousOn (S.Pq a) S.V :=
  (hS.contDiffOn_φb a).continuousOn.pow 2

theorem Hyp.continuousOn_Qq (a : ι) : ContinuousOn (S.Qq a) S.V :=
  (hS.continuousOn_norm_d (hS.contDiffOn_φb a)).pow 2

theorem Hyp.continuousOn_Rq (a : ι) : ContinuousOn (S.Rq a) S.V :=
  (hS.continuousOn_box (hS.contDiffOn_φb a)).pow 2

theorem Hyp.continuousOn_T (a : ι) : ContinuousOn (S.T a) S.V :=
  continuousOn_finsetSum _ fun k _ => (hS.contDiffOn_θb k).continuousOn.mul
    (hS.continuousOn_comp_Ψ (hS.continuousOn_d' (hS.eikonal' a).smooth k))

theorem Hyp.continuousOn_Tq (a : ι) : ContinuousOn (S.Tq a) S.V := (hS.continuousOn_T a).pow 2

theorem Hyp.continuousOn_Mq (a : ι) : ContinuousOn (S.Mq a) S.V :=
  ((hS.continuousOn_T a).sub (hS.continuousOn_box (hS.contDiffOn_φb a))).pow 2

theorem Hyp.continuousOn_Zq (a : ι) : ContinuousOn (S.Zq a) S.V := by
  show ContinuousOn (fun x => S.Zq a x) S.V
  simp only [Zq_def, coform_def]
  exact continuousOn_finsetSum _ fun j _ => continuousOn_finsetSum _ fun k _ =>
    ((hS.contDiffOn_g_inv j k).continuousOn.mul (hS.continuousOn_d (hS.eikonal a).smooth j)).mul
      (hS.continuousOn_param_d (hS.contDiffOn_wb a) a k)

theorem Hyp.continuousOn_Wq (a : ι) (σ : ℝ) : ContinuousOn (S.Wq a σ) S.V :=
  ((hS.continuousOn_Zq a).pow 2).add
    (continuousOn_const.mul ((hS.continuousOn_param (hS.contDiffOn_wb a) a).pow 2))

end StepData

end

end LorentzianCalderon
