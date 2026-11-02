import EinsteinFull.Calculus.S5WeightGradSupport
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Bounded smooth truncations of `exp (q ψ)`

`τ_n (s) = s - log (1 + exp (s - n))` is smooth, `τ_n ≤ min s n`, `0 ≤ τ_n' ≤ 1`, and
`τ_n (s) → s` as `n → ∞`.  The weight `G_n(ψ) = exp (q τ_n (ψ))` is bounded by `exp (q n)`, is
dominated by `exp (q ψ)` for `q ≥ 0`, and has gradient at most `q` times itself whenever
`|∇ψ| ≤ 1`.
-/

open Filter Topology

noncomputable section
namespace EinsteinFull
open EinsteinRelation

section S5Exp

/-- Smooth truncation of the identity from above. -/
def s5Tau (n s : ℝ) : ℝ := s - Real.log (1 + Real.exp (s - n))

/-- The truncated exponential weight profile. -/
def s5G (q n s : ℝ) : ℝ := Real.exp (q * s5Tau n s)

theorem s5Tau_le_self (n s : ℝ) : s5Tau n s ≤ s := by
  unfold s5Tau
  have : 0 ≤ Real.log (1 + Real.exp (s - n)) :=
    Real.log_nonneg (by linarith [Real.exp_pos (s - n)])
  linarith

theorem s5Tau_le_n (n s : ℝ) : s5Tau n s ≤ n := by
  unfold s5Tau
  have h : s - n < Real.log (1 + Real.exp (s - n)) := by
    calc s - n = Real.log (Real.exp (s - n)) := (Real.log_exp _).symm
      _ < Real.log (1 + Real.exp (s - n)) :=
        Real.log_lt_log (Real.exp_pos _) (by linarith)
  linarith

theorem tendsto_s5Tau (s : ℝ) : Tendsto (fun n : ℝ => s5Tau n s) atTop (𝓝 s) := by
  have h1 : Tendsto (fun n : ℝ => s - n) atTop atBot :=
    (tendsto_atBot_add_const_left atTop s tendsto_neg_atTop_atBot).congr fun n => by ring
  have h2 : Tendsto (fun n : ℝ => Real.exp (s - n)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp h1
  have h3 : Tendsto (fun n : ℝ => Real.log (1 + Real.exp (s - n))) atTop
      (𝓝 (Real.log (1 + 0))) :=
    (h2.const_add 1).log (by norm_num)
  have h4 : Real.log (1 + 0) = 0 := by simp
  have h5 := (tendsto_const_nhds (x := s)).sub h3
  rw [h4, sub_zero] at h5
  exact h5

theorem tendsto_s5G (q s : ℝ) : Tendsto (fun n : ℝ => s5G q n s) atTop (𝓝 (Real.exp (q * s))) := by
  unfold s5G
  exact (Real.continuous_exp.tendsto _).comp (((tendsto_s5Tau s).const_mul q))

theorem s5G_pos (q n s : ℝ) : 0 < s5G q n s := Real.exp_pos _

theorem s5G_le_exp {q : ℝ} (hq : 0 ≤ q) (n s : ℝ) : s5G q n s ≤ Real.exp (q * s) :=
  Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (s5Tau_le_self n s) hq)

theorem s5G_le_bound {q : ℝ} (hq : 0 ≤ q) (n s : ℝ) : s5G q n s ≤ Real.exp (q * n) :=
  Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (s5Tau_le_n n s) hq)

theorem s5Tau_hasDerivAt (n s : ℝ) :
    HasDerivAt (s5Tau n)
      (1 - Real.exp (s - n) / (1 + Real.exp (s - n))) s := by
  have h1 : HasDerivAt (fun s => Real.exp (s - n)) (Real.exp (s - n)) s := by
    simpa using ((hasDerivAt_id s).sub_const n).exp
  have h2 : HasDerivAt (fun s => 1 + Real.exp (s - n)) (Real.exp (s - n)) s := by
    simpa using h1.const_add 1
  have h3 : HasDerivAt (fun s => Real.log (1 + Real.exp (s - n)))
      (Real.exp (s - n) / (1 + Real.exp (s - n))) s :=
    h2.log (by positivity)
  exact (hasDerivAt_id s).sub h3

theorem s5Tau_deriv_mem (n s : ℝ) :
    0 ≤ 1 - Real.exp (s - n) / (1 + Real.exp (s - n)) ∧
      1 - Real.exp (s - n) / (1 + Real.exp (s - n)) ≤ 1 := by
  have hp := Real.exp_pos (s - n)
  have h1 : Real.exp (s - n) / (1 + Real.exp (s - n)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  have h2 : 0 ≤ Real.exp (s - n) / (1 + Real.exp (s - n)) := by positivity
  constructor <;> linarith

theorem s5G_hasDerivAt (q n s : ℝ) :
    HasDerivAt (s5G q n)
      (s5G q n s * (q * (1 - Real.exp (s - n) / (1 + Real.exp (s - n))))) s := by
  have h := ((s5Tau_hasDerivAt n s).const_mul q).exp
  unfold s5G
  convert h using 1

theorem s5G_contDiff (q n : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (s5G q n) := by
  unfold s5G s5Tau
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => 1 + Real.exp (s - n)) :=
    contDiff_const.add (Real.contDiff_exp.comp (contDiff_id.sub contDiff_const))
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => Real.log (1 + Real.exp (s - n))) :=
    h1.log fun s => by positivity
  exact Real.contDiff_exp.comp (contDiff_const.mul (contDiff_id.sub h2))

theorem s5_coordDeriv_comp {d : ℕ} {G : ℝ → ℝ} {G' : ℝ} {ψ : Vec d → ℝ} {x : Vec d}
    (hG : HasDerivAt G G' (ψ x)) (hψ : DifferentiableAt ℝ ψ x) (j : Fin d) :
    coordinateDerivative j (fun y => G (ψ y)) x = G' * coordinateDerivative j ψ x := by
  unfold coordinateDerivative
  have h := hG.comp_hasFDerivAt x hψ.hasFDerivAt
  have e : (fun y => G (ψ y)) = G ∘ ψ := rfl
  rw [e, h.fderiv]
  simp

/-- The truncated weight built from a smooth `1`-Lipschitz profile is an `S5Weight`. -/
theorem s5Weight_G {d : ℕ} {q : ℝ} (hq : 0 ≤ q) (n : ℝ) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hg : ∀ x, s5Nrm (fun j => coordinateDerivative j ψ x) ≤ 1) :
    S5Weight (fun x => s5G q n (ψ x)) (Real.exp (q * n)) q where
  smooth := (s5G_contDiff q n).comp hψ
  B_nonneg := (Real.exp_pos _).le
  q_nonneg := hq
  bound x := by
    rw [abs_of_pos (s5G_pos q n _)]
    exact s5G_le_bound hq n _
  grad x := by
    have hd : DifferentiableAt ℝ ψ x := (hψ.differentiable (by simp)).differentiableAt
    have e : (fun j => coordinateDerivative j (fun y => s5G q n (ψ y)) x) =
        fun j => (s5G q n (ψ x) * (q * (1 - Real.exp (ψ x - n) / (1 + Real.exp (ψ x - n))))) *
          coordinateDerivative j ψ x := by
      funext j
      exact s5_coordDeriv_comp (s5G_hasDerivAt q n (ψ x)) hd j
    rw [e, s5Nrm_smul, abs_of_pos (s5G_pos q n _)]
    obtain ⟨h0, h1⟩ := s5Tau_deriv_mem n (ψ x)
    have hGp := s5G_pos q n (ψ x)
    have habs : |s5G q n (ψ x) * (q * (1 - Real.exp (ψ x - n) / (1 + Real.exp (ψ x - n))))| ≤
        s5G q n (ψ x) * q := by
      rw [abs_of_nonneg (mul_nonneg hGp.le (mul_nonneg hq h0))]
      exact mul_le_mul_of_nonneg_left (by nlinarith) hGp.le
    calc _ ≤ (s5G q n (ψ x) * q) * 1 :=
          mul_le_mul habs (hg x) (s5Nrm_nonneg _) (by positivity)
      _ = q * s5G q n (ψ x) := by ring

end S5Exp

end EinsteinFull
