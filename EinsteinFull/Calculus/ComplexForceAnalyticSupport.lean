import EinsteinFull.Calculus.ComplexMildAnalyticSupport
import EinsteinFull.Calculus.VolterraAnalyticSupport

/-!
# Entire complex-force dependence of the actual stationary L2 semigroup

Neumann inversion gives operator-norm analyticity on a short-time force disc.
Integer subdivision makes every fixed force belong to such a disc, and the
actual semigroup law identifies the long-time operator with a finite power.
-/

open MeasureTheory Filter Set
open scoped Topology NNReal BoundedContinuousFunction
noncomputable section
namespace EinsteinFull
open EinsteinRelation

variable {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d}

/-- The weighted gradient is operator-norm analytic throughout the short-time force disc. -/
theorem analyticAt_weightedGradientOrbit_of_small_force
    {F : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hF : ∀ z : ℂ, IsComplexEnvironmentSemigroup Q i z (F z)) (T : ℝ) (z₀ : ℂ)
    (hs : ‖z₀‖ * (4 * Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) *
      ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) * Real.sqrt T) < 1) :
    AnalyticAt ℂ (fun z => (hF z).weightedGradientOrbit T) z₀ := by
  apply analyticAt_clm_of_eq_add_comp_smul_of_norm_lt_one ((hF 0).weightedVolterra T)
    ((hF 0).weightedGradientOrbit T)
  · intro z
    apply ContinuousLinearMap.ext
    intro f
    exact (hF z).weightedGradientOrbit_eq (hF 0) T f
  · exact (ContinuousLinearMap.opNorm_smul_le z₀ _).trans_lt
      ((mul_le_mul_of_nonneg_left ((hF 0).norm_weightedVolterra_le T)
        (norm_nonneg z₀)).trans_lt hs)

/-- The actual semigroup is operator-norm analytic throughout the short-time force disc. -/
theorem analyticAt_complexEnvironmentSemigroup_of_small_force
    {F : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hF : ∀ z : ℂ, IsComplexEnvironmentSemigroup Q i z (F z)) (t : ℝ≥0) (z₀ : ℂ)
    (hs : ‖z₀‖ * (4 * Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) *
      ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) * Real.sqrt (t : ℝ)) < 1) :
    AnalyticAt ℂ (fun z => F z t) z₀ := by
  have hg := analyticAt_weightedGradientOrbit_of_small_force hF (t : ℝ) z₀ hs
  have hc := (((ContinuousLinearMap.compL ℂ _ _ _) ((hF 0).weightedDuhamel t)).analyticAt _).comp hg
  have ha := (analyticAt_const (v := F 0 t)).add
    ((analyticAt_id (𝕜 := ℂ) (z := z₀)).fun_smul hc)
  apply ha.congr
  apply Eventually.of_forall
  intro z
  exact ((hF z).eq_add_weightedDuhamel (hF 0) t).symm

/-- Integer time iteration of an actual semigroup equals its operator power. -/
theorem IsComplexEnvironmentSemigroup.nsmul_eq_pow
    {ζ : ℂ} {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (n : ℕ) (t : ℝ≥0) :
    P (n • t) = (P t)^n := by
  induction n with
  | zero => simpa only [zero_nsmul, pow_zero] using! hP.1
  | succ n ih =>
    rw [succ_nsmul, hP.2.1, ih, pow_succ]
    rfl

/-- Time subdivision makes the actual complex-force semigroup entire in operator norm. -/
theorem analyticAt_complexEnvironmentSemigroup
    {F : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hF : ∀ z : ℂ, IsComplexEnvironmentSemigroup Q i z (F z)) (t : ℝ≥0) (z₀ : ℂ) :
    AnalyticAt ℂ (fun z => F z t) z₀ := by
  obtain ⟨n, hn, hs⟩ := exists_pos_nat_mul_sqrt_div_lt_one
    (‖z₀‖ * (4 * Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) *
      ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)))) (t : ℝ)
  let s : ℝ≥0 := t / n
  have hsmall : ‖z₀‖ * (4 * Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) *
      ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) * Real.sqrt (s : ℝ)) < 1 := by
    simpa only [s, NNReal.coe_div, NNReal.coe_natCast, mul_assoc] using hs
  have ha := (analyticAt_complexEnvironmentSemigroup_of_small_force hF s z₀ hsmall).fun_pow n
  have he : n • s = t := by
    rw [nsmul_eq_mul]
    dsimp only [s]
    exact mul_div_cancel₀ t (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))
  apply ha.congr
  apply Eventually.of_forall
  intro z
  exact ((hF z).nsmul_eq_pow n s).symm.trans (congrArg (F z) he)

/-- The internally constructed stationary evolution is entire in complex force in operator norm. -/
theorem analyticAt_forcedComplexEvolution (t : ℝ≥0) (z₀ : ℂ) :
    AnalyticAt ℂ (fun z => forcedComplexEvolution Q i z t) z₀ :=
  analyticAt_complexEnvironmentSemigroup
    (fun z => isComplexEnvironmentSemigroup_forcedComplexEvolution Q i z) t z₀

end EinsteinFull
