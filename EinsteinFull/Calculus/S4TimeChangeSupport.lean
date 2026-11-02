import EinsteinFull.Calculus.S4PathClockSupport
import EinsteinFull.Calculus.S4GeneratorRegularitySupport

/-!
# The deterministic time-change identity

Along a continuous path `γ`, with `σ_s = A_γ⁻¹ (s)` the inverse of the clock
`A_γ (t) = ∫₀ᵗ μ (γ u) du`, the substitution `u = A_γ (t)` gives
`∫₀^{σ_s} G(γ_t) μ(γ_t) dt = ∫₀^s G(γ_{σ_u}) du`.
Consequently the compensated physical test at time `s` along `inverseClockPath` equals the
compensated reduced test at the time `σ_s`.
-/

open MeasureTheory
open scoped NNReal

namespace EinsteinFull
open EinsteinRelation
open EinsteinRelation.Clock EinsteinRelation.Clock.InverseMeaningV3

theorem timeChange_integral {d : ℕ} {L : ℝ} {ω : FieldPair d} (hω : IsRegular L ω)
    (γ : Path d) (s : ℝ≥0) {G : Vec d → ℝ} (hG : Continuous G) :
    ∫ t in (0 : ℝ)..((inversePhysicalPathClock ω γ L hω s : ℝ≥0) : ℝ),
        G (γ t.toNNReal) * clockDensity ω (γ t.toNNReal) =
      ∫ u in (0 : ℝ)..(s : ℝ), G (γ (inversePhysicalPathClock ω γ L hω u.toNNReal)) := by
  have hμ : Continuous (clockDensity ω) := (reduce ω).2.continuous
  have hcont : Continuous (fun u : ℝ => clockDensity ω (γ u.toNNReal)) :=
    hμ.comp (γ.continuous.comp continuous_real_toNNReal)
  have hσ : Continuous (inversePhysicalPathClock ω γ L hω) :=
    (physicalPathClockOrderIso ω γ L hω).symm.continuous
  have hg : Continuous
      (fun u : ℝ => G (γ (inversePhysicalPathClock ω γ L hω u.toNNReal))) :=
    hG.comp (γ.continuous.comp (hσ.comp continuous_real_toNNReal))
  have hF : ∀ t : ℝ, 0 ≤ t →
      (∫ u in (0 : ℝ)..t, clockDensity ω (γ u.toNNReal)) =
        ((physicalPathClock ω γ t.toNNReal : ℝ≥0) : ℝ) := by
    intro t ht
    show _ = pathClock (clockDensity ω) γ t.toNNReal
    unfold pathClock
    rw [Real.coe_toNNReal t ht]
  have key := intervalIntegral.integral_comp_mul_deriv (a := 0)
    (b := ((inversePhysicalPathClock ω γ L hω s : ℝ≥0) : ℝ))
    (f := fun t : ℝ => ∫ u in (0 : ℝ)..t, clockDensity ω (γ u.toNNReal))
    (f' := fun t : ℝ => clockDensity ω (γ t.toNNReal))
    (g := fun u : ℝ => G (γ (inversePhysicalPathClock ω γ L hω u.toNNReal)))
    (fun x _ => (hcont.integral_hasStrictDerivAt 0 x).hasDerivAt) hcont.continuousOn hg
  have hF0 : (∫ u in (0 : ℝ)..(0 : ℝ), clockDensity ω (γ u.toNNReal)) = 0 :=
    intervalIntegral.integral_same
  have hFT : (∫ u in (0 : ℝ)..((inversePhysicalPathClock ω γ L hω s : ℝ≥0) : ℝ),
      clockDensity ω (γ u.toNNReal)) = (s : ℝ) := by
    rw [hF _ (NNReal.coe_nonneg _), Real.toNNReal_coe,
      physicalPathClock_inversePhysicalPathClock]
  rw [hF0, hFT] at key
  rw [← key]
  refine intervalIntegral.integral_congr fun x hx => ?_
  have hx0 : 0 ≤ x := by
    rw [Set.uIcc_of_le (NNReal.coe_nonneg _)] at hx
    exact hx.1
  show G (γ x.toNNReal) * clockDensity ω (γ x.toNNReal) =
    G (γ (inversePhysicalPathClock ω γ L hω
      (∫ u in (0 : ℝ)..x, clockDensity ω (γ u.toNNReal)).toNNReal)) *
      clockDensity ω (γ x.toNNReal)
  rw [hF x hx0, Real.toNNReal_coe, inversePhysicalPathClock_physicalPathClock]

/-- The compensated physical test along the inverse-clock path is the compensated reduced test
at the stopping time `σ_s`. -/
theorem compensatedTest_physical_inverseClockPath {d : ℕ} {L : ℝ} {ω : FieldPair d}
    (hω : IsRegular L ω) (hs : IsSmoothFieldPair ω) (i : Fin d) (lam : ℝ) {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (γ : Path d) (s : ℝ≥0) :
    compensatedTest (physicalGenerator i ω lam) f s (inverseClockPath ω γ L hω) =
      compensatedTest (reducedGenerator i ω lam) f
        (inversePhysicalPathClock ω γ L hω s) γ := by
  unfold compensatedTest
  have h0 : (inverseClockPath ω γ L hω) 0 = γ 0 := inverseClockPath_zero ω γ L hω
  have hcv := timeChange_integral hω γ s
    (G := physicalGenerator i ω lam f) (continuous_physicalGenerator_apply hs i lam hf)
  have e1 : (fun t : ℝ => reducedGenerator i ω lam f (γ t.toNNReal)) =
      fun t : ℝ => physicalGenerator i ω lam f (γ t.toNNReal) *
        clockDensity ω (γ t.toNNReal) := by
    funext t
    rw [← clockDensity_mul_physicalGenerator]
    exact mul_comm _ _
  rw [h0, e1, hcv]
  rfl

end EinsteinFull
