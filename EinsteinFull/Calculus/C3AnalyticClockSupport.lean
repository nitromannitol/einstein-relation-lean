import EinsteinFull.Calculus.C1EndpointFiniteP
import EinsteinFull.Calculus.C1ClockAnalyticitySupport

/-! Clock values before force multiplication, including force zero.
These are partial supports, not the analytic-clock graph reduction. -/

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace EinsteinFull.AnalyticClock
open EinsteinRelation EinsteinFull.Blueprint

private instance reducedProbability {d : ℕ} {Λ R : ℝ}
    (Q : EnvironmentLaw d Λ R) : IsProbabilityMeasure (reducedLaw Q) :=
  reducedLaw_probability Q

/-- The actual clock observation is bounded, hence belongs to every finite Lp.
No initial horizontal derivative of the clock is required. -/
theorem clock_memLp {d : ℕ} (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (μ : Lp ℂ 2 (reducedLaw Q)) (hμ : IsReducedClockObservation Q μ)
    (p : ℝ≥0∞) : MemLp μ p (reducedLaw Q) := by
  obtain ⟨L, A, B, hL, _, _, _, hb⟩ :=
    node_eq_u2E_reduced_u2D_bounds_of_deps D.ellipticity D.one_le_ellipticity
  apply MemLp.of_bound (Lp.memLp μ).aestronglyMeasurable L
  filter_upwards [hμ, (hb d D.dependenceRange Q).2.2] with ω hω hbounds
  rw [hω, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ((inv_nonneg.mpr (zero_le_one.trans hL)).trans (hbounds.2.1 0).1)]
  exact (hbounds.2.1 0).2

/-- Finite-p representatives of W itself, obtained without dividing by force.
The compact-time constant is chosen before the environment law and datum. -/
theorem exists_centered_representatives
    (hA : node_stationary_u2D_analytic_u2D_semigroupStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (p R T : ℝ) (hp : 2 ≤ p) (hR : 0 < R) (hT : 0 < T) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
    ∃ C : ℝ, 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q →
    ∀ (μ : Lp ℂ 2 (reducedLaw Q)), IsReducedClockObservation Q μ →
    ∀ (P : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      (∀ ζ, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (P ζ)) →
    ∀ r : ℝ≥0, (r : ℝ) ≤ T →
    ∃ Wp : ℂ → Lp ℂ (ENNReal.ofReal p) (reducedLaw Q),
      (∀ ζ, (Wp ζ : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
        centeredComplexLp Q (P ζ r μ)) ∧
      (∀ ζ, AnalyticAt ℂ Wp ζ) ∧
      (∀ ζ, ‖ζ‖ ≤ R → ‖Wp ζ‖ ≤
        C * (eLpNorm μ (ENNReal.ofReal p) (reducedLaw Q)).toReal) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  obtain ⟨C, hC, hrep⟩ := (hA d hd D).2 p R T hp hR hT
  refine ⟨2 * C, by positivity, ?_⟩
  intro Q hQ μ hμ P hP r hr
  have hmem := clock_memLp D Q μ hμ (ENNReal.ofReal p)
  obtain ⟨hb, u, v, huv, han⟩ := hrep Q hQ μ hmem r hr
  have he (ζ : ℂ) : (u ζ : FieldPair d → ℂ) =ᵐ[reducedLaw Q] P ζ r μ := by
    simpa only [(hP ζ).eq_forcedComplexEvolution] using (huv ζ).1
  refine ⟨fun ζ => EndpointFiniteP.center (u ζ),
    fun ζ => EndpointFiniteP.center_ae_l2 Q (u ζ) (P ζ r μ) (he ζ), ?_, ?_⟩
  · intro ζ
    exact ((EndpointFiniteP.center (μ := reducedLaw Q)).analyticAt _).comp (han ζ).1
  · intro ζ hζ
    have hn : ‖u ζ‖ ≤ C * (eLpNorm μ (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
      rw [Lp.norm_def, eLpNorm_congr_ae (huv ζ).1]
      have h := ENNReal.toReal_mono
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmem.eLpNorm_ne_top) (hb ζ hζ).2.2.1
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC.le] using h
    exact (EndpointFiniteP.norm_center_le (u ζ)).trans (by linarith)

end EinsteinFull.AnalyticClock
