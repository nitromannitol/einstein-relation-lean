import EinsteinFull.Calculus.C1EndpointFiniteP
import Mathlib.Analysis.Complex.Schwarz

/-! Removable force division on the same finite-p endpoint and projection families.
No endpoint localization estimate is assumed by the actual-family construction. -/
open MeasureTheory Metric Set
open scoped ENNReal NNReal Topology
noncomputable section

namespace EinsteinFull.EndpointDivision

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- The removable quotient retains the actual derivative at force zero. -/
def divide (E : ℂ → F) : ℂ → F := dslope E 0

@[simp] theorem divide_zero (E : ℂ → F) : divide E 0 = deriv E 0 := dslope_same E 0

/-- Exact factorization, including zero force. -/
theorem factor (E : ℂ → F) (z : ℂ) : E z - E 0 = z • divide E z := by
  simpa only [sub_zero, divide] using (sub_smul_dslope E 0 z).symm

/-- Holomorphy across the removable singularity on an open disc. -/
theorem differentiableOn_divide [CompleteSpace F] {E : ℂ → F} {R : ℝ} (hR : 0 < R)
    (hE : DifferentiableOn ℂ E {z | ‖z‖ < R}) :
    DifferentiableOn ℂ (divide E) {z | ‖z‖ < R} := by
  exact (Complex.differentiableOn_dslope (by
    simpa only [ball_zero_eq] using Metric.ball_mem_nhds (0 : ℂ) hR)).mpr hE

/-- Uniform Cauchy/Schwarz estimate on the smaller disc, with the zero case included. -/
theorem norm_divide_le {E : ℂ → F} {B M : ℝ} (hB : 0 < B)
    (hE : DifferentiableOn ℂ E {z | ‖z‖ < B + 1})
    (hn : ∀ z, ‖z‖ ≤ B + 1 → ‖E z‖ ≤ M) {z : ℂ} (hz : ‖z‖ < B) :
    ‖divide E z‖ ≤ 2 * M := by
  have h0 := hn 0 (by simp; linarith)
  have hM : 0 ≤ M := (norm_nonneg _).trans h0
  have hm : MapsTo E (ball 0 (B + 1)) (closedBall (E 0) (2 * M)) := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm]
    exact (norm_sub_le _ _).trans (by
      have hw' : ‖w‖ < B + 1 := by simpa only [mem_ball, dist_zero_right] using hw
      have hh := hn w hw'.le
      linarith)
  have hh := Complex.norm_dslope_le_div_of_mapsTo_ball
    (by simpa only [ball_zero_eq] using hE) hm
    (by simpa only [mem_ball, dist_zero_right] using hz.trans (by linarith) :
      z ∈ ball 0 (B + 1))
  exact hh.trans ((div_le_iff₀ (by linarith : 0 < B + 1)).mpr (by nlinarith))

/-- Every fixed continuous complex linear map commutes with removable division. -/
theorem divide_map (A : F →L[ℂ] G) {E : ℂ → F}
    (hE : DifferentiableAt ℂ E 0) (z : ℂ) :
    divide (fun w => A (E w)) z = A (divide E z) :=
  A.dslope_comp E 0 z (fun _ => hE)

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Zero expectation is preserved even at zero force, by the fixed bottom projection. -/
theorem integral_divide_eq_zero {E : ℂ → Lp ℂ p μ}
    (hE : DifferentiableAt ℂ E 0) (hmean : ∀ z, (∫ ω, E z ω ∂μ) = 0) (z : ℂ) :
    (∫ ω, divide E z ω ∂μ) = 0 := by
  have hb (w : ℂ) : EndpointProjection.project (m := ⊥) (E w) = 0 := by
    apply Lp.ext
    apply (EndpointProjection.project_ae (E w)).trans
    simpa only [condExp_bot, hmean w] using! (Lp.coeFn_zero ℂ p μ).symm
  have he : (fun w => EndpointProjection.projectionCLM (m := ⊥) (E w)) =
      fun _ : ℂ => (0 : Lp ℂ p μ) := funext hb
  have hc := divide_map (EndpointProjection.projectionCLM (m := ⊥)) hE z
  rw [he] at hc
  have hz : EndpointProjection.project (m := ⊥) (divide E z) = 0 := by
    have hz0 : divide (fun _ : ℂ => (0 : Lp ℂ p μ)) z = 0 := by
      by_cases hz : z = 0
      · simp [hz, divide]
      · simp only [divide, dslope_of_ne _ hz, slope_def_module, sub_self, smul_zero]
    rw [hz0] at hc
    exact hc.symm
  rw [← EndpointProjection.integral_project (m := ⊥) bot_le, hz]
  exact (integral_congr_ae (Lp.coeFn_zero ℂ p μ)).trans (integral_zero _ _)

/-- The fixed projection commutes with the same removable quotient. -/
theorem divide_project {m : MeasurableSpace Ω} {E : ℂ → Lp ℂ p μ}
    (hE : DifferentiableAt ℂ E 0) (z : ℂ) :
    divide (fun w => EndpointProjection.project (m := m) (E w)) z =
      EndpointProjection.project (m := m) (divide E z) :=
  by
    change divide (fun w => EndpointProjection.projectionCLM (μ := μ) (p := p) (m := m) (E w)) z =
      EndpointProjection.projectionCLM (μ := μ) (p := p) (m := m) (divide E z)
    exact divide_map (EndpointProjection.projectionCLM (μ := μ) (p := p) (m := m)) (E := E) hE z

/-- Applying Cauchy to the localization error preserves its Gaussian exponential.
The bound is on a larger disc; it is never divided by the force norm. -/
theorem norm_divide_sub_project_le {m : MeasurableSpace Ω}
    {E : ℂ → Lp ℂ p μ} {B M : ℝ} (hB : 0 < B)
    (hE : DifferentiableOn ℂ E {z | ‖z‖ < B + 1})
    (hn : ∀ z, ‖z‖ ≤ B + 1 →
      ‖E z - EndpointProjection.project (m := m) (E z)‖ ≤ M)
    {z : ℂ} (hz : ‖z‖ < B) :
    ‖divide E z - EndpointProjection.project (m := m) (divide E z)‖ ≤ 2 * M := by
  let A : Lp ℂ p μ →L[ℂ] Lp ℂ p μ :=
    ContinuousLinearMap.id ℂ _ - EndpointProjection.projectionCLM (m := m)
  have h0 : DifferentiableAt ℂ E 0 := hE.differentiableAt (by
    simpa only [ball_zero_eq] using Metric.ball_mem_nhds (0 : ℂ) (by linarith : 0 < B + 1))
  have hh := norm_divide_le hB (A.differentiable.comp_differentiableOn hE) hn hz
  change ‖divide (fun w => A (E w)) z‖ ≤ 2 * M at hh
  rw [divide_map A h0] at hh
  exact hh

end EinsteinFull.EndpointDivision
