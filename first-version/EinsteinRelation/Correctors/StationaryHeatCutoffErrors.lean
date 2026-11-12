import EinsteinRelation.Correctors.StationaryLocalErrorLimit
import EinsteinRelation.Correctors.RoundedCutoffWindowLp
import EinsteinRelation.Correctors.HeatGradientJointMeasurability
import EinsteinRelation.Correctors.HeatGradientStationaryCovariance

/-! Source: `paper/main.tex:722,756`. Both literal heat cutoff endpoint
errors vanish almost surely in local L² after any positive time dilation. -/
open MeasureTheory Filter Topology
open scoped ENNReal
namespace EinsteinRelation.Correctors
open HeatSelectedSkewMeaning

/-- Stationarity turns the environment `C/t` estimate into almost sure
local L² convergence of both actual endpoint windows. Their endpoints
remain the prescribed rescaled times and the nearest original mesh times. -/
theorem ae_heat_cutoff_endpoint_errors_local_L2 {d : ℕ}
    (Q : Measure (FieldPair d)) [SFinite Q] (hQ : IsStationary Q)
    (ν : Measure (Vec d)) [IsFiniteMeasure ν]
    (F : FieldPair d → Vec d) (hF : Measurable F)
    (j k l : Fin d) (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hbound : ∀ t : ℝ, 0 < t → eLpNorm
      (fun ω => akmHeatGradientSpaceIntegral (fun y => F (translate y ω)) t j k l 0)
        2 Q ≤ ENNReal.ofReal (C / t)) :
    let lower : ℕ → FieldPair d → Vec d → ℝ := fun n ω x =>
      ∫ t in Set.Icc (((⌊(c / ((n : ℝ) + 1))⁻¹⌋₊ + 1 : ℕ) : ℝ))⁻¹
        (c / ((n : ℝ) + 1)),
        akmHeatGradientSpaceIntegral (fun y => F (translate y ω)) t j k l x
    let upper : ℕ → FieldPair d → Vec d → ℝ := fun n ω x =>
      ∫ t in Set.Icc (c * ((n : ℝ) + 1))
        ((⌊c * ((n : ℝ) + 1)⌋₊ + 1 : ℕ) : ℝ),
        akmHeatGradientSpaceIntegral (fun y => F (translate y ω)) t j k l x
    ∀ᵐ ω ∂Q,
      ((∀ n, MemLp (lower n ω) 2 ν) ∧
        Tendsto (fun n => eLpNorm (lower n ω) 2 ν) atTop (𝓝 0)) ∧
      ((∀ n, MemLp (upper n ω) 2 ν) ∧
        Tendsto (fun n => eLpNorm (upper n ω) 2 ν) atTop (𝓝 0)) := by
  dsimp only
  let H : FieldPair d × ℝ → ℝ := fun q =>
    akmHeatGradientSpaceIntegral (fun y => F (translate y q.1)) q.2 j k l 0
  have hH : Measurable H :=
    (measurable_actualHeatGradientSpaceIntegral_stationary F hF j k l).comp
      (measurable_id.prodMk measurable_const)
  let a (n : ℕ) : ℝ := c / ((n : ℝ) + 1)
  let b (n : ℕ) : ℝ := c * ((n : ℝ) + 1)
  let f (n : ℕ) (ω : FieldPair d) : ℝ :=
    ∫ t in Set.Icc (((⌊(a n)⁻¹⌋₊ + 1 : ℕ) : ℝ))⁻¹ (a n), H (ω, t)
  let g (n : ℕ) (ω : FieldPair d) : ℝ :=
    ∫ t in Set.Icc (b n) ((⌊b n⌋₊ + 1 : ℕ) : ℝ), H (ω, t)
  have hf (n : ℕ) : Measurable (f n) :=
    hH.stronglyMeasurable.integral_prod_right'.measurable
  have hg (n : ℕ) : Measurable (g n) :=
    hH.stronglyMeasurable.integral_prod_right'.measurable
  have hfnorm (n : ℕ) : eLpNorm (f n) 2 Q ≤
      ENNReal.ofReal ((C * c) / ((n : ℝ) + 1)) :=
    eLpNorm_reciprocal_rounding_window_le (by norm_num) (by norm_num)
      hH hC hc hbound n
  have hgnorm (n : ℕ) : eLpNorm (g n) 2 Q ≤
      ENNReal.ofReal ((C / c) / ((n : ℝ) + 1)) :=
    eLpNorm_integer_rounding_window_le (by norm_num) (by norm_num)
      hH hC hc hbound n
  filter_upwards [ae_local_L2_zero_of_stationary_error_bound Q hQ ν f hf
    (C * c) (mul_pos hC hc).le hfnorm,
    ae_local_L2_zero_of_stationary_error_bound Q hQ ν g hg
      (C / c) (div_pos hC hc).le hgnorm] with ω hωf hωg
  have hlower (n : ℕ) : (fun x =>
      ∫ t in Set.Icc (((⌊(c / ((n : ℝ) + 1))⁻¹⌋₊ + 1 : ℕ) : ℝ))⁻¹
        (c / ((n : ℝ) + 1)),
        akmHeatGradientSpaceIntegral (fun y => F (translate y ω)) t j k l x) =
        (fun x => f n (translate x ω)) := by
    funext x
    exact setIntegral_akmHeatGradient_stationary_covariance F ω _ j k l x
  have hupper (n : ℕ) : (fun x =>
      ∫ t in Set.Icc (c * ((n : ℝ) + 1))
        ((⌊c * ((n : ℝ) + 1)⌋₊ + 1 : ℕ) : ℝ),
        akmHeatGradientSpaceIntegral (fun y => F (translate y ω)) t j k l x) =
        (fun x => g n (translate x ω)) := by
    funext x
    exact setIntegral_akmHeatGradient_stationary_covariance F ω _ j k l x
  simpa only [hlower, hupper] using And.intro hωf hωg

end EinsteinRelation.Correctors
