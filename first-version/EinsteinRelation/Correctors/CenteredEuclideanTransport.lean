import EinsteinRelation.Correctors.AKMHeatKernelLebesguePoint
import EinsteinRelation.External.AKMEnergyDensity
import EinsteinRelation.Environment.MatrixNorm
open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors
open External.AKM

/-- Source: `paper/main.tex:709-716`. Coordinate and Euclidean carriers
give exactly the same centered scalar-plus-Frobenius average. -/
theorem centered_scalar_flux_average_toLp
    {d : ℕ} (φ : EuclideanSpace ℝ (Fin d) → ℝ) (σ : Vec d → Mat d)
    (y : EuclideanSpace ℝ (Fin d)) (r p : ℝ) :
    (⨍⁻ x in Metric.ball y r,
      ENNReal.ofReal (|φ x - ⨍ z in Metric.ball y r, φ z ∂volume| ^ p) +
      ENNReal.ofReal (frobeniusNorm (σ x.ofLp - Matrix.of (fun j k =>
        ⨍ z in Metric.ball y r, σ z.ofLp j k ∂volume)) ^ p) ∂volume) =
    (⨍⁻ x in ball y.ofLp r,
      ENNReal.ofReal (|φ (WithLp.toLp 2 x) -
        ⨍ z in ball y.ofLp r, φ (WithLp.toLp 2 z) ∂volume| ^ p) +
      ENNReal.ofReal (frobeniusNorm (σ x - Matrix.of (fun j k =>
        ⨍ z in ball y.ofLp r, σ z j k ∂volume)) ^ p) ∂volume) := by
  let e : EuclideanSpace ℝ (Fin d) ≃ᵐ Vec d := (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).toMeasurableEquiv
  have hmp : MeasurePreserving e volume volume :=
    PiLp.volume_preserving_ofLp (Fin d)
  have hpre : e ⁻¹' ball y.ofLp r = Metric.ball y r := by
    ext x
    simp [e, PiLp.homeomorph, ball,
      Metric.mem_ball, dist_eq_norm, EuclideanSpace.norm_eq,
      euclideanNorm, euclideanSq, dot, sq]
  have hvol : volume (Metric.ball y r) = volume (ball y.ofLp r) := by
    rw [← hpre]
    exact hmp.measure_preimage_emb e.measurableEmbedding (ball y.ofLp r)
  have hmp_restrict : MeasurePreserving e (volume.restrict (Metric.ball y r))
      (volume.restrict (ball y.ofLp r)) := by
    rw [← hpre]
    exact hmp.restrict_preimage_emb e.measurableEmbedding (ball y.ofLp r)
  have hs : (⨍ z in Metric.ball y r, φ z ∂volume) =
      (⨍ z in ball y.ofLp r, φ (WithLp.toLp 2 z) ∂volume) := by
    simp only [average_eq, measureReal_def, Measure.restrict_apply_univ]
    rw [hvol]
    congr 1
    simpa [e] using hmp_restrict.integral_comp e.measurableEmbedding
      (fun z => φ (WithLp.toLp 2 z))
  have ht (j k : Fin d) : (⨍ z in Metric.ball y r, σ z.ofLp j k ∂volume) =
      (⨍ z in ball y.ofLp r, σ z j k ∂volume) := by
    simp only [average_eq, measureReal_def, Measure.restrict_apply_univ]
    rw [hvol]
    congr 1
    exact hmp_restrict.integral_comp e.measurableEmbedding (fun z => σ z j k)
  simp_rw [hs, ht]
  simp only [laverage_eq, Measure.restrict_apply_univ]
  rw [hvol]
  congr 1
  let G : Vec d → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (|φ (WithLp.toLp 2 x) - ⨍ z in ball y.ofLp r, φ (WithLp.toLp 2 z) ∂volume| ^ p) +
    ENNReal.ofReal (frobeniusNorm (σ x - Matrix.of (fun j k => ⨍ z in ball y.ofLp r, σ z j k ∂volume)) ^ p)
  exact (MeasurePreserving.lintegral_map_equiv G e hmp_restrict).symm
end EinsteinRelation.Correctors
