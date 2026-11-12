import EinsteinRelation.Correctors.PairedCorrectorPlanarAmplitude
import EinsteinRelation.Correctors.ConditionalCenteredCoordinateTransport
import EinsteinRelation.Correctors.SpatialBallVolume

/-! Spatial continuity and the literal mollifier for the repaired planar
estimate, `paper/main.tex:872–894`. The coordinate carrier retains its usual
norm; every ball below is an AKM Euclidean ball. -/

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM NormalizedSpatialRepresentativeSupport

/-- Continuity supplies local square integrability on Euclidean balls.
Source: `paper/main.tex:872–883`. -/
theorem continuous_memLp_euclideanBall {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (u : Vec d → E) (hu : Continuous u) (R : ℝ) :
    MemLp u 2 (volume.restrict (ball 0 R)) := by
  apply (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mpr
  apply ((hu.norm.pow 2).continuousOn.integrableOn_compact
    (isCompact_closedBall (0 : Vec d) R)).mono_set
  intro x hx
  apply Metric.mem_closedBall.mpr
  rw [dist_zero_right]
  have hxR : euclideanNorm x < R := by simpa [ball] using hx
  exact (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    (fun j => by simpa only [Real.norm_eq_abs] using Regeneration.coordinate_abs_le_euclideanNorm x j)
    |>.trans hxR.le

/-- Continuous skew fields have their prescribed point values fixed by
almost-everywhere skewness. Source: `paper/main.tex:877–883`. -/
theorem continuous_skew_of_ae {d : ℕ} (S : Vec d → Mat d) (hS : Continuous S)
    (hs : ∀ᵐ x ∂volume, (S x).transpose = -(S x)) :
    ∀ x, (S x).transpose = -(S x) := by
  have heq : (fun x => (S x).transpose) = (fun x => -(S x)) :=
    (hS.matrix_transpose.ae_eq_iff_eq volume hS.neg).mp hs
  exact fun x => congrFun heq x

/-- The scaled source mollifier in coordinates centered at its actual
source center. Source: `paper/main.tex:872–894`. -/
theorem sourceMollifier_centered_coordinates {d : ℕ}
    (ζ : SourceMollifier d) {R : ℝ} (hR : 1 ≤ R) (y : Point d) :
    let w : Vec d → ℝ := fun x =>
      sourceScaledMollifierKernel ζ R y (WithLp.toLp 2 (x + y.ofLp))
    Continuous w ∧ HasCompactSupport w ∧ Integrable w volume ∧
      (∀ x, 0 ≤ w x) ∧ (∫ x, w x) = 1 ∧ Function.support w ⊆ ball 0 R := by
  dsimp only
  let w : Vec d → ℝ := fun x =>
    sourceScaledMollifierKernel ζ R y (WithLp.toLp 2 (x + y.ofLp))
  change Continuous w ∧ HasCompactSupport w ∧ Integrable w volume ∧
    (∀ x, 0 ≤ w x) ∧ (∫ x, w x) = 1 ∧ Function.support w ⊆ ball 0 R
  have heq : w = fun x => sourceScaledMollifierKernel ζ R 0 (WithLp.toLp 2 x) := by
    ext x
    simp [w, sourceScaledMollifierKernel]
  have hc : Continuous w := by
    rw [heq]
    exact (continuous_sourceScaledMollifierKernel ζ R 0).comp
      (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ))
  have hs : HasCompactSupport w := by
    rw [heq]
    exact (hasCompactSupport_sourceScaledMollifierKernel ζ hR 0).comp_homeomorph
      (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).symm
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  refine ⟨hc, hs, hc.integrable_of_hasCompactSupport hs, ?_, ?_, ?_⟩
  · intro x
    rw [heq]
    exact mul_nonneg (inv_nonneg.mpr (pow_nonneg hRpos.le _)) (ζ.nonnegative _)
  · rw [heq]
    exact ((PiLp.volume_preserving_toLp (Fin d)).integral_comp
      (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).symm.measurableEmbedding
      _).trans (integral_sourceScaledMollifierKernel ζ hR 0)
  · intro x hx
    have hn : ζ.density (R⁻¹ • WithLp.toLp 2 x) ≠ 0 := by
      intro hz
      apply hx
      simp [heq, sourceScaledMollifierKernel, hz, Function.mem_support] at *
    have hb := ζ.supportWithinUnitBall (subset_tsupport _ (Function.mem_support.mpr hn))
    have hb' : R⁻¹ * euclideanNorm x < 1 := by
      simpa [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hRpos), abs_of_pos hRpos, TimeChange.euclideanNorm_eq_norm_toLp] using hb
    change euclideanNorm (x - 0) < R
    rw [sub_zero]
    exact (inv_mul_lt_iff₀ hRpos).mp hb' |>.trans_eq (mul_one R)
end EinsteinRelation.Correctors
