import EinsteinRelation.Correctors.CanonicalAffineLocalRegularity
import EinsteinRelation.Correctors.RegularRepresentativeSelection
import EinsteinRelation.Correctors.HolderContinuity

/-! Source: `paper/main.tex:694-704,735-737`. The spatial canonical
affine gradient admits a jointly measurable continuous version. This
selection depends only on its existing stationary volume class. -/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger StationarySpatialRealization

/-- A regular version of the actual affine corrector gradient. -/
def canonicalAffineGradientRegularRepresentative
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (ω : FieldPair d) (x : Vec d) : Vec d := fun j =>
  spatialRegularRepresentative (fun ρ z => (unitVector i +
    ((canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
      (reducedEnvironmentLaw Q)) (translate z ρ)).ofLp) j) ω x

/-- The regular affine gradient is jointly Borel measurable. -/
theorem measurable_canonicalAffineGradientRegularRepresentative
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    Measurable (fun p : Vec d × FieldPair d =>
      canonicalAffineGradientRegularRepresentative Q i p.2 p.1) := by
  apply measurable_pi_lambda
  intro j
  apply measurable_spatialRegularRepresentative
  have hg := (PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin d => ℝ)).measurable.comp
    (measurable_spatialRealization (canonicalCorrectorGradient Q i :
      Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)))
  exact (measurable_pi_apply j).comp (measurable_const.add hg)

/-- The sup norm ball is contained in a controlled Euclidean ball. -/
theorem supBall_subset_dimension_euclideanBall {d : ℕ} {R : ℝ} :
    Metric.ball (0 : Vec d) R ⊆ ball 0 (((d : ℝ) + 1) * R) := by
  intro x hx
  change euclideanNorm (x - 0) < ((d : ℝ) + 1) * R
  rw [sub_zero]
  exact (euclideanNorm_le_dimension_mul_norm x).trans_lt
    (mul_lt_mul_of_pos_left (by simpa only [Metric.mem_ball, dist_zero_right] using hx)
      (by positivity))

/-- Continuous gradient versions supplied locally by GT identify the
shrinking-average selection for almost every environment, on all space. -/
theorem ae_canonicalAffineGradientRegularRepresentative
    (hP : BallPoincareEstimate) (h836 : InteriorRegularRepresentative)
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      Continuous (canonicalAffineGradientRegularRepresentative Q i ω) ∧
      (fun x => unitVector i +
        ((canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
          (reducedEnvironmentLaw Q)) (translate x ω)).ofLp) =ᵐ[volume]
        canonicalAffineGradientRegularRepresentative Q i ω := by
  filter_upwards [ae_canonicalAffine_c1Alpha_representatives hP h836 Q i] with ω hω
  obtain ⟨u, _, _, hu⟩ := hω
  have hj (j : Fin d) := continuous_spatialRegularRepresentative_of_ball_versions
    (fun x => (unitVector i +
      ((canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
        (reducedEnvironmentLaw Q)) (translate x ω)).ofLp) j) (by
      intro n
      let S : ℝ := ((d : ℝ) + 1) * ((n : ℝ) + 1)
      obtain ⟨v, h, hreg, _, hheq⟩ := hu S (by dsimp [S]; positivity)
      obtain ⟨K, hK⟩ := hreg.2
      refine ⟨fun x => h x j,
        (continuousOn_of_holderBound (by norm_num : (0 : ℝ) < 1 / 2) (hK j)).mono
          supBall_subset_dimension_euclideanBall, ?_⟩
      filter_upwards [hheq.symm.filter_mono (ae_mono (Measure.restrict_mono_set volume
        supBall_subset_dimension_euclideanBall))] with x hx
      exact congrFun hx j)
  refine ⟨continuous_pi_iff.mpr (fun j => (hj j).1), ?_⟩
  filter_upwards [ae_all_iff.mpr (fun j => (hj j).2)] with x hx
  exact funext hx

end EinsteinRelation.Correctors
