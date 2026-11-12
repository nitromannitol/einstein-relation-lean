import EinsteinRelation.Correctors.AKMPhysicalScalarLocalBound
import EinsteinRelation.Correctors.AKMPhysicalFluxOscillationBound
import EinsteinRelation.Correctors.AKMPhysicalFluxSobolev
import EinsteinRelation.Correctors.FrobeniusEntryBound
import EinsteinRelation.Correctors.LocalRootIntegralMonotonicity
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger HeatSelectedSkewMeaning
open Environment.AKMTestIntegralSupport ReductionImageV3
/-- Source: `paper/main.tex:727-745`. Both physical potentials have
local value bounds controlled by their radius-four L² oscillations. -/
theorem ae_physicalAKM_joint_local_bounds
    (h817 : LocalBoundednessEstimate) (h68 : FluxGradientEstimate)
    (hP : BallPoincareEstimate) (h832 : InteriorGradientEstimate)
    (h836 : InteriorRegularRepresentative) (d : ℕ) [Fact (2 ≤ d)]
    (L : ℝ) (hL : 1 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ {r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
      (i : Fin d) (φ : Corrector (actualCoefficientLaw Q) (halfDirection i))
      (S : FluxCorrector (scaledAKMCorrector φ 2)),
      (∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
        (2 : ℝ) • (halfDirection i + φ.grad
          (project (r₀ := r₀) Q.ellipticity_parameter ω) y) =
        (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate (r₀ • y) (reduce ω.1))).ofLp) →
      (∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
        centeredFlux (scaledAKMCorrector φ 2)
          (project (r₀ := r₀) Q.ellipticity_parameter ω) y =
            ellipticityScale L •
              ((canonicalCorrectorFlux Q i (translate (r₀ • y) (reduce ω.1))).ofLp -
                (expectedCorrectorFlux Q i).ofLp)) →
      ∀ (σ : FieldPair d → Vec d → Mat d),
        HasHeatSelectedSkewCorrectorColumn (Fact.out : 2 ≤ d) Q i σ →
        ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ (z : Vec d) (c : ℝ) (b : Mat d),
          let u : Vec d → ℝ := fun x => (2 * r₀) * φ.potential
            (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x)
          let T : Vec d → Mat d := fun x => (r₀ / ellipticityScale L) • S.potential
            (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x)
          let A : ℝ := 1 + Real.sqrt (∫ x in ball z 4, |u x - c| ^ 2 ∂volume) +
            Real.sqrt (∫ x in ball z 4, frobeniusNorm (T x - b) ^ 2 ∂volume)
          ∀ᵐ x ∂volume.restrict (ball z (1 / 4)),
            |u x - c| ≤ C * A ∧ frobeniusNorm (T x - b) ≤ C * A := by
  obtain ⟨A, hA, ha⟩ := ae_physicalAKMScalar_local_bound_of_GT h817 d L hL
  obtain ⟨B, hB, hb⟩ := ae_physicalAKMFlux_local_bound_from_scalar_oscillation
    h817 h68 hP h832 h836 d L hL
  refine ⟨A + ((d : ℝ) + 1) * B, by positivity, ?_⟩
  intro r₀ Q i φ S hid hsource σ hσ
  filter_upwards [ha Q i φ hid, hb Q i φ S hid hsource σ hσ,
    ae_physicalAKMFlux_memLp_on_balls Q i φ S,
    ae_physicalAKMPotential_affine_weakSolution Q i φ hid] with ω hu hT hS huLp
  intro z c b
  let u : Vec d → ℝ := fun x => (2 * r₀) * φ.potential
    (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x)
  let T : Vec d → Mat d := fun x => (r₀ / ellipticityScale L) • S.potential
    (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x)
  let U := Real.sqrt (∫ x in ball z 4, |u x - c| ^ 2 ∂volume)
  let V := Real.sqrt (∫ x in ball z 4, frobeniusNorm (T x - b) ^ 2 ∂volume)
  have hU : 0 ≤ U := Real.sqrt_nonneg _
  have hV : 0 ≤ V := Real.sqrt_nonneg _
  letI : IsFiniteMeasure (volume.restrict (ball z 4)) :=
    isFiniteMeasure_restrict_euclideanBall z 4 (by norm_num)
  have hSm : ∀ j k, MemLp (fun x => (T x - b) j k) 2 (volume.restrict (ball z 4)) :=
    fun j k => (hS z 4 (by norm_num) j k).sub (memLp_const _)
  have hroot : ∀ j k, Real.sqrt (∫ x in ball z 1, |(T x - b) j k| ^ 2 ∂volume) ≤ V :=
    fun j k => sqrt_entry_integral_le_frobenius_on_larger_ball
      (fun x => T x - b) z 1 4 (by norm_num) hSm j k
  have hentry : ∀ j k, ∀ᵐ x ∂volume.restrict (ball z (1 / 4)),
      |(T x - b) j k| ≤ B * (1 + U + V) := by
    intro j k
    filter_upwards [hT j k z c (b j k)] with x hx
    change _ ≤ B * (_ + 1 + U) at hx
    have hr := hroot j k
    change Real.sqrt (∫ x in ball z 1,
      |(r₀ / ellipticityScale L) * S.potential
        (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x) j k - b j k| ^ 2
          ∂volume) ≤ V at hr
    exact hx.trans (mul_le_mul_of_nonneg_left (by linarith) hB.le)
  have hscalar := ae_restrict_of_ae_restrict_of_subset
    (show ball z (1 / 4) ⊆ ball z 1 from fun x hx =>
      (show euclideanNorm (x - z) < 1 / 4 from hx).trans (by norm_num)) (hu z c)
  filter_upwards [hscalar, ae_all_iff.mpr (fun j => ae_all_iff.mpr (hentry j))] with x hx hxx
  change _ ≤ (A + ((d : ℝ) + 1) * B) * (1 + U + V) ∧
    _ ≤ (A + ((d : ℝ) + 1) * B) * (1 + U + V)
  have hN : 0 ≤ 1 + U + V := by positivity
  constructor
  · change |u x - c| ≤ A * (1 + U) at hx
    apply hx.trans
    exact (mul_le_mul_of_nonneg_left (by linarith : 1 + U ≤ 1 + U + V) hA.le).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity) : A ≤ A + ((d : ℝ) + 1) * B) hN)
  · apply (frobeniusNorm_le_dimension_mul (T x - b) (B * (1 + U + V))
      (by positivity) hxx).trans
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (by nlinarith : (d : ℝ) * B ≤ A + ((d : ℝ) + 1) * B) hN
end EinsteinRelation.Correctors
