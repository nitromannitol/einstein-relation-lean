import EinsteinRelation.Correctors.AKMJointStationaryBallMoments
import EinsteinRelation.Correctors.PhysicalLocalL2Moments

/-!
# Physical stationary local L² bounds

Source: `paper/main.tex:724-731`, the `d > 2` case of
`eq.corrector-unit-L2`. The scalar and tensor source representatives
are chosen jointly. Their physical amplitudes are respectively `2r₀`
and `r₀ / ellipticityScale L`; the latter is the amplitude whose
derivative has the canonical centered-flux normalization.
-/
open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3
open NormalizedScalarPhysicalLawTransportSupport
open NormalizedSpatialRepresentativeSupport

/-- The high-dimensional radius-four L² estimate on the actual physical
law, uniformly over every local center. The scalar source remains
identified with every normalized canonical scalar representative.
This statement does not assert the unproved physical heat-selection
property of the rescaled flux potential. -/
theorem exists_physical_stationary_local_L2_moments
    (h45 : ScalarStationaryEstimate) (h68 : FluxGradientEstimate)
    (h614 : FluxStationaryEstimate)
    (hP : External.GilbargTrudinger.BallPoincareEstimate)
    (d : ℕ) [Fact (2 ≤ d)] (hd : 2 < d) (L r₀ p : ℝ)
    (hL : 1 ≤ L) (hr₀ : 1 ≤ r₀) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : EnvironmentLaw d L r₀) (i : Fin d),
      ∃ ψ : Corrector (actualCoefficientLaw Q) (halfDirection i),
        ∃ S : FluxCorrector (scaledAKMCorrector ψ 2),
          (∀ (ζ : SourceMollifier d) (R : ℝ) (hR : 1 ≤ R) (y : Point d)
            (φ : FieldPair d → Point d → ℝ),
            IsNormalizedCanonicalScalarCorrector Q i ζ R hR y φ →
            ∀ᵐ ω ∂physicalReferenceLaw Q, ∃ c : ℝ,
              (fun x : Vec d => φ (reduce ω.1) (WithLp.toLp 2 x)) =ᵐ[volume]
                (fun x => (2 * r₀) * ψ.potential
                  (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x) + c)) ∧
          ∀ z : Vec d,
            (∫⁻ ω, ENNReal.ofReal ((Real.sqrt (∫ x in ball z 4,
              |(2 * r₀) * ψ.potential
                (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x)| ^ 2
                ∂volume)) ^ p) ∂physicalReferenceLaw Q) ≤ ENNReal.ofReal C ∧
            (∫⁻ ω, ENNReal.ofReal ((Real.sqrt (∫ x in ball z 4,
              frobeniusNorm ((r₀ / ellipticityScale L) • S.potential
                (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x)) ^ 2
                ∂volume)) ^ p) ∂physicalReferenceLaw Q) ≤ ENNReal.ofReal C := by
  obtain ⟨C₀, hC₀, hest⟩ := exists_joint_stationary_akm_ball_four_moments
    h45 h68 h614 hP d hd L r₀ p hL hp
  let A : ℝ := (Real.sqrt ((2 * r₀) ^ 2 * r₀ ^ d)) ^ p
  let B : ℝ := (Real.sqrt ((r₀ / ellipticityScale L) ^ 2 * r₀ ^ d)) ^ p
  have hA : 0 ≤ A := Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hB : 0 ≤ B := Real.rpow_nonneg (Real.sqrt_nonneg _) _
  refine ⟨(A + B + 1) * C₀, mul_pos (by linarith) hC₀, ?_⟩
  intro Q i
  obtain ⟨ψ, S, hm, _, _, _, _, hbφ, hbS, hgauge⟩ := hest Q i
  have hu : ∀ᵐ a ∂actualCoefficientLaw Q, ∀ R : ℝ, 0 < R →
      MemLp (ψ.potential a) 2 (volume.restrict (ball 0 R)) :=
    ψ.locally_square_integrable.mono fun a ha R hR => (ha R hR).1
  have hS : ∀ᵐ a ∂actualCoefficientLaw Q, ∀ R : ℝ, 0 < R → ∀ j k,
      MemLp (fun x => S.potential a x j k) 2 (volume.restrict (ball 0 R)) :=
    S.locally_square_integrable.mono fun a ha R hR j k => (ha R hR j k).1
  refine ⟨ψ, S, hgauge, ?_⟩
  intro z
  constructor
  · have h := scalar_local_L2_moment_measurePreserving_inv_dilation
      (measurePreserving_akmProject Q) ψ.potential hm hu r₀ (2 * r₀) 4 p hr₀
      (by norm_num) (by linarith) (ENNReal.ofReal C₀) hbφ z
    apply h.trans
    rw [← ENNReal.ofReal_mul hA]
    exact ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (by linarith) hC₀.le)
  · have h := flux_local_L2_moment_measurePreserving_inv_dilation
      (measurePreserving_akmProject Q) S.potential S.measurable_potential hS
      r₀ (r₀ / ellipticityScale L) 4 p hr₀ (by norm_num) (by linarith)
      (ENNReal.ofReal C₀) hbS z
    apply h.trans
    rw [← ENNReal.ofReal_mul hB]
    exact ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (by linarith) hC₀.le)

end EinsteinRelation.Correctors
