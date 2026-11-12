import EinsteinRelation.Correctors.AKMPhysicalPlanarLocalMoments
import EinsteinRelation.Correctors.AKMPhysicalStationaryLocalMoments

/-! Source: `paper/main.tex:718-731`. The frozen AKM estimates give
local scalar L² data in both dimensions, retaining the canonical gradient
identity required by the repaired GT proof. -/
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3

/-- Scalar radius-four oscillation moments with a physical canonical
gradient, uniformly before the law and direction. The scalar gauge is
chosen from the actual AKM potential. -/
theorem exists_physical_scalar_local_L2_data
    (h45 : ScalarStationaryEstimate) (h46 : ScalarPlanarL2Estimate)
    (h68 : FluxGradientEstimate) (h614 : FluxStationaryEstimate)
    (h615 : FluxPlanarL2Estimate)
    (hP : External.GilbargTrudinger.BallPoincareEstimate)
    (d : ℕ) [Fact (2 ≤ d)] (L r₀ p : ℝ)
    (hL : 1 ≤ L) (hr₀ : 1 ≤ r₀) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : EnvironmentLaw d L r₀) (i : Fin d),
      ∃ φ : Corrector (actualCoefficientLaw Q) (halfDirection i),
        ∃ c : PhysicalField d L → ℝ,
          (∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
            (2 : ℝ) • (halfDirection i + φ.grad
              (project (r₀ := r₀) Q.ellipticity_parameter ω) y) =
            (correctorUnitVector i + (canonicalCorrectorGradient Q i :
              Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
                (translate (r₀ • y) (reduce ω.1))).ofLp) ∧
          (∫⁻ ω, ENNReal.ofReal ((Real.sqrt (∫ x in ball 0 4,
            |(2 * r₀) * φ.potential
              (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x) - c ω| ^ 2
                ∂volume)) ^ p) ∂physicalReferenceLaw Q) ≤ ENNReal.ofReal C := by
  by_cases hd : d = 2
  · subst d
    obtain ⟨C, hC, hest⟩ := exists_physical_planar_local_L2_moments
      h46 h68 h615 hP L r₀ p hL hr₀ (by linarith)
    refine ⟨C, hC, ?_⟩
    intro Q i
    obtain ⟨φ, S, hid, hm⟩ := hest Q i
    exact ⟨φ, (fun ω => scalarHeatAverage (fun x => (2 * r₀) * φ.potential
      (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x)) 0 (r₀ * 4)),
      hid, (hm 0).1⟩
  · have hd' : 2 < d := by have := (Fact.out : 2 ≤ d); omega
    obtain ⟨C₀, hC₀, hest⟩ := exists_joint_stationary_akm_ball_four_moments
      h45 h68 h614 hP d hd' L r₀ p hL hp
    let A := (Real.sqrt ((2 * r₀) ^ 2 * r₀ ^ d)) ^ p
    have hA : 0 < A := by
      have hr : 0 < r₀ := by linarith
      dsimp [A]
      positivity
    refine ⟨A * C₀, mul_pos hA hC₀, ?_⟩
    intro Q i
    obtain ⟨φ, S, hm, _, hid, _, _, hb, _, _⟩ := hest Q i
    have hu : ∀ᵐ a ∂actualCoefficientLaw Q, ∀ R : ℝ, 0 < R →
        MemLp (φ.potential a) 2 (volume.restrict (ball 0 R)) :=
      φ.locally_square_integrable.mono fun a ha R hR => (ha R hR).1
    refine ⟨φ, (fun _ => 0), hid, ?_⟩
    have h := scalar_local_L2_moment_measurePreserving_inv_dilation
      (measurePreserving_akmProject Q) φ.potential hm hu r₀ (2 * r₀) 4 p hr₀
      le_rfl (by linarith) (ENNReal.ofReal C₀) hb 0
    simpa only [sub_zero, A, ENNReal.ofReal_mul hA.le] using h

end EinsteinRelation.Correctors
