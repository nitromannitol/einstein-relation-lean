import EinsteinRelation.Correctors.AKMPhysicalFluxLocalBound
import EinsteinRelation.Correctors.SpatialBallLocalL2Support
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3
/-- Source: `paper/main.tex:733-745`. The physical raw tensor has
entrywise local L² data on every ball, with no extra input. -/
theorem ae_physicalAKMFlux_memLp_on_balls {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (halfDirection i))
    (S : FluxCorrector (scaledAKMCorrector φ 2)) :
    ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ (z : Vec d) (R : ℝ), 0 < R → ∀ j k,
      MemLp (fun x => (r₀ / ellipticityScale L) * S.potential
        (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x) j k) 2
        (volume.restrict (ball z R)) := by
  have hr : 0 < r₀ := zero_lt_one.trans_le Q.range_parameter
  filter_upwards [(measurePreserving_akmProject Q).quasiMeasurePreserving.ae
    S.locally_square_integrable] with ω hl
  intro z R hR j k
  exact memLp_on_euclideanBall_of_origin_balls _
    (memLp_two_on_euclidean_balls_dilation _
      (fun t ht => (hl t ht j k).1) r₀⁻¹ (r₀ / ellipticityScale L) (inv_pos.mpr hr)) z R hR
/-- Source: `paper/main.tex:733-745`. Joint measurability of the physical
raw tensor follows from the source tensor's actual measurable potential. -/
theorem measurable_physicalAKMFlux_potential {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (halfDirection i))
    (S : FluxCorrector (scaledAKMCorrector φ 2)) :
    Measurable (fun q : PhysicalField d L × Vec d =>
      (r₀ / ellipticityScale L) • S.potential
        (project (r₀ := r₀) Q.ellipticity_parameter q.1) (r₀⁻¹ • q.2)) := by
  exact (S.measurable_potential.comp
    (((measurePreserving_akmProject Q).measurable.comp measurable_fst).prodMk
      (measurable_const.smul measurable_snd))).const_smul (r₀ / ellipticityScale L)
end EinsteinRelation.Correctors
