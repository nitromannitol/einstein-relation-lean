import EinsteinRelation.Correctors.CenteredGaugeInvariance
import EinsteinRelation.Correctors.SpatialWeakLocalization
import EinsteinRelation.Correctors.PairedPDEBallNormalization
import EinsteinRelation.Correctors.ScalarPotentialApproxRestriction

/-! # Centered scalar moments do not depend on normalization scale

Source: `paper/main.tex:715–722,762–766`. Two normalized canonical scalar
potentials have the same weak gradient. Their centered values agree on
every positive Euclidean ball, including when their normalizations differ.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM NormalizedSpatialRepresentativeSupport
open NormalizedScalarPhysicalLawTransportSupport

/-- Centering on a ball removes the almost-sure additive difference
between arbitrary normalizations of the canonical scalar potential.
Source: `paper/main.tex:715–722,762–766`. -/
theorem ae_centered_normalizedCanonicalScalar_eq
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ R T : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (ζ η : SourceMollifier d) (hR : 1 ≤ R) (hT : 1 ≤ T)
    (y z : Point d) (u v : FieldPair d → Vec d → ℝ)
    (hu : IsNormalizedCanonicalScalarCorrector Q i ζ R hR y (fun ω x => u ω x.ofLp))
    (hv : IsNormalizedCanonicalScalarCorrector Q i η T hT z (fun ω x => v ω x.ofLp))
    (r : ℝ) (hr : 0 < r) :
    ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      (fun x => u ω x - ⨍ a in ball (0 : Vec d) r, u ω a ∂volume) =ᵐ[
          volume.restrict (ball (0 : Vec d) r)]
        (fun x => v ω x - ⨍ a in ball (0 : Vec d) r, v ω a ∂volume) := by
  have hd : 0 < d := by have := (Fact.out : 2 ≤ d); omega
  have hvol := ENNReal.toReal_pos_iff.mp (paired_ball_volume_pos_finite (d := d) hr)
  let μ := volume.restrict (ball (0 : Vec d) r)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hvol.2.ne
  letI : NeZero μ := ⟨by
    intro h
    have hh : μ Set.univ = 0 := by rw [h]; simp
    exact hvol.1.ne' (by simpa only [μ, Measure.restrict_apply_univ] using hh)⟩
  filter_upwards [hu.2, hv.2] with ω hω hω'
  obtain ⟨_, hGu, _⟩ := hω
  obtain ⟨_, hGv, _⟩ := hω'
  obtain ⟨c, hc⟩ := weakPotentials_differ_by_constant hd hGu hGv
  have hvi : Integrable (v ω) μ :=
    ((locallyIntegrableOn_univ.mp (hGv ⟨0, hd⟩).1).integrableOn_isCompact
      (isCompact_closedBall (0 : Vec d) r)).mono_set
        (ScalarPotentialApproximation.euclideanBall_subset_coordinateClosedBall r hr.le)
  exact centered_scalar_ae_eq_of_gauge μ hvi c (ae_restrict_of_ae hc)

end EinsteinRelation.Correctors
