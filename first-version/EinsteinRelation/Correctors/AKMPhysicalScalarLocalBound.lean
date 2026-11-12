import EinsteinRelation.Correctors.ScalarLocalBound
import EinsteinRelation.Correctors.LocalRootIntegralMonotonicity
import EinsteinRelation.Correctors.AKMPhysicalScalarSobolev
import EinsteinRelation.Correctors.GTFourBallCoefficientSupport
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger
open Environment.AKMTestIntegralSupport ReductionImageV3
/-- Source: `paper/main.tex:727-735`. The physical scalar value is
controlled on every unit ball by the actual physical scalar oscillation. -/
theorem ae_physicalAKMScalar_local_bound_of_GT
    (h817 : LocalBoundednessEstimate)
    (d : ℕ) [Fact (2 ≤ d)] (L : ℝ) (hL : 1 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ {r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
      (φ : Corrector (actualCoefficientLaw Q) (halfDirection i)),
      (∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
        (2 : ℝ) • (halfDirection i + φ.grad
          (project (r₀ := r₀) Q.ellipticity_parameter ω) y) =
        (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate (r₀ • y) (reduce ω.1))).ofLp) →
      ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ (z : Vec d) (c : ℝ),
        ∀ᵐ x ∂volume.restrict (ball z 1),
          |(2 * r₀) * φ.potential
            (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x) - c| ≤ C * (1 + Real.sqrt
                (∫ x in ball z 4, |(2 * r₀) * φ.potential
                  (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x) - c| ^ 2
                  ∂volume)) := by
  have hB : 0 < sourceReducedBound L := by unfold sourceReducedBound; positivity
  have hΛ : 0 < ((d : ℝ) + 1) * sourceReducedBound L := by positivity
  obtain ⟨C, hC, hlocal⟩ := scalar_corrector_local_bound_of_GT
    h817 d (Fact.out : 2 ≤ d) (sourceReducedBound L)⁻¹
    (((d : ℝ) + 1) * sourceReducedBound L) (inv_pos.mpr hB) hΛ
  refine ⟨C, hC, ?_⟩
  intro r₀ Q i φ hid
  have hc := (measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae
    (reduced_gt_coefficient_hypotheses_ball_four Q)
  filter_upwards [hc, ae_physicalAKMPotential_affine_weakSolution Q i φ hid] with ω hcoeff hw
  intro z c
  have h24 : ball z 2 ⊆ ball z 4 := fun x hx =>
    (show euclideanNorm (x - z) < 2 from hx).trans (by norm_num)
  have ha2 : EllipticBound (ball z 2) (reduce ω.1).1
      (sourceReducedBound L)⁻¹ (((d : ℝ) + 1) * sourceReducedBound L) :=
    ⟨(hcoeff z).1.1, fun x hx => (hcoeff z).1.2 x (h24 hx)⟩
  have h := hlocal (reduce ω.1).1 z ha2
    (fun x => (2 * r₀) * φ.potential
      (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x))
    (fun x => ((canonicalCorrectorGradient Q i :
      Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
        (translate x (reduce ω.1))).ofLp)
    i c (hw z 2 (by norm_num) c).1 (hw z 2 (by norm_num) c).2
  have hroot := sqrt_setIntegral_euclideanBall_mono
    (fun x => |(2 * r₀) * φ.potential
      (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x) - c| ^ 2)
    z 2 4 (by norm_num)
    (by simpa only [sq_abs] using (hw z 4 (by norm_num) c).1.integrable_sq)
    (fun _ => sq_nonneg _)
  filter_upwards [h] with x hx
  exact hx.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hroot) hC.le)
end EinsteinRelation.Correctors
