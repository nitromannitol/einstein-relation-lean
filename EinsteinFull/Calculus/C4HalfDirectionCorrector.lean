import EinsteinRelation.Correctors.AKMEnergyTransfer
import EinsteinRelation.Correctors.AKMCorrectorDirectionScaling

/-!
The canonical scalar producer uses half a coordinate direction. Reuse the
existing linear construction to normalize its actual scalar corrector
on the same coefficient law, without changing their representatives.
-/

open MeasureTheory

noncomputable section
namespace EinsteinFull.Calculus.C4HalfDirectionCorrector

open EinsteinRelation EinsteinRelation.Correctors EinsteinRelation.External.AKM
open EinsteinRelation.Environment.AKMTestIntegralSupport

/-- Doubling the source half-direction gives the Euclidean coordinate vector. -/
theorem two_smul_halfDirection {d : ℕ} (i : Fin d) :
    (2 : ℝ) • halfDirection i = (correctorUnitVector i).ofLp := by
  simp only [halfDirection, smul_smul, correctorUnitVector, WithLp.ofLp_toLp]
  norm_num [unitVector]

/-- The direction used after normalization has Euclidean norm one. -/
theorem euclideanNorm_correctorUnitVector {d : ℕ} (i : Fin d) :
    euclideanNorm (correctorUnitVector i).ofLp = 1 := by
  simp [correctorUnitVector, euclideanNorm, euclideanSq, dot, mul_ite]

/-- The doubled concrete scalar corrector, retaining every characterization field. -/
def doubledCorrector {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
    (i : Fin d) (φ : Corrector (actualCoefficientLaw Q) (halfDirection i)) :
    Corrector (actualCoefficientLaw Q) (correctorUnitVector i).ofLp where
  potential := (scaledAKMCorrector φ 2).potential
  grad := (scaledAKMCorrector φ 2).grad
  measurable_grad := (scaledAKMCorrector φ 2).measurable_grad
  weak_gradient := (scaledAKMCorrector φ 2).weak_gradient
  locally_square_integrable := (scaledAKMCorrector φ 2).locally_square_integrable
  stationary := (scaledAKMCorrector φ 2).stationary
  harmonic := by
    simpa only [two_smul_halfDirection] using (scaledAKMCorrector φ 2).harmonic
  sublinear := (scaledAKMCorrector φ 2).sublinear
  cell_integrable := by
    simpa only [two_smul_halfDirection] using (scaledAKMCorrector φ 2).cell_integrable

/-- The scalar potential is literally doubled. -/
theorem doubledCorrector_potential {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
    (i : Fin d) (φ : Corrector (actualCoefficientLaw Q) (halfDirection i))
    (a : Coefficient d (AKMUpperEllipticity L)) (x : Vec d) :
    (doubledCorrector Q i φ).potential a x = 2 * φ.potential a x := rfl

/-- The scalar gradient is literally doubled. -/
theorem doubledCorrector_grad {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
    (i : Fin d) (φ : Corrector (actualCoefficientLaw Q) (halfDirection i))
    (a : Coefficient d (AKMUpperEllipticity L)) (x : Vec d) :
    (doubledCorrector Q i φ).grad a x = (2 : ℝ) • φ.grad a x := rfl

/-- Centering the flux commutes with the concrete normalization. -/
theorem centeredFlux_doubledCorrector {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
    (i : Fin d) (φ : Corrector (actualCoefficientLaw Q) (halfDirection i))
    (a : Coefficient d (AKMUpperEllipticity L)) (x : Vec d) :
    centeredFlux (doubledCorrector Q i φ) a x = (2 : ℝ) • centeredFlux φ a x := by
  have h := centeredFlux_scaledAKMCorrector φ 2 a x
  simpa only [centeredFlux, meanFlux, scaledAKMCorrector, doubledCorrector,
    two_smul_halfDirection] using h

end EinsteinFull.Calculus.C4HalfDirectionCorrector
