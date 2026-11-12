import EinsteinRelation.Correctors.StationaryLocalFluxAssembly
import EinsteinRelation.Correctors.LocalFluxMeasurability
import EinsteinRelation.Correctors.LocalGradientRate
import EinsteinRelation.Correctors.LocalFluxRate
import EinsteinRelation.Correctors.CoordinateMomentProjections
import EinsteinRelation.Correctors.EuclideanCoordinateMoments
import EinsteinRelation.Mobility.VelocityResolventRate

/-! # Assembling the local corrector from its spatial fields

Source: `paper/main.tex:921–938,968–977`. The gradient is the sum of the
conditional-gradient average and the derivative correction. The error is
literally `a(0) H - K`. Spatial equations and separate moment estimates imply
the production horizontal construction. The hypotheses here are internal
construction obligations, not additional literature inputs.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors

/-- The five spatial averages in `paper/main.tex:921–938`, before forming
the local gradient and flux error. This structure contains only fields. -/
structure LocalCorrectorFields (d : ℕ) where
  scalar : FieldPair d → ℝ
  skew : FieldPair d → Mat d
  gradientAverage : FieldPair d → Vec d
  scalarCorrection : FieldPair d → Vec d
  skewCorrection : FieldPair d → Vec d

namespace LocalCorrectorFields

/-- The actual local gradient, `paper/main.tex:931–938`. -/
def gradient {d : ℕ} (f : LocalCorrectorFields d) : FieldPair d → Vec d :=
  f.gradientAverage + f.scalarCorrection

/-- The actual flux error, `paper/main.tex:921–938`. -/
def flux {d : ℕ} (f : LocalCorrectorFields d) : FieldPair d → Vec d :=
  fun ω => (ω.1 0).mulVec (f.scalarCorrection ω) - f.skewCorrection ω

/-- The two separate correction estimates and the conditional-gradient
estimate give the joint inverse-radius error. Source: `paper/main.tex:968–977`. -/
theorem error_rate {d : ℕ} (hd : 2 ≤ d) {L r₀ R p A B D : ℝ}
    (Q : EnvironmentLaw d L r₀) (f : LocalCorrectorFields d)
    (g : FieldPair d → Vec d) (hgm : Measurable g)
    (hp : 1 ≤ p) (hR : 1 ≤ R) (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hVm : Measurable f.gradientAverage) (hHm : Measurable f.scalarCorrection)
    (hKm : Measurable f.skewCorrection)
    (hV : eLpNorm (fun ω => euclideanNorm (f.gradientAverage ω - g ω))
      (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤
        ENNReal.ofReal (2 * (A * R ^ (-(d : ℝ) / 2))))
    (hH : eLpNorm (fun ω => euclideanNorm (f.scalarCorrection ω))
      (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal (B * R⁻¹))
    (hK : eLpNorm (fun ω => euclideanNorm (f.skewCorrection ω))
      (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal (D * R⁻¹)) :
    eLpNorm (fun ω => euclideanNorm (f.flux ω))
        (ENNReal.ofReal p) (reducedEnvironmentLaw Q) +
      eLpNorm (fun ω => euclideanNorm (f.gradient ω - g ω))
        (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤
      ENNReal.ofReal (((Real.exp (2 * L) * L) * B + D + (2 * A + B)) * R⁻¹) := by
  have hF := eLpNorm_local_flux_error_rate_le Q hp hR hB hD hHm hKm hH hK
  have hG := eLpNorm_corrected_local_gradient_rate_le hd hp hR hA hB hVm hHm hgm hV hH
  have hL : 0 ≤ Real.exp (2 * L) * L :=
    mul_nonneg (Real.exp_pos _).le (zero_le_one.trans Q.ellipticity_parameter)
  calc
    _ ≤ ENNReal.ofReal (((Real.exp (2 * L) * L) * B + D) * R⁻¹) +
        ENNReal.ofReal ((2 * A + B) * R⁻¹) := add_le_add hF hG
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

/-- Spatial local-flux equations give the horizontal equations. Finite
scalar, Frobenius, gradient-error and correction moments suffice to derive
all square-integrability premises. Source: `paper/main.tex:926–938`. -/
theorem horizontal_equations {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) (f : LocalCorrectorFields d)
    (hφm : Measurable f.scalar) (hSm : Measurable f.skew)
    (hVm : Measurable f.gradientAverage) (hHm : Measurable f.scalarCorrection)
    (hFm : Measurable f.flux)
    (hφ : eLpNorm f.scalar 2 (reducedEnvironmentLaw Q) < ⊤)
    (hS : eLpNorm (fun ω => frobeniusNorm (f.skew ω)) 2
      (reducedEnvironmentLaw Q) < ⊤)
    (hG : eLpNorm (fun ω => euclideanNorm (f.gradient ω -
      ((canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
        (reducedEnvironmentLaw Q)) ω).ofLp)) 2 (reducedEnvironmentLaw Q) < ⊤)
    (hF : eLpNorm (fun ω => euclideanNorm (f.flux ω)) 2 (reducedEnvironmentLaw Q) < ⊤)
    (hspatial : ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      HasWeakGradient Set.univ (orbit f.scalar ω)
        (fun x => f.gradient (translate x ω)) ∧
      HasWeakRowDivergence Set.univ (fun x => f.skew (translate x ω))
        (fun x => (ω.1 x).mulVec (unitVector i + f.gradient (translate x ω)) -
          (expectedCorrectorFlux Q i).ofLp - f.flux (translate x ω))) :
    HasWeakHorizontalGradient (reducedEnvironmentLaw Q)
      (reducedEnvironmentLaw_stationary Q) f.scalar f.gradient ∧
    ∀ j, HasWeakHorizontalDivergence (reducedEnvironmentLaw Q)
      (reducedEnvironmentLaw_stationary Q) (fun ω k => f.skew ω j k)
      (fun ω => (∑ k, (ω.1 0) j k * (unitVector i k + f.gradient ω k)) -
        (expectedCorrectorFlux Q i).ofLp j - f.flux ω j) := by
  have hGm : Measurable f.gradient := hVm.add hHm
  have hg : Measurable (fun ω =>
      ((canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
        (reducedEnvironmentLaw Q)) ω).ofLp) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).continuous.measurable.comp
      (Lp.stronglyMeasurable _).measurable
  have hG2 (j : Fin d) : MemLp (fun ω => f.gradient ω j) 2 (reducedEnvironmentLaw Q) := by
    have hdiff : MemLp (fun ω => f.gradient ω j -
        ((canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
          (reducedEnvironmentLaw Q)) ω).ofLp j) 2 (reducedEnvironmentLaw Q) :=
      ⟨((measurable_pi_apply j).comp (hGm.sub hg)).aestronglyMeasurable,
        (eLpNorm_coordinate_le (μ := reducedEnvironmentLaw Q) (p := 2)
          (fun ω => f.gradient ω - ((canonicalCorrectorGradient Q i :
            Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) ω).ofLp) j).trans_lt hG⟩
    have hcanon := (memLp_euclidean_coordinate (reducedEnvironmentLaw Q)
      (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
      (Lp.memLp _) j).1
    have heq : ((fun ω => f.gradient ω j -
        ((canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
          (reducedEnvironmentLaw Q)) ω).ofLp j) +
        (fun ω => ((canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
          (reducedEnvironmentLaw Q)) ω).ofLp j)) = (fun ω => f.gradient ω j) := by
      funext ω
      exact sub_add_cancel _ _
    exact heq ▸ hdiff.add hcanon
  apply stationary_localFlux_equations Q i f.scalar f.skew f.gradient f.flux
    hφm hSm hGm hFm ⟨hφm.aestronglyMeasurable, hφ⟩
  · intro j k
    exact ⟨((continuous_id.matrix_elem j k).measurable.comp hSm).aestronglyMeasurable,
      (eLpNorm_entry_le f.skew j k).trans_lt hS⟩
  · exact hG2
  · intro j
    exact ⟨((measurable_pi_apply j).comp hFm).aestronglyMeasurable,
      (eLpNorm_coordinate_le f.flux j).trans_lt hF⟩
  · exact hspatial

end LocalCorrectorFields

end EinsteinRelation.Correctors
