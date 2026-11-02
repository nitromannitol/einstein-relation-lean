import EinsteinRelation.External.AKMCorrectorOscillation
import EinsteinRelation.Correctors.SpatialWeakDilation
import EinsteinRelation.Correctors.SublinearOscillationDilation

/-!
# Direction homogeneity of the raw scalar corrector

Source: `paper/main.tex:716,727-729`. The scalar estimates use directions
in the open unit ball, whereas the flux estimates use unit directions.
The change of direction scales the actual scalar potential and gradient,
including their weak equation, sublinearity, and expected cell flux.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

private theorem weakDivergence_zero_const_smul {d : ℕ}
    {F : Vec d → Vec d} (h : HasWeakDivergence Set.univ F (fun _ => 0)) (c : ℝ) :
    HasWeakDivergence Set.univ (fun x => c • F x) (fun _ => 0) := by
  refine ⟨fun j x hx => ?_, locallyIntegrableOn_zero, ?_⟩
  · exact (h.1 j x hx).smul c
  · intro η hη
    have hdot (x : Vec d) : dot (c • F x) (gradient η x) =
        c * dot (F x) (gradient η x) := by
      simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    simpa only [hdot, integral_const_mul, zero_mul, integral_zero, neg_zero, mul_zero]
      using congrArg (fun v : ℝ => c * v) (h.2.2 η hη)

/-- The actual raw corrector after multiplying its direction by a scalar. -/
def scaledAKMCorrector {d : ℕ} {K : ℝ} {P : Measure (Coefficient d K)}
    {e : Vec d} (φ : Corrector P e) (c : ℝ) : Corrector P (c • e) where
  potential a x := c * φ.potential a x
  grad a x := c • φ.grad a x
  measurable_grad := φ.measurable_grad.const_smul c
  weak_gradient := by
    filter_upwards [φ.weak_gradient, φ.locally_square_integrable] with a ha hl
    simpa only [one_smul, mul_one] using
      hasWeakGradient_dilation (φ.potential a) (φ.grad a)
        (fun R hR => (hl R hR).1) (fun R hR => (hl R hR).2) ha 1 c zero_lt_one
  locally_square_integrable := by
    filter_upwards [φ.locally_square_integrable] with a ha R hR
    exact ⟨(ha R hR).1.const_smul c, (ha R hR).2.const_smul c⟩
  stationary := by
    intro z
    filter_upwards [φ.stationary z] with a ha
    filter_upwards [ha] with x hx
    rw [hx]
  harmonic := by
    filter_upwards [φ.harmonic] with a ha
    have hflux : (fun x => (a x).mulVec (c • e + c • φ.grad a x)) =
        (fun x => c • (a x).mulVec (e + φ.grad a x)) := by
      funext x
      rw [← smul_add, Matrix.mulVec_smul]
    rw [hflux]
    exact weakDivergence_zero_const_smul ha c
  sublinear := by
    filter_upwards [φ.sublinear, φ.locally_square_integrable] with a ha hl
    simpa only [one_smul] using
      sublinear_oscillation_dilation (φ.potential a)
        (fun R hR => (hl R hR).1) ha 1 c zero_lt_one
  cell_integrable := by
    have hflux : (fun a : Coefficient d K =>
        ∫ x in unitCell d, (a x).mulVec (c • e + c • φ.grad a x) ∂volume) =
        (fun a => c • ∫ x in unitCell d, (a x).mulVec (e + φ.grad a x) ∂volume) := by
      funext a
      simp_rw [← smul_add, Matrix.mulVec_smul, integral_smul]
    rw [hflux]
    exact φ.cell_integrable.smul c

/-- The expected cell flux scales with the direction, on the same coefficient law. -/
theorem meanFlux_scaledAKMCorrector {d : ℕ} {K : ℝ} {P : Measure (Coefficient d K)}
    {e : Vec d} (φ : Corrector P e) (c : ℝ) :
    meanFlux (scaledAKMCorrector φ c) = c • meanFlux φ := by
  simp only [meanFlux, scaledAKMCorrector, ← smul_add, Matrix.mulVec_smul, integral_smul]

/-- Centering commutes with the direction normalization used for the flux inputs. -/
theorem centeredFlux_scaledAKMCorrector {d : ℕ} {K : ℝ}
    {P : Measure (Coefficient d K)} {e : Vec d} (φ : Corrector P e) (c : ℝ)
    (a : Coefficient d K) (x : Vec d) :
    centeredFlux (scaledAKMCorrector φ c) a x = c • centeredFlux φ a x := by
  unfold centeredFlux
  rw [meanFlux_scaledAKMCorrector]
  simp only [scaledAKMCorrector, ← smul_add, Matrix.mulVec_smul, smul_sub]

end EinsteinRelation.Correctors
