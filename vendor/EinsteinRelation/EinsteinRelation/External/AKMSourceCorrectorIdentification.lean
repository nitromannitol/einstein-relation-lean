import EinsteinRelation.External.AKMEnergyDensitySources
import EinsteinRelation.Correctors.SublinearCorrectorDifference
import EinsteinRelation.Correctors.WeakCorrectorDifference
import EinsteinRelation.Correctors.ZeroOscillationGradient

/-!
# Identification of characterized source corrector gradients

Source: `paper/main.tex:693-698,727-729`; AKM Theorem 3.3, (3.17),
p. 75, applied to the difference of two affine-corrector potentials.
The outer-radius limit uses their centered sublinear oscillations. No
corrector uniqueness is assumed.
-/

open MeasureTheory Filter Topology
noncomputable section
namespace EinsteinRelation.External.AKM
open Environment.AKMTestIntegralSupport Correctors

/-- Forget the centered-cell integrability field; retain the actual potential,
gradient and all source corrector characterizations. -/
def Corrector.toSourceCorrector {d : ℕ} {K : ℝ} {P : Measure (Coefficient d K)}
    {e : Vec d} (φ : Corrector P e) : SourceCorrector P e where
  potential := φ.potential
  grad := φ.grad
  measurable_grad := φ.measurable_grad
  weak_gradient := φ.weak_gradient
  locally_square_integrable := φ.locally_square_integrable
  stationary := φ.stationary
  harmonic := φ.harmonic
  sublinear := φ.sublinear

/-- Two source-characterized affine correctors have the same gradient.
This is the identification required before applying the published energy
estimate to an arbitrary `Corrector`. -/
theorem SourceCorrector.grad_ae_eq
    (h33 : LargeScaleOscillationEstimate) {d : ℕ} (hd : 2 ≤ d)
    {K : ℝ} (hK : 1 < K) {P : Measure (Coefficient d K)}
    (hP : LawHypotheses P) {e : Vec d} (φ ψ : SourceCorrector P e) :
    ∀ᵐ a ∂P, φ.grad a =ᵐ[volume] ψ.grad a := by
  filter_upwards [ae_sublinear_harmonic_zero_oscillation h33 d hd K hK P hP,
    φ.weak_gradient, ψ.weak_gradient, φ.locally_square_integrable,
    ψ.locally_square_integrable, φ.harmonic, ψ.harmonic, φ.sublinear, ψ.sublinear]
    with a ha hφw hψw hφl hψl hφh hψh hφs hψs
  obtain ⟨X, hX, hosc⟩ := ha
  have hdif := affine_corrector_difference_weakSolution a e (φ.potential a)
    (ψ.potential a) (φ.grad a) (ψ.grad a) hφw hψw
    (fun R hR => (hφl R hR).1) (fun R hR => (hψl R hR).1)
    (fun R hR => (hφl R hR).2) (fun R hR => (hψl R hR).2) hφh hψh
  have hsub := sublinear_centered_oscillation_sub (φ.potential a) (ψ.potential a)
    (fun R hR => (hφl R hR).1) (fun R hR => (hψl R hR).1) hφs hψs
  have hz := weakGradient_zero_of_large_ball_zero_oscillation
    (fun x => φ.potential a x - ψ.potential a x)
    (fun x => φ.grad a x - ψ.grad a x) hdif.1
    (fun R hR => (hφl R hR).1.sub (hψl R hR).1) X
    (zero_lt_one.trans_le hX) (hosc _ _ hdif.2 hsub)
  filter_upwards [hz] with x hx
  exact sub_eq_zero.mp hx

end EinsteinRelation.External.AKM
