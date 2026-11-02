import EinsteinFull.Calculus.C4GaussianCoefficientRowWeakProduct
import EinsteinFull.Blueprint.G3.Proofs.W4Queue0420_1
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation
/-- The first Gaussian derivative of the actual row flux, with ordered kernel derivatives. -/
theorem gaussian_derivative_coefficient_row_weak_product
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (hβ : IsReducedDriftObservation Q hQ β)
    (u : Lp ℂ 2 (reducedLaw Q)) (G : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) u G)
    (l : Fin d) (H R : Lp ℂ 2 (reducedLaw Q))
    (hH : (H : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      fun ω => ∑ k : Fin d, (ω.1 0 l k : ℂ) * G k ω)
    (hR : (R : FieldPair d → ℂ) =ᵐ[reducedLaw Q] fun ω => β l ω * u ω)
    (i : Fin d) (s : ℝ) (hs : 0 < s) :
    gaussianDerivativeAverage hd Q s hs 1 (fun _ => i) H =
      (∑ k : Fin d, gaussianDerivativeAverage hd Q s hs 2 (fun n => if n = 0 then i else k)
        (complexCoefficientMul Q l k u)) - (2 : ℂ) • gaussianDerivativeAverage hd Q s hs 1 (fun _ => i) R := by
  classical
  have havg (f : Lp ℂ 2 (reducedLaw Q)) (j : Fin d) :
      HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) j
        (gaussianAverage hd Q s hs f)
        (gaussianDerivativeAverage hd Q s hs 1 (fun _ => j) f) := by
    rw [c3GaussianDerivativeAverage_one_eq_gradient]
    exact homogeneousAverage_hasComplexHorizontalGradient_allData Q ⟨0, by omega⟩ s hs 0 f j
  have hsecond (f : Lp ℂ 2 (reducedLaw Q)) (k : Fin d) :
      HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) i
        (gaussianDerivativeAverage hd Q s hs 1 (fun _ => k) f)
        (gaussianDerivativeAverage hd Q s hs 2 (fun n => if n = 0 then i else k) f) := by
    obtain ⟨v, hv, hv₂⟩ := UnforcedIdentification.homogeneousAverage_hasHorizontalJet_two
      Q ⟨0, by omega⟩ s hs 0 (fun n => if n = 0 then i else k) f
    have he : v = gaussianDerivativeAverage hd Q s hs 1 (fun _ => k) f :=
      hv.unique (havg f k)
    rw [he] at hv₂
    simpa only [ite_true, homogeneousDerivativeAverage, neg_zero,
      gaussianDerivativeAverage] using hv₂
  have hsum (S : Finset (Fin d)) :
      HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) i
        (∑ k ∈ S, gaussianDerivativeAverage hd Q s hs 1 (fun _ => k)
          (complexCoefficientMul Q l k u))
        (∑ k ∈ S, gaussianDerivativeAverage hd Q s hs 2
          (fun n => if n = 0 then i else k) (complexCoefficientMul Q l k u)) := by
    induction S using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using
        HasComplexHorizontalDerivative.zero (reducedLaw Q) (reducedLaw_stationary Q) i
    | @insert k S hk ih =>
      simpa only [Finset.sum_insert hk] using
        (hsecond (complexCoefficientMul Q l k u) k).add ih
  have hright := (hsum Finset.univ).add ((havg R i).smul (-2 : ℂ))
  simp only [neg_smul, ← sub_eq_add_neg] at hright
  rw [← gaussian_coefficient_row_weak_product hd D Q hQ β hβ u G hG l H R hH hR s hs]
    at hright
  exact (havg H i).unique hright
end EinsteinFull.Blueprint
