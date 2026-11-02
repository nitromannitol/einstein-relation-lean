import EinsteinFull.Calculus.C4CoefficientRowWeakProduct
import EinsteinFull.Calculus.C7UnitInitializationSupport
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation
/-- Gaussian smoothing of the actual coefficient-row weak product. -/
theorem gaussian_coefficient_row_weak_product
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (hβ : IsReducedDriftObservation Q hQ β)
    (u : Lp ℂ 2 (reducedLaw Q)) (G : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) u G)
    (l : Fin d) (H R : Lp ℂ 2 (reducedLaw Q))
    (hH : (H : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      fun ω => ∑ k : Fin d, (ω.1 0 l k : ℂ) * G k ω)
    (hR : (R : FieldPair d → ℂ) =ᵐ[reducedLaw Q] fun ω => β l ω * u ω)
    (s : ℝ) (hs : 0 < s) :
    gaussianAverage hd Q s hs H =
      (∑ k : Fin d, gaussianDerivativeAverage hd Q s hs 1 (fun _ => k)
        (complexCoefficientMul Q l k u)) - (2 : ℂ) • gaussianAverage hd Q s hs R := by
  classical
  apply UnitInitialization.endpointPairing_ext Q
  intro g
  let v := homogeneousAverage Q ⟨0, by omega⟩ s hs 0 g
  let V := homogeneousGaussianHorizontalGradient Q ⟨0, by omega⟩ s hs 0 g
  have hV := homogeneousAverage_hasComplexHorizontalGradient_allData Q
    ⟨0, by omega⟩ s hs 0 g
  have hw := coefficient_row_weak_product D Q hQ β hβ u v G V hG hV l
  have hleft : (∫ ω, (∑ k : Fin d, (ω.1 0 l k : ℂ) * G k ω) * v ω
      ∂reducedLaw Q) = c4EndpointPairing Q H v := by
    rw [c4EndpointPairing_apply]
    exact integral_congr_ae (hH.mono fun ω h => by dsimp only; rw [h])
  have hdrift : (∫ ω, β l ω * u ω * v ω ∂reducedLaw Q) =
      c4EndpointPairing Q R v := by
    rw [c4EndpointPairing_apply]
    exact integral_congr_ae (hR.mono fun ω h => by dsimp only; rw [h])
  have hflux : (∫ ω, u ω * (∑ k : Fin d, (ω.1 0 l k : ℂ) * V k ω)
      ∂reducedLaw Q) = ∑ k, c4EndpointPairing Q (complexCoefficientMul Q l k u) (V k) := by
    simp only [c4EndpointPairing_apply]
    have hi (k : Fin d) : Integrable
        (fun ω => complexCoefficientMul Q l k u ω * V k ω) (reducedLaw Q) :=
      (Lp.memLp (complexCoefficientMul Q l k u)).integrable_mul (Lp.memLp (V k))
    rw [← integral_finsetSum _ (fun k _ => hi k)]
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr (fun k => complexCoefficientMul_coe Q l k u)] with ω hω
    simp only [Finset.mul_sum, hω]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hleft, hdrift, hflux] at hw
  have hav (f : Lp ℂ 2 (reducedLaw Q)) :
      c4EndpointPairing Q (gaussianAverage hd Q s hs f) g =
        c4EndpointPairing Q f v := by
    change c4EndpointPairing Q (homogeneousAverage Q ⟨0, by omega⟩ s hs 0 f) g = _
    simpa only [neg_zero] using
      c4EndpointPairing_homogeneousAverage Q ⟨0, by omega⟩ s hs 0 f g
  have hder (k : Fin d) : c4EndpointPairing Q
      (gaussianDerivativeAverage hd Q s hs 1 (fun _ => k)
        (complexCoefficientMul Q l k u)) g =
      -c4EndpointPairing Q (complexCoefficientMul Q l k u) (V k) := by
    rw [c3EndpointPairing_gaussianDerivativeAverage_one,
      c3GaussianDerivativeAverage_one_eq_gradient]
  rw [hav]
  have hsum (f : Fin d → Lp ℂ 2 (reducedLaw Q)) :
      c4EndpointPairing Q (∑ k, f k) g = ∑ k, c4EndpointPairing Q (f k) g :=
    map_sum ((c4EndpointPairing Q).flip g) f Finset.univ
  simp only [map_sub, sub_apply, hsum, hder, Finset.sum_neg_distrib]
  change _ = _ - c4EndpointPairing Q ((2 : ℂ) • gaussianAverage hd Q s hs R) g
  have htwo : (2 : ℂ) • gaussianAverage hd Q s hs R =
      (2 : ℝ) • gaussianAverage hd Q s hs R := by simp only [two_smul]
  rw [htwo, map_smul, smul_apply, hav]
  simpa only [Complex.real_smul, Complex.ofReal_ofNat] using hw
end EinsteinFull.Blueprint
