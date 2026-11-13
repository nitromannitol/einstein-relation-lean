import EinsteinFull.Calculus.C6SublinearFluxTraceIdentification
import EinsteinRelation.Correctors.WeakGradientCentering

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

noncomputable section

namespace EinsteinFull.Blueprint

open EinsteinRelation EinsteinRelation.External.AKM EinsteinRelation.Correctors
open EinsteinRelation.Environment.AKMTestIntegralSupport ReductionImageV3

/-- Heat selection fixes the sign: the column trace is the negative of the
literal row trace used by `sublinear_source_flux_column_trace`. -/
theorem c6_sourceColumnGradientTrace_eq_neg_row {d : ℕ} {K : ℝ}
    {P : Measure (Coefficient d K)} {e : Vec d} {φ : Corrector P e}
    (S : FluxCorrector φ) :
    ∀ᵐ a ∂P, ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j : Fin d,
      (∑ k : Fin d, S.grad a k j x k) = -c6SourceRowDivergence S a x j := by
  filter_upwards [S.heat_selected] with a ha
  have hswap := ae_all_iff.mpr fun j => ae_all_iff.mpr fun k =>
    c6_heatSelectedFluxGradient_ae_swap ha j k k
  filter_upwards [hswap] with x hx
  intro j
  change (∑ k : Fin d, S.grad a k j x k) = -(∑ k : Fin d, S.grad a j k x k)
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun k _ => hx j k

/-- On the actual source law the selected column trace is minus centered
flux. This sign is independent of every additive potential gauge. -/
theorem c6_actualSourceColumnGradientTrace_eq_neg_centeredFlux
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (correctorUnitVector i).ofLp)
    (S : FluxCorrector φ) :
    ∀ᵐ a ∂actualCoefficientLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      ∀ j : Fin d, (∑ k : Fin d, S.grad a k j x k) = -centeredFlux φ a x j := by
  filter_upwards [c6_sourceColumnGradientTrace_eq_neg_row S,
    sublinear_source_flux_column_trace d hd D Q hQ i φ S] with a hcol htrace
  filter_upwards [hcol, htrace] with x hx htrace
  intro j
  rw [hx j, htrace]

end EinsteinFull.Blueprint
