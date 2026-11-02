import EinsteinFull.External.Source.AKMLocalizedEnergy

open MeasureTheory

namespace EinsteinFull.External.Draft
open EinsteinRelation EinsteinRelation.External.AKM
open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinFull.External.Source.AKM

/-- DRAFT graph leaf `external:AKM#5.85`, AKM printed pp.221–222,
with the actual coordinate minimization of pp.155–156 and energy (4.103).
The source constants are chosen before the law. The exponent called α in
(5.82) is γ here; α below is the auxiliary fluctuation exponent in (4.84).
Only r≥2 is retained, the domain of the explicit source construction.
The conclusion supplies genuine minimizing selectors and the source local
sigma algebra, not an arbitrary localized energy with presumed estimates.
No stationary-carrier, complex-force or commutator identification is asserted. -/
def akmLocalizedEnergyStmt : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ K s δ γ : ℝ,
    1 < K → 1 < s → s < 2 → 0 < δ →
    (d : ℝ) / 2 * (1 + δ) < γ →
    γ < min ((d : ℝ) / s) ((d : ℝ) / 2 * (1 + δ) + δ) →
    ∃ α σ θ C₀ C : ℝ,
      0 < α ∧ α ≤ (d : ℝ) / 2 ∧ γ < α * (1 + δ) + δ ∧
      0 < σ ∧ σ ≤ 1 / 2 ∧ 0 < θ ∧ θ ≤ 1 / 2 ∧ 0 < C₀ ∧ 0 < C ∧
      ∀ P : Measure (Coefficient d K), LawHypotheses P →
      ∃ W : ∀ (a : Coefficient d K) (z : Vec d) (r : ℝ), 2 ≤ r →
          LocalizedBasis a z (localizationOuterRadius δ r)
            (localizationIntermediateRadius δ α γ r) σ θ C₀,
        ∀ (z : Vec d) (r : ℝ) (hr : 2 ≤ r) (p q : Vec d),
          euclideanNorm p < 1 → euclideanNorm q < 1 →
          @Measurable (Coefficient d K) ℝ
            (localSigma (ball z (localizationOuterRadius δ r))) inferInstance
            (fun a => localizedEnergyJ1 (W a z r hr) r p q) ∧
          OsBound P (fun a =>
            |gaussianEnergyJ1 a z r p q - localizedEnergyJ1 (W a z r hr) r p q|)
            s (C * r ^ (-γ))

end EinsteinFull.External.Draft
