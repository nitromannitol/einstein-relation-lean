import EinsteinRelation.Calculus.Weak
import EinsteinRelation.Calculus.ZeroWeakGradientConstant
import EinsteinRelation.Correctors.NormalizedScalarPhysicalLawTransportSupport
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # Uniqueness of the normalized scalar corrector

For two potentials satisfying the normalized canonical scalar corrector predicate with the same
data, the difference of the two slices has zero weak gradient. A locally integrable function on
`Vec d` with zero weak gradient is almost everywhere constant
(`EinsteinRelation.ae_eq_const_of_zero_weak_gradient`), so the two slices differ by a constant
almost everywhere. The normalization then forces the constants to agree, and the two values agree
almost everywhere. -/

open MeasureTheory

namespace EinsteinRelation.Correctors.NormalizedScalarCorrectorUniqueness

open NormalizedSpatialRepresentativeSupport
open StationarySpatialRealization
open NormalizedScalarPhysicalLawTransportSupport

/-- Equal gauge classes have equal normalized ordinary classes. Hence two potentials in the same
gauge class, each normalized to itself, agree almost everywhere. -/
theorem value_ae_eq_of_gauge_eq_of_normalized {d : ℕ} (ζ : SourceMollifier d) (R : ℝ)
    (hR : 1 ≤ R) (y : Point d) (ψ ψ' : ScalarSpatialPotential d)
    (hclass : Quotient.mk (spatialGaugeSetoid d ℝ) ψ = Quotient.mk (spatialGaugeSetoid d ℝ) ψ')
    (hψ : sourceMollifierNormalize ζ R hR y (Quotient.mk (spatialGaugeSetoid d ℝ) ψ) =
      Quotient.mk (spatialAESetoid d ℝ) ψ)
    (hψ' : sourceMollifierNormalize ζ R hR y (Quotient.mk (spatialGaugeSetoid d ℝ) ψ') =
      Quotient.mk (spatialAESetoid d ℝ) ψ') :
    ψ.value =ᵐ[volume] ψ'.value := by
  have hae : Quotient.mk (spatialAESetoid d ℝ) ψ = Quotient.mk (spatialAESetoid d ℝ) ψ' := by
    rw [← hψ, ← hψ', hclass]
  have h := Quotient.exact hae
  change ψ.value =ᵐ[volume] ψ'.value at h
  exact h

/-- Two weak gradients with the same gradient give a difference that pairs to zero with every
coordinate derivative of a smooth compactly supported test function. -/
theorem integral_sub_mul_coordinateDerivative_eq_zero {d : ℕ} {u v : Vec d → ℝ}
    {G : Vec d → Vec d} (hu : HasWeakGradient Set.univ u G)
    (hv : HasWeakGradient Set.univ v G) (j : Fin d) {ψ : Vec d → ℝ}
    (hψ : IsSpatialTest Set.univ ψ) :
    ∫ x, (u x - v x) * coordinateDerivative j ψ x = 0 := by
  have hkC : Continuous (fun x => coordinateDerivative j ψ x) := by
    unfold coordinateDerivative
    exact (hψ.1.continuous_fderiv (mod_cast le_top)).clm_apply continuous_const
  have hkc : HasCompactSupport (fun x => coordinateDerivative j ψ x) :=
    hψ.2.1.fderiv_apply ℝ (unitVector j)
  have hu_int : Integrable (fun x => u x * coordinateDerivative j ψ x) volume := by
    refine ((locallyIntegrableOn_univ.mp (hu j).1).integrable_smul_left_of_hasCompactSupport
      hkC hkc).congr ?_
    filter_upwards with x
    simp only [smul_eq_mul]
    ring
  have hv_int : Integrable (fun x => v x * coordinateDerivative j ψ x) volume := by
    refine ((locallyIntegrableOn_univ.mp (hv j).1).integrable_smul_left_of_hasCompactSupport
      hkC hkc).congr ?_
    filter_upwards with x
    simp only [smul_eq_mul]
    ring
  have hu_eq := (hu j).2.2 ψ hψ
  have hv_eq := (hv j).2.2 ψ hψ
  simp only [setIntegral_univ] at hu_eq hv_eq
  simp only [sub_mul]
  rw [integral_sub hu_int hv_int]
  linarith

/-- For two normalized canonical scalar correctors with the same data, almost every event gives
slices whose difference pairs to zero with every coordinate derivative of every test function. -/
theorem ae_integral_sub_mul_coordinateDerivative_eq_zero {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : SourceMollifier d) (R : ℝ) (hR : 1 ≤ R)
    (y : Point d) (φ φ' : FieldPair d → Point d → ℝ)
    (hφ : IsNormalizedCanonicalScalarCorrector Q i ζ R hR y φ)
    (hφ' : IsNormalizedCanonicalScalarCorrector Q i ζ R hR y φ') :
    ∀ᵐ ω ∂reducedEnvironmentLaw Q, ∀ (j : Fin d) {ψ : Vec d → ℝ},
      IsSpatialTest Set.univ ψ →
        ∫ x, (φ ω (WithLp.toLp 2 x) - φ' ω (WithLp.toLp 2 x)) * coordinateDerivative j ψ x = 0 := by
  filter_upwards [hφ.2, hφ'.2] with ω hω hω'
  obtain ⟨_, hG, -⟩ := hω
  obtain ⟨_, hG', -⟩ := hω'
  intro j ψ hψ
  exact integral_sub_mul_coordinateDerivative_eq_zero hG hG' j hψ

/-- Two normalized canonical scalar correctors with the same data agree almost everywhere, for
almost every environment. Their coordinate slices have the same weak gradient, so the difference
is almost everywhere constant on `Vec d`. That constant is a gauge shift, and the normalization
identifies the two gauge classes, so the values agree almost everywhere. -/
theorem ae_value_eq_of_normalized_canonical_scalar_corrector {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : SourceMollifier d) (R : ℝ) (hR : 1 ≤ R)
    (y : Point d) (φ φ' : FieldPair d → Point d → ℝ)
    (hφ : IsNormalizedCanonicalScalarCorrector Q i ζ R hR y φ)
    (hφ' : IsNormalizedCanonicalScalarCorrector Q i ζ R hR y φ') :
    ∀ᵐ ω ∂reducedEnvironmentLaw Q, φ ω =ᵐ[volume] φ' ω := by
  have hd : 0 < d := by
    have := (Fact.out : 2 ≤ d)
    omega
  filter_upwards [hφ.2, hφ'.2] with ω hω hω'
  obtain ⟨hLI, hG, hnorm⟩ := hω
  obtain ⟨hLI', hG', hnorm'⟩ := hω'
  -- The difference of the two coordinate representatives is locally integrable on `Vec d`.
  have hloc : LocallyIntegrable
      (fun x : Vec d => φ ω (WithLp.toLp 2 x) - φ' ω (WithLp.toLp 2 x)) volume :=
    (locallyIntegrableOn_univ.mp (hG ⟨0, hd⟩).1).sub
      (locallyIntegrableOn_univ.mp (hG' ⟨0, hd⟩).1)
  obtain ⟨c, hc⟩ := ae_eq_const_of_zero_weak_gradient hloc
    (fun j ψ hψ => integral_sub_mul_coordinateDerivative_eq_zero hG hG' j hψ)
  have hc' : ∀ᵐ x ∂(volume : Measure (Vec d)),
      φ ω (WithLp.toLp 2 x) - φ' ω (WithLp.toLp 2 x) = c := by
    filter_upwards [hc] with x hx
    exact hx
  -- Transport the almost-everywhere identity along the measure-preserving map `toLp`.
  have hemb : MeasurableEmbedding (WithLp.toLp 2 : (Fin d → ℝ) → Point d) :=
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurableEmbedding
  have hpt : ∀ᵐ y' ∂(volume : Measure (Point d)), φ ω y' - φ' ω y' = c := by
    have hmp : Measure.map (WithLp.toLp 2 : (Fin d → ℝ) → Point d) volume = volume :=
      (PiLp.volume_preserving_toLp (Fin d)).map_eq
    rw [← hmp]
    exact (hemb.ae_map_iff (p := fun y' : Point d => φ ω y' - φ' ω y' = c)).mpr hc'
  have hgauge : SpatialGaugeEq (⟨φ ω, hLI⟩ : ScalarSpatialPotential d) ⟨φ' ω, hLI'⟩ := by
    refine ⟨c, ?_⟩
    filter_upwards [hpt] with y' hy'
    change φ ω y' = φ' ω y' + c
    linarith
  have hclass : Quotient.mk (spatialGaugeSetoid d ℝ) (⟨φ ω, hLI⟩ : ScalarSpatialPotential d) =
      Quotient.mk (spatialGaugeSetoid d ℝ) (⟨φ' ω, hLI'⟩ : ScalarSpatialPotential d) :=
    Quotient.sound hgauge
  exact value_ae_eq_of_gauge_eq_of_normalized ζ R hR y ⟨φ ω, hLI⟩ ⟨φ' ω, hLI'⟩ hclass
    hnorm hnorm'


end EinsteinRelation.Correctors.NormalizedScalarCorrectorUniqueness
