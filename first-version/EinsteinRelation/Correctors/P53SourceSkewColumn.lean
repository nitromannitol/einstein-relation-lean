import EinsteinRelation.Correctors.P53SourceSkewStationaryGradient
import EinsteinRelation.Correctors.P53SourceSkewDivergence
import EinsteinRelation.Correctors.P53SourceSkewPoisson
import EinsteinRelation.Correctors.P53SourceSkewHeatHessianIBP
import EinsteinRelation.Correctors.CanonicalHarmonicFromPoincare
import EinsteinRelation.Correctors.CenteredCorrectorFluxSupport

/-!
# A heat-selected skew flux corrector

Source: `paper/main.tex:688-702,732-748`; AKM Lemma 6.1, (6.5)-(6.7). The stationary
gradient selected by the heat formula (6.7) for the canonical centered flux is
the weak gradient of a jointly measurable potential that is skew at every point.
Its row divergence is the centered flux (AKM (6.6)), by the ergodic argument of
`P53SourceSkewDivergence`, and its entries solve the curl Poisson equation (6.5),
by closedness. This constructs a field with the frozen meaning
`HasHeatSelectedSkewCorrectorColumn`. Inputs: `FluxGradientEstimate` (AKM Lemma 6.1)
and `BallPoincareEstimate` (Gilbarg–Trudinger (7.45)).
-/

open MeasureTheory Filter Topology
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM HeatSelectedSkewMeaning

variable {d : ℕ}

/-- The integral of a coordinate derivative of a smooth compactly supported function
vanishes. -/
theorem integral_coordinateDerivative_eq_zero {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (i : Fin d) : ∫ x, coordinateDerivative i φ x = 0 := by
  have h := integral_mul_coordinateDerivative_eq_neg (f := φ) (g := fun _ => (1 : ℝ)) (i := i)
    (hφ.of_le (by norm_cast)) hφc contDiff_const
  have h0 : coordinateDerivative i (fun _ : Vec d => (1 : ℝ)) = fun _ => 0 := by
    funext x
    simp [coordinateDerivative]
  simp only [h0, mul_zero, integral_zero, mul_one] at h
  linarith

/-- Subtracting a constant vector preserves a weak divergence on all of space. -/
theorem hasWeakDivergence_sub_const {F : Vec d → Vec d} {h : Vec d → ℝ}
    (hF : HasWeakDivergence Set.univ F h) (c : Vec d) :
    HasWeakDivergence Set.univ (fun x => F x - c) h := by
  refine ⟨fun i => (hF.1 i).sub (locallyIntegrableOn_const _), hF.2.1, fun φ hφ => ?_⟩
  have hD (i : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative i φ) :=
    contDiff_coordinateDerivative' hφ.1 i
  have hDc (i : Fin d) : HasCompactSupport (coordinateDerivative i φ) :=
    hasCompactSupport_coordinateDerivative' hφ.2.1 i
  have hFi (i : Fin d) : Integrable (fun x => F x i * coordinateDerivative i φ x) volume := by
    simpa only [smul_eq_mul] using (locallyIntegrableOn_univ.mp (hF.1 i))
      |>.integrable_smul_right_of_hasCompactSupport (hD i).continuous (hDc i)
  have hci (i : Fin d) : Integrable (fun x => c i * coordinateDerivative i φ x) volume :=
    ((hD i).continuous.integrable_of_hasCompactSupport (hDc i)).const_mul _
  have h1 := hF.2.2 φ hφ
  simp only [Measure.restrict_univ, dot, gradient] at h1 ⊢
  rw [← h1]
  have hsumF : Integrable (fun x => ∑ i, F x i * coordinateDerivative i φ x) volume :=
    integrable_finset_sum _ fun i _ => hFi i
  have hsumc : Integrable (fun x => ∑ i, c i * coordinateDerivative i φ x) volume :=
    integrable_finset_sum _ fun i _ => hci i
  have hc0 : ∫ x, ∑ i, c i * coordinateDerivative i φ x = 0 := by
    rw [integral_finset_sum _ fun i _ => hci i]
    exact Finset.sum_eq_zero fun i _ => by
      rw [integral_const_mul, integral_coordinateDerivative_eq_zero hφ.1 hφ.2.1 i, mul_zero]
  calc (∫ x, ∑ i, (F x - c) i * coordinateDerivative i φ x)
      = ∫ x, ((∑ i, F x i * coordinateDerivative i φ x) -
          ∑ i, c i * coordinateDerivative i φ x) := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    _ = ∫ x, ∑ i, F x i * coordinateDerivative i φ x := by
        rw [integral_sub hsumF hsumc, hc0, sub_zero]

/-- The centered canonical flux has mean zero in every coordinate. -/
theorem integral_canonicalCenteredFlux_coord {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
    (i k : Fin d) :
    ∫ ω, (canonicalCorrectorFlux Q i ω - expectedCorrectorFlux Q i).ofLp k
      ∂reducedEnvironmentLaw Q = 0 := by
  have hint : Integrable (fun ω => canonicalCorrectorFlux Q i ω - expectedCorrectorFlux Q i)
      (reducedEnvironmentLaw Q) :=
    (canonicalCorrectorFlux_integrable Q i).sub (integrable_const _)
  have h0 : ∫ ω, (canonicalCorrectorFlux Q i ω - expectedCorrectorFlux Q i)
      ∂reducedEnvironmentLaw Q = 0 := by
    rw [integral_sub (canonicalCorrectorFlux_integrable Q i) (integrable_const _)]
    simp [expectedCorrectorFlux_eq_integral]
  have h := (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).integral_comp_comm hint
  calc (∫ ω, (canonicalCorrectorFlux Q i ω - expectedCorrectorFlux Q i).ofLp k
        ∂reducedEnvironmentLaw Q)
      = ∫ ω, (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
          (canonicalCorrectorFlux Q i ω - expectedCorrectorFlux Q i) ∂reducedEnvironmentLaw Q :=
        rfl
    _ = 0 := by rw [h, h0, map_zero]

/-- The centered canonical flux along almost every orbit is weakly divergence free. -/
theorem ae_canonicalCenteredFlux_hasWeakDivergence [Fact (2 ≤ d)] {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    ∀ᵐ ρ ∂reducedEnvironmentLaw Q, HasWeakDivergence Set.univ
      (fun x => (canonicalCorrectorFlux Q i (translate x ρ) - expectedCorrectorFlux Q i).ofLp)
      (fun _ => 0) := by
  filter_upwards [ae_canonicalCorrectorFlux_hasWeakDivergence Q i] with ρ hρ
  simpa only [WithLp.ofLp_sub] using hasWeakDivergence_sub_const hρ (expectedCorrectorFlux Q i).ofLp

/-- The row-divergence identity for the heat-selected stationary gradient of the
canonical centered flux. -/
theorem ae_sum_diag_canonicalHeatSelected [Fact (2 ≤ d)] {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) (F : FieldPair d → Fin d → Fin d → Fin d → ℝ)
    (hFm : ∀ j k l, Measurable (fun ω => F ω j k l))
    (hF2 : ∀ j k l, MemLp (fun ω => F ω j k l) 2 (reducedEnvironmentLaw Q))
    (hsel : ∀ᵐ ρ ∂reducedEnvironmentLaw Q, IsHeatSelectedFluxGradient
      (centeredFluxOrbit Q i ρ) (fun j k x l => F (translate x ρ) j k l)) (j : Fin d) :
    (fun ω => ∑ k : Fin d, F ω j k k) =ᵐ[reducedEnvironmentLaw Q]
      fun ω => (canonicalCorrectorFlux Q i ω - expectedCorrectorFlux Q i).ofLp j :=
  HeatSelectedDivergenceData.sum_diag_ae_eq
    ⟨fun ω => (canonicalCorrectorFlux Q i ω - expectedCorrectorFlux Q i).ofLp, F,
      (canonical_flux_source_measurable_memLp Q i).1,
      (canonical_flux_source_measurable_memLp Q i).2,
      integral_canonicalCenteredFlux_coord Q i,
      ae_canonicalCenteredFlux_hasWeakDivergence Q i, hFm, hF2, hsel⟩
    (reducedEnvironmentLaw_stationary Q) (reducedEnvironmentLaw_ergodic Q Fact.out) j

/-- AKM Lemma 6.1 produces a heat-selected skew flux corrector column with the frozen
meaning, jointly measurable and skew at every point, with locally square-integrable
entries. Inputs: `FluxGradientEstimate`, `BallPoincareEstimate`. -/
theorem exists_heatSelectedSkewCorrectorColumn (h68 : FluxGradientEstimate)
    (hP : External.GilbargTrudinger.BallPoincareEstimate)
    [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    ∃ σ : FieldPair d → Vec d → Mat d,
      HasHeatSelectedSkewCorrectorColumn (Fact.out : 2 ≤ d) Q i σ ∧
      (∀ j k, Measurable (fun p : FieldPair d × Vec d => σ p.1 p.2 j k)) ∧
      (∀ ω x, (σ ω x).transpose = -(σ ω x)) ∧
      ∀ᵐ ρ ∂reducedEnvironmentLaw Q, ∀ R : ℝ, 0 < R → ∀ j k,
        MemLp (fun x => σ ρ x j k) 2 (volume.restrict (ball 0 R)) := by
  have hd2 : 2 ≤ d := Fact.out
  have hd : 0 < d := by omega
  obtain ⟨σ, F, hσm, hσsk, hFm, hF2, hae⟩ :=
    exists_stationary_heatSelected_skew_potential h68 hP Q i
  have hQr : IsStationary (reducedEnvironmentLaw Q) := reducedEnvironmentLaw_stationary Q
  obtain ⟨hgm, -⟩ := canonical_flux_source_measurable_memLp Q i
  have hdiag (j : Fin d) := ae_sum_diag_canonicalHeatSelected Q i F hFm hF2
    (hae.mono fun ρ hρ => hρ.1) j
  have horbit (j : Fin d) : ∀ᵐ ρ ∂reducedEnvironmentLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      (∑ k : Fin d, F (translate x ρ) j k k) =
        (canonicalCorrectorFlux Q i (translate x ρ) - expectedCorrectorFlux Q i).ofLp j := by
    have hum : Measurable (fun ω => ∑ k : Fin d, F ω j k k) :=
      Finset.measurable_sum _ fun k _ => hFm j k k
    have hvm : Measurable (fun ω =>
        (canonicalCorrectorFlux Q i ω - expectedCorrectorFlux Q i).ofLp j) :=
      (measurable_pi_apply j).comp hgm
    exact Entropy.ae_ae_translate_eq (u := fun ω => ∑ k : Fin d, F ω j k k)
      (v := fun ω => (canonicalCorrectorFlux Q i ω - expectedCorrectorFlux Q i).ofLp j)
      hQr hum hvm (hdiag j)
  refine ⟨σ, ⟨F, fun j k l => (hFm j k l).aestronglyMeasurable, ?_⟩, hσm, hσsk, ?_⟩
  · filter_upwards [hae, ae_all_iff.mpr horbit] with ρ hρ hdivρ
    obtain ⟨hsel, hweak, -, hswap, hcyc⟩ := hρ
    refine ⟨⟨ae_of_all _ fun x => hσsk ρ x, fun ψ hψ hψc j => ?_, fun ψ hψ hψc j k => ?_⟩,
      isIteratedAKMHeatGradientAt_of_isHeatSelectedFluxGradient _ ρ F hsel,
      fun row col => hweak row col⟩
    · exact closedSkew_rowDivergence_identity hd hweak hdivρ hψ hψc j
    · exact closedSkew_poisson_identity hd hweak hswap hcyc hdivρ hψ hψc j k
  · filter_upwards [hae] with ρ hρ
    exact hρ.2.2.1

end EinsteinRelation.Correctors
