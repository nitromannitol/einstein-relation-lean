import EinsteinRelation.Correctors.CorrectorLocalFromSelectedEnergyBounds
import EinsteinRelation.Correctors.CorrectorLocalFromRegularSources
import EinsteinRelation.Correctors.GradientCopyFromMeasurableKernel
import EinsteinRelation.Correctors.PlanarCenteredIntegrability
import EinsteinRelation.Correctors.ConditionalCopyPlanarMoments
import EinsteinRelation.Correctors.PlanarEnergyFromGradientCopies
import EinsteinRelation.Correctors.CorrectorGradientMomentsFromLiterature

/-! # Proposition 5.3 from measurable kernels and a regular skew family

Source: `paper/main.tex:762–766,872–890,948–973`. All point-gradient
and planar copy estimates follow from the measurable scalar-kernel
construction. A regular normalized skew family can be supplied or
constructed from the existing flux-gradient and regularity inputs.
-/

open MeasureTheory
namespace EinsteinRelation
open Environment.AKMTestIntegralSupport Correctors ReductionImageV3 External.AKM External.GilbargTrudinger HeatSelectedSkewMeaning
open Correctors.NormalizedSpatialRepresentativeSupport
open Correctors.NormalizedScalarPhysicalLawTransportSupport
local instance : Fact (2 ≤ (2 : ℕ)) := ⟨le_rfl⟩
attribute [local instance] ReductionImageV3.fieldPair_standardBorel
local instance kernelAssemblyRestrictionMeasurableSpace {d : ℕ} (U : Set (Vec d)) :
    MeasurableSpace C(U, Mat d) := borel C(U, Mat d)

variable
    (hP : BallPoincareEstimate)
    (h836 : InteriorRegularRepresentative)
    (S : ∀ {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}, EnvironmentLaw d L r₀ → ℝ → Fin d →
      FieldPair d → Vec d → Mat d)
    (hS : ∀ {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}
      (Q : EnvironmentLaw d L r₀) (R : ℝ), 1 ≤ R → ∀ i : Fin d,
      HasHeatSelectedSkewCorrectorColumn (Fact.out : 2 ≤ d) Q i (S Q R i))
    (hSm : ∀ {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}
      (Q : EnvironmentLaw d L r₀) (R : ℝ), 1 ≤ R → ∀ i j k : Fin d,
      StronglyMeasurable (fun z : FieldPair d × Vec d => S Q R i z.1 z.2 j k))
    (hSsk : ∀ {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}
      (Q : EnvironmentLaw d L r₀) (R : ℝ), 1 ≤ R → ∀ (i : Fin d) (ω : FieldPair d)
        (x : Vec d), (S Q R i ω x).transpose = -(S Q R i ω x))
    (hSn : ∀ {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}
      (Q : EnvironmentLaw d L r₀) (R : ℝ), 1 ≤ R → ∀ i j k : Fin d,
      ∀ᵐ ω ∂reducedEnvironmentLaw Q,
        (∫ z, S Q R i ω (-z) j k ∂mollifierCenterMeasure d R) = 0)
    (hSc : ∀ {L r₀ : ℝ} (Q : EnvironmentLaw 2 L r₀) (R : ℝ),
      1 ≤ R → ∀ i : Fin 2, ∀ᵐ ω ∂reducedEnvironmentLaw Q, Continuous (S Q R i ω))


include hP h836 hS hSm hSsk hSn hSc

/-- Proposition 5.3 reduced to the actual point-gradient copy decay.
Planar spatial RMS decay follows by nested conditioning and averaging,
with Lemma 5.1 handling small radii. The same fixed continuous sources
serve every exponent. Source: `paper/main.tex:872–890,948–973`. -/
theorem correctorLocalConstruction_of_regular_skew_and_gradient_copy_bounds
    (hgradient : ∀ (d : ℕ) [Fact (2 ≤ d)] (Λ₀ r₀ m : ℝ),
      2 ≤ m → ∃ C : ℝ, ∀ (Q : EnvironmentLaw d Λ₀ r₀) (R : ℝ), 1 ≤ R →
        ∀ (y : Point d) (i : Fin d),
        eLpNorm (fun z : C(conditionalCorrectorBall R y, Mat d) ×
          (FieldPair d × FieldPair d) =>
          euclideanNorm (conditionalCorrectorGradient Q i y z.2.1 -
            conditionalCorrectorGradient Q i y z.2.2)) (ENNReal.ofReal m)
          (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y)) ≤
            ENNReal.ofReal (C * R ^ (-(d : ℝ) / 2)))
    (h45 : ScalarStationaryEstimate) (h46 : ScalarPlanarL2Estimate)
    (h47 : ScalarHeatDifferenceEstimate) (h68 : FluxGradientEstimate)
    (h614 : FluxStationaryEstimate) (h615 : FluxPlanarL2Estimate)
    (h616 : FluxHeatDifferenceEstimate)
    (h817 : LocalBoundednessEstimate) (h832 : InteriorGradientEstimate)
    (hH2 : CorrectorWeakH2) :
    CorrectorLocalConstruction := by
  apply correctorLocalConstruction_of_selected_regular_sources_and_separate_copy_bounds
    hP h836 S hS hSm hSsk hSn hSc
    hgradient _ h45 h46 h47 h68 h614 h615 h616 h817 h832 hH2
  intro L r₀ m hm
  have H51 := correctorGradientMoments_of_literature
    h45 h46 h68 h614 h615 hP h817 h832 h836
  have hg : ∃ C : ℝ, ∀ (Q : EnvironmentLaw 2 L r₀) (R : ℝ), 1 ≤ R →
      ∀ (y : Point 2) (i : Fin 2),
      eLpNorm (fun z : C(conditionalCorrectorBall R y, Mat 2) ×
        (FieldPair 2 × FieldPair 2) =>
        euclideanNorm (conditionalCorrectorGradient Q i y z.2.1 -
          conditionalCorrectorGradient Q i y z.2.2)) (ENNReal.ofReal m)
        (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y)) ≤
          ENNReal.ofReal (C/R) := by
    obtain ⟨C, hC⟩ := hgradient 2 L r₀ m hm
    refine ⟨C, fun Q R hR y i => ?_⟩
    simpa only [Nat.cast_ofNat, show -(2 : ℝ)/2 = -1 by norm_num,
      Real.rpow_neg_one, div_eq_mul_inv] using hC Q R hR y i
  obtain ⟨B, hB, hEb⟩ := exists_planar_copy_energy_bound_of_gradient_copy_bounds H51 L r₀ m hm hg
  obtain ⟨C, _, hb⟩ := paired_planar_centered_moments_of_energy h817 hP L
  refine ⟨C*B, ?_⟩
  intro Q R hR i
  let φ : FieldPair 2 → Point 2 → ℝ := fun ω x =>
    selectedContinuousCanonicalScalarSource hP h836 Q R i ω x.ofLp
  let σ := S Q R i
  have hφ := selectedContinuousCanonicalScalarSource_normalized hP h836 Q R hR i
  have hσ := hS Q R hR i
  have hc : ∀ᵐ ω ∂reducedEnvironmentLaw Q, Continuous (φ ω) ∧ Continuous (σ ω) := by
    filter_upwards [ae_continuous_selectedContinuousCanonicalScalarSource hP h836 Q R i,
      hSc Q R hR i] with ω hφc hσc
    exact ⟨hφc.comp (PiLp.continuous_ofLp 2 (fun _ : Fin 2 => ℝ)), hσc⟩
  have hσm (a b : Fin 2) : Measurable (fun z : FieldPair 2 × Vec 2 => σ z.1 z.2 a b) :=
    (hSm Q R hR i a b).measurable
  obtain ⟨hEi, hEn⟩ := hEb Q R hR 0 i
  obtain ⟨hφm, hSm, _, _, hn⟩ := hb Q (canonicalSourceMollifier 2) R hR 0 i
    φ σ hφ hσ hc hσm (ENNReal.ofReal m) B hB.le hEi hEn
  obtain ⟨hφi, hSi⟩ := integrable_planar_centered_correctors h817 hP Q
    (canonicalSourceMollifier 2) R hR 0 i φ σ hφ hσ hc hσm
  exact ⟨hφm, hφi, hSm, hSi, hn⟩

/-- Proposition 5.3, conditional on the listed frozen inputs, the
regular skew source family, and the explicit internal coefficient-joint
kernel construction. No spatial energy, stationary identification or
point-copy bound remains as a premise.
Source: `paper/main.tex:872–890,948–973`. -/
theorem correctorLocalConstruction_of_measurable_kernel_and_regular_skew
    (hdecay : ParabolicSemigroupKernelDecay) (hreg : ParabolicLargeScale)
    (hAKM : EllipticLargeScale)
    (h45 : ScalarStationaryEstimate) (h46 : ScalarPlanarL2Estimate)
    (h47 : ScalarHeatDifferenceEstimate) (h68 : FluxGradientEstimate)
    (h614 : FluxStationaryEstimate) (h615 : FluxPlanarL2Estimate)
    (h616 : FluxHeatDifferenceEstimate)
    (h817 : LocalBoundednessEstimate) (h832 : InteriorGradientEstimate)
    (hH2 : CorrectorWeakH2)
    (hkernel : ∀ (d : ℕ) [Fact (2 ≤ d)] (L r₀ : ℝ) (Q : EnvironmentLaw d L r₀),
      ∃ (CK : ℝ → ℝ)
        (P : Coefficient d (AKMUpperEllipticity L) → ℝ → Vec d → Vec d → ℝ),
        (∀ α, 0 < α → α < (AKMUpperEllipticity L)⁻¹ → 0 < CK α) ∧
        Measurable (fun z :
          (Coefficient d (AKMUpperEllipticity L) × (ℝ × Vec d)) × Vec d =>
          P z.1.1 z.1.2.1 z.1.2.2 z.2) ∧
        ∀ᵐ A ∂actualCoefficientLaw Q,
          ∃ (X Y : ℝ → Vec d → Vec d → Vec d)
            (H : ℝ → Vec d → Vec d → Mat d), HeatKernelProperties A (P A) X Y H CK) :
    CorrectorLocalConstruction := by
  have H51 := correctorGradientMoments_of_literature
    h45 h46 h68 h614 h615 hP h817 h832 h836
  apply correctorLocalConstruction_of_regular_skew_and_gradient_copy_bounds
    hP h836 S hS hSm hSsk hSn hSc _
    h45 h46 h47 h68 h614 h615 h616 h817 h832 hH2
  intro d hd L r₀ m hm
  exact gradient_copy_decay_of_measurable_kernel
    hdecay hreg hAKM hP h817 h832 h836 H51 d L r₀ m hm (hkernel d L r₀)

omit hS hSm hSsk hSn hSc

/-- Proposition 5.3 with the regular skew family also constructed from
AKM flux-gradient and GT inputs. Only the explicit internal scalar-kernel
construction remains beyond the listed frozen inputs.
Source: `paper/main.tex:872–890,948–973`. -/
theorem correctorLocalConstruction_of_measurable_kernel
    (hdecay : ParabolicSemigroupKernelDecay) (hreg : ParabolicLargeScale)
    (hAKM : EllipticLargeScale)
    (h45 : ScalarStationaryEstimate) (h46 : ScalarPlanarL2Estimate)
    (h47 : ScalarHeatDifferenceEstimate) (h68 : FluxGradientEstimate)
    (h614 : FluxStationaryEstimate) (h615 : FluxPlanarL2Estimate)
    (h616 : FluxHeatDifferenceEstimate)
    (h817 : LocalBoundednessEstimate) (h832 : InteriorGradientEstimate)
    (hH2 : CorrectorWeakH2)
    (hkernel : ∀ (d : ℕ) [Fact (2 ≤ d)] (L r₀ : ℝ) (Q : EnvironmentLaw d L r₀),
      ∃ (CK : ℝ → ℝ)
        (P : Coefficient d (AKMUpperEllipticity L) → ℝ → Vec d → Vec d → ℝ),
        (∀ α, 0 < α → α < (AKMUpperEllipticity L)⁻¹ → 0 < CK α) ∧
        Measurable (fun z :
          (Coefficient d (AKMUpperEllipticity L) × (ℝ × Vec d)) × Vec d =>
          P z.1.1 z.1.2.1 z.1.2.2 z.2) ∧
        ∀ᵐ A ∂actualCoefficientLaw Q,
          ∃ (X Y : ℝ → Vec d → Vec d → Vec d)
            (H : ℝ → Vec d → Vec d → Mat d), HeatKernelProperties A (P A) X Y H CK) :
    CorrectorLocalConstruction := by
  have H51 := correctorGradientMoments_of_literature
    h45 h46 h68 h614 h615 hP h817 h832 h836
  apply correctorLocalConstruction_of_continuous_sources_and_gradient_copy_bounds
    hP h836 _ h45 h46 h47 h68 h614 h615 h616 h817 h832 hH2
  intro d hd L r₀ m hm
  exact gradient_copy_decay_of_measurable_kernel
    hdecay hreg hAKM hP h817 h832 h836 H51 d L r₀ m hm (hkernel d L r₀)

end EinsteinRelation
