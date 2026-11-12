import EinsteinRelation.Correctors.CanonicalRegularExistence
import EinsteinRelation.Correctors.P53SourceSkewFamilies
import EinsteinRelation.Correctors.PlanarContinuousBallSupport
import EinsteinRelation.Correctors.ConditionalSpatialMollifierMoment

/-! # A continuous normalized heat-selected skew source

Source: `paper/main.tex:740–750,762–766,909–918`. The continuous volume
representative is antisymmetrized and centered before it is selected.
Every property below follows from the existing cited AKM and GT inputs.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger HeatSelectedSkewMeaning

/-- A continuous, jointly measurable heat-selected skew source with exact
pointwise skew symmetry and the production mollifier normalization.
Source: `paper/main.tex:740–750,909–918`. -/
theorem exists_continuous_normalized_heatSelectedSkewSource
    (h68 : FluxGradientEstimate) (hP : BallPoincareEstimate)
    (h836 : InteriorRegularRepresentative)
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
    (R : ℝ) (hR : 1 ≤ R) (i : Fin d) :
    ∃ S : FieldPair d → Vec d → Mat d,
      HasHeatSelectedSkewCorrectorColumn (Fact.out : 2 ≤ d) Q i S ∧
      (∀ j k, StronglyMeasurable (fun z : FieldPair d × Vec d => S z.1 z.2 j k)) ∧
      (∀ ω x, (S ω x).transpose = -(S ω x)) ∧
      (∀ j k, ∀ᵐ ω ∂reducedEnvironmentLaw Q,
        (∫ z, S ω (-z) j k ∂mollifierCenterMeasure d R) = 0) ∧
      ∀ᵐ ω ∂reducedEnvironmentLaw Q, Continuous (S ω) := by
  obtain ⟨σ, hσ, hm, hc⟩ := exists_continuous_heatSelectedSkewCorrectorColumn h68 hP h836 Q i
  let τ : FieldPair d → Vec d → Mat d := fun ω x =>
    (1/2 : ℝ) • (σ ω x - (σ ω x).transpose)
  have hτsk (ω : FieldPair d) (x : Vec d) : (τ ω x).transpose = -(τ ω x) := by
    ext j k
    simp only [τ, Matrix.transpose_apply, Matrix.smul_apply, Matrix.sub_apply,
      Matrix.neg_apply, smul_eq_mul]
    ring
  have hτm (j k : Fin d) : Measurable (fun z : FieldPair d × Vec d => τ z.1 z.2 j k) := by
    have he (a b : Fin d) : Measurable (fun z : FieldPair d × Vec d => σ z.1 z.2 a b) :=
      ((show Continuous (fun A : Mat d => A a b) by fun_prop).measurable.comp hm).comp
        measurable_swap
    exact ((he j k).sub (he k j)).const_mul (1/2)
  have hτc : ∀ᵐ ω ∂reducedEnvironmentLaw Q, Continuous (τ ω) := by
    filter_upwards [hc] with ω hω
    exact continuous_const.smul (hω.sub hω.matrix_transpose)
  have hτeq : ∀ᵐ ω ∂reducedEnvironmentLaw Q, σ ω =ᵐ[volume] τ ω := by
    filter_upwards [hc, hσ.choose_spec.2] with ω hω hs
    have hsk := continuous_skew_of_ae (σ ω) hω hs.1.1
    exact ae_of_all _ fun x => by
      ext j k
      have he := congrFun (congrFun (hsk x) j) k
      simp only [Matrix.transpose_apply, Matrix.neg_apply] at he
      simp only [τ, Matrix.smul_apply, Matrix.sub_apply, Matrix.transpose_apply, smul_eq_mul]
      rw [he]
      ring
  have hτ := heatSelectedSkewCorrector_congr_spatial_ae (Fact.out : 2 ≤ d) Q i hσ hτeq
  let S : FieldPair d → Vec d → Mat d := fun ω x => τ ω x - mollifierMatrixAverage R (τ ω)
  have hSsk (ω : FieldPair d) (x : Vec d) : (S ω x).transpose = -(S ω x) := by
    simp only [S, Matrix.transpose_sub, hτsk,
      mollifierMatrixAverage_transpose (hτsk ω), neg_sub_neg, neg_sub]
  refine ⟨S, hasHeatSelectedSkewCorrectorColumn_sub hτ _
    (fun ω => mollifierMatrixAverage_transpose (hτsk ω)), ?_, hSsk, ?_, ?_⟩
  · intro j k
    have hav : Measurable (fun ω => mollifierMatrixAverage R (τ ω) j k) := by
      exact ((((Entropy.contDiff_unitMassScaledMollifier R).continuous.measurable.comp
        measurable_snd).mul (hτm j k)).stronglyMeasurable.integral_prod_right').measurable
    exact ((hτm j k).sub (hav.comp measurable_fst)).stronglyMeasurable
  · intro j k
    have hR0 : 0 < R := zero_lt_one.trans_le hR
    filter_upwards [hτc] with ω hω
    rw [integral_mollifierCenterMeasure hR0]
    have hw : Integrable (Calculus.unitMassScaledMollifier d R) volume :=
      (Entropy.contDiff_unitMassScaledMollifier R).continuous.integrable_of_hasCompactSupport
        (Entropy.hasCompactSupport_unitMassScaledMollifier hR0)
    have hi : Integrable (fun x => Calculus.unitMassScaledMollifier d R x * τ ω x j k)
        volume :=
      (((continuous_apply k).comp ((continuous_apply j).comp hω)).mul
        (Entropy.contDiff_unitMassScaledMollifier R).continuous).integrable_of_hasCompactSupport
          ((Entropy.hasCompactSupport_unitMassScaledMollifier hR0).mul_left) |>.congr
            (ae_of_all _ fun x => mul_comm _ _)
    rw [integral_neg_eq_self (fun z => Calculus.unitMassScaledMollifier d R z * S ω z j k)
      volume]
    simp only [S, Matrix.sub_apply, mul_sub]
    rw [integral_sub hi (hw.mul_const _), integral_mul_const,
      Entropy.integral_unitMassScaledMollifier' hR0, one_mul]
    exact sub_self _
  · filter_upwards [hτc] with ω hω
    exact hω.sub continuous_const

/-- The regular normalized source is selected before any moment exponent.
Source: `paper/main.tex:762–766,909–918`. -/
def selectedContinuousNormalizedSkewSource
    (h68 : FluxGradientEstimate) (hP : BallPoincareEstimate)
    (h836 : InteriorRegularRepresentative)
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
    (R : ℝ) (i : Fin d) : FieldPair d → Vec d → Mat d :=
  (exists_continuous_normalized_heatSelectedSkewSource h68 hP h836 Q
    (max 1 R) (le_max_left _ _) i).choose

/-- All source properties of the fixed regular normalized family.
Source: `paper/main.tex:740–750,762–766,909–918`. -/
theorem selectedContinuousNormalizedSkewSource_spec
    (h68 : FluxGradientEstimate) (hP : BallPoincareEstimate)
    (h836 : InteriorRegularRepresentative)
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
    (R : ℝ) (hR : 1 ≤ R) (i : Fin d) :
    let S := selectedContinuousNormalizedSkewSource h68 hP h836 Q R i
    HasHeatSelectedSkewCorrectorColumn (Fact.out : 2 ≤ d) Q i S ∧
      (∀ j k, StronglyMeasurable (fun z : FieldPair d × Vec d => S z.1 z.2 j k)) ∧
      (∀ ω x, (S ω x).transpose = -(S ω x)) ∧
      (∀ j k, ∀ᵐ ω ∂reducedEnvironmentLaw Q,
        (∫ z, S ω (-z) j k ∂mollifierCenterMeasure d R) = 0) ∧
      ∀ᵐ ω ∂reducedEnvironmentLaw Q, Continuous (S ω) := by
  have h := (exists_continuous_normalized_heatSelectedSkewSource h68 hP h836 Q
    (max 1 R) (le_max_left _ _) i).choose_spec
  simpa only [selectedContinuousNormalizedSkewSource, max_eq_right hR] using h

end EinsteinRelation.Correctors
