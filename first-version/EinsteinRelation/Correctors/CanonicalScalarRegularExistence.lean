import EinsteinRelation.Correctors.CanonicalGradientRegularRepresentative
import EinsteinRelation.Correctors.RegularPotentialDerivative
import EinsteinRelation.Correctors.MeasurableRayPrimitive
import EinsteinRelation.Correctors.MeasurableScalarNormalization
import EinsteinRelation.Correctors.SpatialWeakCongruence

/-! Source: `paper/main.tex:694-704,735-737,762-766`. Scalar existence
with a jointly measurable continuous representative is derived from the
actual canonical gradient, Poincaré, and GT Corollary 8.36. The ray formula
selects the value gauge; the prescribed mollifier then normalizes it. -/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger
open NormalizedSpatialRepresentativeSupport NormalizedScalarPhysicalLawTransportSupport

/-- A measurable scalar primitive of the regular canonical affine gradient,
with the coordinate affine part removed. -/
def canonicalScalarRayPrimitive
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (ω : FieldPair d) (x : Vec d) : ℝ :=
  spatialRayPrimitive (canonicalAffineGradientRegularRepresentative Q i) ω x - x i

/-- The selected scalar primitive is jointly measurable. -/
theorem measurable_canonicalScalarRayPrimitive
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    Measurable (fun p : Vec d × FieldPair d => canonicalScalarRayPrimitive Q i p.2 p.1) :=
  (measurable_spatialRayPrimitive _
    (measurable_canonicalAffineGradientRegularRepresentative Q i)).sub
      ((measurable_pi_apply i).comp measurable_fst)

/-- The measurable ray formula is a continuous weak potential of the
actual canonical gradient on almost every environment. -/
theorem ae_canonicalScalarRayPrimitive_weakGradient
    (hP : BallPoincareEstimate) (h836 : InteriorRegularRepresentative)
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    ∀ᵐ ω ∂reducedEnvironmentLaw Q, Continuous (canonicalScalarRayPrimitive Q i ω) ∧
      HasWeakGradient Set.univ (canonicalScalarRayPrimitive Q i ω) (fun x =>
        ((canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
          (reducedEnvironmentLaw Q)) (translate x ω)).ofLp) := by
  filter_upwards [ae_canonicalAffine_c1Alpha_representatives hP h836 Q i,
    ae_canonicalAffineGradientRegularRepresentative hP h836 Q i] with ω hω hG
  obtain ⟨u, hw, _, hu⟩ := hω
  let a : Vec d → ℝ := fun x => x i + u x
  let ar : Vec d → ℝ := spatialRegularRepresentative (fun _ : Unit => a) ()
  let G := canonicalAffineGradientRegularRepresentative Q i ω
  have har : Continuous ar ∧ a =ᵐ[volume] ar :=
    continuous_spatialRegularRepresentative_of_ball_versions a (by
      intro n
      let S : ℝ := ((d : ℝ) + 1) * ((n : ℝ) + 1)
      obtain ⟨v, h, hreg, hveq, _⟩ := hu S (by dsimp [S]; positivity)
      have hv : ContinuousOn v (ball 0 S) :=
        fun x hx => (hreg.1 x hx).continuousAt.continuousWithinAt
      refine ⟨v, hv.mono supBall_subset_dimension_euclideanBall, ?_⟩
      exact hveq.symm.filter_mono (ae_mono (Measure.restrict_mono_set volume
        supBall_subset_dimension_euclideanBall)))
  have hd (x : Vec d) : HasFDerivAt ar
      (∑ j : Fin d, (G x j) • (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ)) x := by
    let S : ℝ := euclideanNorm x + 1
    have hS : 0 < S := by dsimp [S]; have hn : 0 ≤ euclideanNorm x := Real.sqrt_nonneg (euclideanSq x); linarith
    obtain ⟨v, h, hreg, hveq, hheq⟩ := hu S hS
    have hopen : IsOpen (ball (0 : Vec d) S) := by
      unfold ball euclideanNorm euclideanSq dot
      exact isOpen_lt (by fun_prop) continuous_const
    have hx : x ∈ ball (0 : Vec d) S := by
      change euclideanNorm (x - 0) < S
      simp only [sub_zero]
      dsimp [S]
      linarith
    obtain ⟨K, hK⟩ := hreg.2
    apply hasFDerivAt_of_local_regular_representatives ar G har.1 hG.1 x _ hopen hx v h
      (fun y hy => (hreg.1 y hy).continuousAt.continuousWithinAt)
      (continuousOn_pi.mpr (fun j => continuousOn_of_holderBound (by norm_num) (hK j)))
      hreg.1
    · exact Filter.EventuallyEq.trans (ae_restrict_of_ae har.2.symm) hveq.symm
    · exact Filter.EventuallyEq.trans (ae_restrict_of_ae hG.2.symm) hheq.symm
  have hpoint (x : Vec d) : canonicalScalarRayPrimitive Q i ω x = ar x - ar 0 - x i := by
    have h := spatialRayPrimitive_eq_sub_of_hasFDerivAt ar G hG.1 hd x
    exact congrArg (fun z => z - x i) h
  have hcont : Continuous (canonicalScalarRayPrimitive Q i ω) := by
    have heq : canonicalScalarRayPrimitive Q i ω = fun x => ar x - ar 0 - x i := funext hpoint
    rw [heq]
    exact (har.1.sub continuous_const).sub (continuous_apply i)
  refine ⟨hcont, ?_⟩
  apply hasWeakGradient_congr_ae isOpen_univ (hasWeakGradient_sub_const Set.univ hw (ar 0))
    ?_ Filter.EventuallyEq.rfl
  simp only [Measure.restrict_univ]
  filter_upwards [har.2] with x hx
  rw [hpoint x, ← hx]
  dsimp [a]
  ring

/-- The scalar half of corrector existence, strengthened to an actual
jointly measurable continuous normalized representative. -/
theorem exists_continuous_normalizedCanonicalScalarCorrector
    (hP : BallPoincareEstimate) (h836 : InteriorRegularRepresentative)
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (ζ : SourceMollifier d) (R : ℝ) (hR : 1 ≤ R) (y : Point d) :
    ∃ φ : FieldPair d → Point d → ℝ,
      IsNormalizedCanonicalScalarCorrector Q i ζ R hR y φ ∧
      ∀ᵐ ω ∂reducedEnvironmentLaw Q, Continuous (φ ω) := by
  exact ⟨normalizedScalarSelection (canonicalScalarRayPrimitive Q i) ζ R hR y,
    normalizedScalarSelection_isNormalizedCanonicalScalarCorrector Q i _
      (measurable_canonicalScalarRayPrimitive Q i)
      (ae_canonicalScalarRayPrimitive_weakGradient hP h836 Q i) ζ R hR y⟩

end EinsteinRelation.Correctors
