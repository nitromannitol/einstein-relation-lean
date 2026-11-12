import EinsteinRelation.Correctors.StationaryWeightedOrbit
import EinsteinRelation.Correctors.HorizontalCharacterizationSupport
import EinsteinRelation.Correctors.SpatialWeakProduct
import EinsteinRelation.Calculus.Mollifier
import EinsteinRelation.Calculus.EnvironmentWeakCalculus
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-! # Spatial weak derivatives of stationary observables

Source: `paper/main.tex:789–816,926–938`. A samplewise spatial weak
gradient of a stationary square-integrable observable is its actual
horizontal translation-generator gradient. Spatial weak equations are
tested with a compact weight times a smooth orbit, then integrated over
the environment law. This supplies the bridge needed by the canonical
corrector identification, without assuming smooth samplewise solutions.
-/

open MeasureTheory Filter

namespace EinsteinRelation.Correctors

private theorem continuous_coordinateDerivative {d : ℕ} {η : Vec d → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (i : Fin d) :
    Continuous (coordinateDerivative i η) :=
  ((contDiff_infty_iff_fderiv.mp hη).2.clm_apply contDiff_const).continuous

/-- A compact smooth spatial test has zero integrated coordinate derivative.
Source: `paper/main.tex:789–816`, spatial to horizontal weak equations. -/
theorem integral_coordinateDerivative_eq_zero {d : ℕ} {η : Vec d → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η) (i : Fin d) :
    (∫ x, coordinateDerivative i η x ∂volume) = 0 := by
  have hint : Integrable (coordinateDerivative i η) volume :=
    (continuous_coordinateDerivative hη i).integrable_of_hasCompactSupport
    (hηc.fderiv_apply ℝ (unitVector i))
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure (Vec d))) (f := fun _ => (1 : ℝ))
    (g := η) (v := unitVector i)
    (by simp)
    (by simpa only [one_mul] using hint)
    (by simpa only [one_mul] using hη.continuous.integrable_of_hasCompactSupport hηc)
    (differentiable_const (1 : ℝ)) (hη.differentiable (by simp))
  simpa [coordinateDerivative] using h

private theorem stationary_spatial_ibp {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) (i : Fin d)
    {f g : FieldPair d → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : MemLp f 2 Q) (hg : MemLp g 2 Q)
    (hweak : ∀ᵐ ω ∂Q, HasWeakPartialDerivative Set.univ i (orbit f ω) (orbit g ω))
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hη1 : (∫ x, η x ∂volume) = 1)
    {H : FieldPair d → ℝ} (hH : IsHorizontalTest H) :
    (∫ ω, f ω * horizontalDerivative i H ω ∂Q) = -(∫ ω, g ω * H ω ∂Q) := by
  have hfD : Integrable (fun ω => f ω * horizontalDerivative i H ω) Q :=
    hf.integrable_mul (hH.memLp_derivative Q 2 i)
  have hfH : Integrable (fun ω => f ω * H ω) Q := hf.integrable_mul (hH.memLp Q 2)
  have hgH : Integrable (fun ω => g ω * H ω) Q := hg.integrable_mul (hH.memLp Q 2)
  have hηint : Integrable η volume := hη.continuous.integrable_of_hasCompactSupport hηc
  have hdηint : Integrable (coordinateDerivative i η) volume :=
    (continuous_coordinateDerivative hη i).integrable_of_hasCompactSupport
    (hηc.fderiv_apply ℝ (unitVector i))
  have hA := integrable_weighted_orbit Q hQ hη.continuous.measurable hηint
    (hfm.mul (hH.measurable_derivative i)) hfD
  have hB := integrable_weighted_orbit Q hQ (continuous_coordinateDerivative hη i).measurable
    hdηint (hfm.mul hH.1) hfH
  have hC := integrable_weighted_orbit Q hQ hη.continuous.measurable hηint
    (hgm.mul hH.1) hgH
  have heq :
      (fun ω => (∫ x, η x * (f (translate x ω) * horizontalDerivative i H (translate x ω))) +
          ∫ x, coordinateDerivative i η x * (f (translate x ω) * H (translate x ω))) =ᵐ[Q]
        fun ω => -(∫ x, η x * (g (translate x ω) * H (translate x ω))) := by
    filter_upwards [hweak, hA.prod_left_ae, hB.prod_left_ae] with ω hω hAω hBω
    have ht : IsSpatialTest Set.univ (fun x => η x * orbit H ω x) :=
      ⟨hη.mul (hH.2.1 ω), hηc.mul_right, Set.subset_univ _⟩
    have hw := hω.2.2 _ ht
    rw [Measure.restrict_univ] at hw
    rw [← integral_add hAω hBω]
    calc
      _ = ∫ x, orbit f ω x * coordinateDerivative i (fun x => η x * orbit H ω x) x := by
        apply integral_congr_ae
        exact ae_of_all _ fun x => by
          dsimp only
          rw [coordinateDerivative_mul i η (orbit H ω) x
            (hη.differentiable (by simp) x) ((hH.2.1 ω).differentiable (by simp) x)]
          rw [← horizontalDerivative_translate]
          simp only [orbit]
          ring
      _ = -(∫ x, orbit g ω x * (η x * orbit H ω x)) := hw
      _ = _ := by
        congr 1
        apply integral_congr_ae
        exact ae_of_all _ fun x => by simp only [orbit]; ring
  have hexp := integral_congr_ae heq
  rw [integral_add hA.integral_prod_right hB.integral_prod_right, integral_neg] at hexp
  rw [integral_weighted_orbit Q hQ hη.continuous.measurable hηint
      (hfm.mul (hH.measurable_derivative i)) hfD,
    integral_weighted_orbit Q hQ (continuous_coordinateDerivative hη i).measurable
      hdηint (hfm.mul hH.1) hfH,
    integral_weighted_orbit Q hQ hη.continuous.measurable hηint (hgm.mul hH.1) hgH,
    hη1, integral_coordinateDerivative_eq_zero hη hηc i] at hexp
  simpa only [one_mul, zero_mul, add_zero] using hexp

/-- Samplewise weak spatial differentiation gives the horizontal weak
derivative against the entire bounded smooth orbit core.
Source: `paper/main.tex:789–816,926–938`. -/
theorem weakHorizontalLpDerivative_of_spatial {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) (i : Fin d)
    {f g : FieldPair d → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : MemLp f 2 Q) (hg : MemLp g 2 Q)
    (hweak : ∀ᵐ ω ∂Q, HasWeakPartialDerivative Set.univ i (orbit f ω) (orbit g ω)) :
    HasWeakHorizontalLpDerivative Q i (hf.toLp f) (hg.toLp g) := by
  intro H hH
  have hfi := hf.integrable_mul (hH.memLp_derivative Q 2 i)
  have hgi := hg.integrable_mul (hH.memLp Q 2)
  have heq := stationary_spatial_ibp Q hQ i hfm hgm hf hg hweak
    (contDiff_mollifier d) (hasCompactSupport_mollifier d) (integral_mollifier d) hH
  have hfD : (fun ω => hf.toLp f ω * horizontalDerivative i H ω) =ᵐ[Q]
      fun ω => f ω * horizontalDerivative i H ω := by
    filter_upwards [hf.coeFn_toLp] with ω hω using congrArg (· * horizontalDerivative i H ω) hω
  have hgH : (fun ω => hg.toLp g ω * H ω) =ᵐ[Q] fun ω => g ω * H ω := by
    filter_upwards [hg.coeFn_toLp] with ω hω using congrArg (· * H ω) hω
  exact ⟨hfi.congr hfD.symm, hgi.congr hgH.symm,
    (integral_congr_ae hfD).trans (heq.trans (congrArg Neg.neg (integral_congr_ae hgH).symm))⟩

/-- A stationary observable with an actual square-integrable samplewise
weak gradient belongs to the full strong horizontal H¹ generator domain.
Source: `paper/main.tex:789–816,926–938`. -/
theorem horizontalH1_of_spatial_weakGradient {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {f : FieldPair d → ℝ} {G : FieldPair d → Vec d}
    (hfm : Measurable f) (hGm : Measurable G) (hf : MemLp f 2 Q)
    (hG : ∀ i, MemLp (fun ω => G ω i) 2 Q)
    (hweak : ∀ᵐ ω ∂Q, HasWeakGradient Set.univ (orbit f ω) (fun x => G (translate x ω))) :
    hf.toLp f ∈ horizontalH1 Q hQ := by
  apply (horizontalH1_iff_weakHorizontalLpDerivative hQ _).2
  intro i
  refine ⟨(hG i).toLp (fun ω => G ω i), ?_⟩
  apply weakHorizontalLpDerivative_of_spatial Q hQ i hfm ((measurable_pi_apply i).comp hGm)
    hf (hG i)
  filter_upwards [hweak] with ω hω using hω i

/-- Identification of each actual strong translation derivative with
the given samplewise spatial weak derivative. Source:
`paper/main.tex:789–816,926–938`. -/
theorem horizontalLpDerivatives_of_spatial_weakGradient {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {f : FieldPair d → ℝ} {G : FieldPair d → Vec d}
    (hfm : Measurable f) (hGm : Measurable G) (hf : MemLp f 2 Q)
    (hG : ∀ i, MemLp (fun ω => G ω i) 2 Q)
    (hweak : ∀ᵐ ω ∂Q, HasWeakGradient Set.univ (orbit f ω) (fun x => G (translate x ω))) :
    ∀ i, HasHorizontalLpDerivative Q hQ i (hf.toLp f) ((hG i).toLp (fun ω => G ω i)) := by
  let v : horizontalH1 Q hQ :=
    ⟨hf.toLp f, horizontalH1_of_spatial_weakGradient Q hQ hfm hGm hf hG hweak⟩
  intro i
  have hder := hasHorizontalLpDerivative_horizontalH1Gradient Q hQ v i
  have hspace := weakHorizontalLpDerivative_of_spatial Q hQ i hfm
    ((measurable_pi_apply i).comp hGm) hf (hG i)
    (hweak.mono fun ω hω => hω i)
  have hid := (hasHorizontalLpDerivative_to_weak hder).unique hQ hspace
  rw [hid] at hder
  exact hder

/-- Samplewise spatial weak gradients satisfy the complete horizontal
weak-gradient predicate used by Proposition 5.3, including all tests in
the actual generator domain specified there. Source:
`paper/main.tex:926–938`. -/
theorem weakHorizontalGradient_of_spatial {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {f : FieldPair d → ℝ} {G : FieldPair d → Vec d}
    (hfm : Measurable f) (hGm : Measurable G) (hf : MemLp f 2 Q)
    (hG : ∀ i, MemLp (fun ω => G ω i) 2 Q)
    (hweak : ∀ᵐ ω ∂Q, HasWeakGradient Set.univ (orbit f ω) (fun x => G (translate x ω))) :
    HasWeakHorizontalGradient Q hQ f G := by
  refine ⟨hf.integrable (by norm_num), fun i => (hG i).integrable (by norm_num), ?_⟩
  intro i H DH _hH hDH
  have hder := horizontalLpDerivatives_of_spatial_weakGradient Q hQ hfm hGm hf hG hweak i
  have hparts := horizontalGenerators_integration_by_parts Q hQ i H DH
    (hf.toLp f) ((hG i).toLp (fun ω => G ω i)) hDH hder
  calc
    (∫ ω, f ω * DH ω ∂Q) = ∫ ω, DH ω * hf.toLp f ω ∂Q := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with ω hω
      rw [hω, mul_comm]
    _ = -(∫ ω, H ω * (hG i).toLp (fun ω => G ω i) ω ∂Q) := hparts.2.2
    _ = -(∫ ω, G ω i * H ω ∂Q) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [(hG i).coeFn_toLp] with ω hω
      rw [hω, mul_comm]

end EinsteinRelation.Correctors
