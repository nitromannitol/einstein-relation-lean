import EinsteinRelation.Correctors.CanonicalGradientRegularRepresentative
import EinsteinRelation.Correctors.HolderFluxAlgebra
import EinsteinRelation.Correctors.HolderCentering
import Mathlib.MeasureTheory.Measure.OpenPos

/-! Source: `paper/main.tex:735-743`. The physical flux of the regular
canonical gradient is a jointly measurable continuous, locally Hölder
version of the centered stationary corrector flux. -/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger

/-- The actual coefficient acting on the selected canonical affine gradient. -/
def canonicalRegularCenteredFlux
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (ω : FieldPair d) (x : Vec d) : Vec d :=
  (ω.1 x).mulVec (canonicalAffineGradientRegularRepresentative Q i ω x) -
    (expectedCorrectorFlux Q i).ofLp

/-- Joint Borel measurability of the regular physical flux. -/
theorem measurable_canonicalRegularCenteredFlux
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    Measurable (fun p : Vec d × FieldPair d => canonicalRegularCenteredFlux Q i p.2 p.1) := by
  have hc : Continuous (fun p : Vec d × FieldPair d => p.2.1 p.1) := by fun_prop
  exact ((show Continuous (fun p : Mat d × Vec d => p.1.mulVec p.2) from
    continuous_fst.matrix_mulVec continuous_snd).measurable.comp
      (hc.measurable.prodMk (measurable_canonicalAffineGradientRegularRepresentative Q i))).sub
        measurable_const

/-- The centered canonical flux has a continuous locally Hölder version
on a single full-measure event, with its spatial volume class preserved. -/
theorem ae_canonicalRegularCenteredFlux
    (hP : BallPoincareEstimate) (h836 : InteriorRegularRepresentative)
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      Continuous (canonicalRegularCenteredFlux Q i ω) ∧
      ((fun x => (canonicalCorrectorFlux Q i (translate x ω) -
        expectedCorrectorFlux Q i).ofLp) =ᵐ[volume] canonicalRegularCenteredFlux Q i ω) ∧
      ∀ R : ℝ, 0 < R → ∃ K : ℝ, ∀ j,
        HolderBound (ball 0 R) (1 / 2) (fun x => canonicalRegularCenteredFlux Q i ω x j) K := by
  have hL : 0 ≤ L := zero_le_one.trans Q.ellipticity_parameter
  filter_upwards [ae_canonicalAffine_c1Alpha_representatives hP h836 Q i,
    ae_canonicalAffineGradientRegularRepresentative hP h836 Q i,
    ae_spatial_canonicalCorrectorFlux Q i measurable_id,
    ActualImageLpStateTransport.ae_reducedEnvironmentLaw_mem_image Q]
    with ω hlocal hG hflux himg
  obtain ⟨u, _, _, hu⟩ := hlocal
  obtain ⟨η, hη, hηeq⟩ := himg
  have hb := sourceReducedBound_support Q.ellipticity_parameter hη
  have hB : 0 < sourceReducedBound L := zero_lt_one.trans_le hb.1
  have hell : IsElliptic (sourceReducedBound L) ω.1 := by
    simpa only [← hηeq] using hb.2.1
  have hlip : IsOperatorLipschitz (Real.exp (2 * L) * (L + 2 * L ^ 2)) ω.1 := by
    simpa only [← hηeq] using hb.2.2.2.1
  refine ⟨(ω.1.continuous.matrix_mulVec hG.1).sub continuous_const, ?_, ?_⟩
  · filter_upwards [hflux, hG.2] with x hx hg
    change (canonicalCorrectorFlux Q i (translate x ω)).ofLp -
      (expectedCorrectorFlux Q i).ofLp =
      (ω.1 x).mulVec _ - (expectedCorrectorFlux Q i).ofLp
    have hx' : (canonicalCorrectorFlux Q i (translate x ω)).ofLp =
        (ω.1 x).mulVec (unitVector i +
          ((canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
            (reducedEnvironmentLaw Q)) (translate x ω)).ofLp) := by
      simpa only [id_eq, WithLp.ofLp_add, correctorUnitVector, WithLp.ofLp_toLp] using hx
    rw [hx', hg]
  · intro R hR
    obtain ⟨v, h, hreg, _, hheq⟩ := hu R hR
    obtain ⟨H, hH⟩ := hreg.2
    have hopen : IsOpen (ball (0 : Vec d) R) := by
      unfold ball euclideanNorm euclideanSq dot
      exact isOpen_lt (by fun_prop) continuous_const
    have hh : ContinuousOn h (ball 0 R) :=
      continuousOn_pi.mpr (fun j => continuousOn_of_holderBound (by norm_num) (hH j))
    have hpoint : Set.EqOn (canonicalAffineGradientRegularRepresentative Q i ω) h
        (ball 0 R) := Measure.eqOn_open_of_ae_eq
      (Filter.EventuallyEq.trans (ae_restrict_of_ae hG.2.symm) hheq.symm)
      hopen hG.1.continuousOn hh
    obtain ⟨C, hC⟩ := exists_holderBound_mulVec (ball 0 R) (1 / 2)
      (sourceReducedBound L + (Real.exp (2 * L) * (L + 2 * L ^ 2)) * (4 * (R / 2) + 1))
      H (fun x => ω.1 x) h
      (by simpa only [show (2 : ℝ) * (R / 2) = R by ring] using
        holderBound_half_ball_of_isElliptic_lipschitz hB (by positivity) (half_pos hR) hell hlip)
      hH
    obtain ⟨D, hD⟩ := exists_holderBound_sub_const (ball 0 R)
      (fun x => (ω.1 x).mulVec (h x)) (expectedCorrectorFlux Q i).ofLp (1 / 2) C hC
    refine ⟨D, fun j => ?_⟩
    obtain ⟨S, J, hS, hJ, hSJ, hs, hj⟩ := hD j
    refine ⟨S, J, hS, hJ, hSJ, ?_, ?_⟩
    · intro x hx
      simpa only [canonicalRegularCenteredFlux, hpoint hx, Pi.sub_apply] using hs x hx
    · intro x hx y hy
      simpa only [canonicalRegularCenteredFlux, hpoint hx, hpoint hy, Pi.sub_apply] using hj x hx y hy

end EinsteinRelation.Correctors
