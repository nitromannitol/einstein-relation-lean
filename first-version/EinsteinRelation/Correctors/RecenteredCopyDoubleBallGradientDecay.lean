import EinsteinRelation.Correctors.PhysicalCouplingIntegratedGradientDecay
import EinsteinRelation.Correctors.RecenteredPhysicalCopies
import EinsteinRelation.Correctors.PairedEnergyBallCutoff
import EinsteinRelation.Correctors.EuclideanBallAverageComparison
import EinsteinRelation.Correctors.SemigroupPrescribedGradient

/-! # The manuscript double-ball finite-time paired gradient

Source: `paper/main.tex:834–857,886–894`. The physical observation radius
is `r₀ R`; the normalized PDE radius is `R`. Marginals, agreement, cutoff,
zero trace, integrability and the inner-ball energy transfer are derived.
-/

open MeasureTheory Set
open scoped ENNReal
namespace EinsteinRelation.Correctors
open External.AKM ReductionImageV3 Environment.AKMTestIntegralSupport
open NormalizedSpatialRepresentativeSupport

/-- The literal same-flow integrated gradient has the sharp paired moment
rate under the actual recentered copy law. The remaining scalar large-time
premise refers to this very flow. Source: `paper/main.tex:834–857,886–894`. -/
theorem recenteredPhysicalCopy_doubleBall_integrated_gradient_decay
    (d n : ℕ) (hd : 2 ≤ d) (hn : 1+(d : ℝ)/2 < (n : ℝ))
    (L r₀ C : ℝ) (hC : 0 ≤ C) :
    ∃ B : ℝ, 0 < B ∧ ∀ (Q : EnvironmentLaw d L r₀) (i : Fin d)
      (u : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → ℝ)
      (G : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → Vec d),
      Measurable (fun z : Coefficient d (AKMUpperEllipticity L) ×
        (ℝ × Vec d) => u z.1 z.2) →
      Measurable (fun z : Coefficient d (AKMUpperEllipticity L) ×
        (ℝ × Vec d) => G z.1 z.2) →
      (∀ᵐ A ∂actualCoefficientLaw Q,
        IsSemigroupSolution A (fun x => (A x).mulVec (unitVector i)) (u A) (G A) ∧
        HasCanonicalKernelRepresentation A (fun x => (A x).mulVec (unitVector i)) (u A)) →
      ∀ p : ℝ, 2 ≤ p →
      (∀ t : ℝ, 1 ≤ t → ∀ x : Vec d,
        eLpNorm (fun A => u A (t,x)) (ENNReal.ofReal p) (actualCoefficientLaw Q) ≤
          ENNReal.ofReal (C*t^(-(1 : ℝ)/2-(d : ℝ)/4))) →
      ∀ R : ℝ, 1 ≤ R → ∀ y : Point d,
      let F := fun A : PhysicalField d L × PhysicalField d L =>
        Real.sqrt (⨍ x in originBall d (2*R), euclideanSq
          (∫ t in Icc (0 : ℝ) (4*R^2),
            G (project (r₀ := r₀) Q.ellipticity_parameter A.1) (t,x) -
              G (project (r₀ := r₀) Q.ellipticity_parameter A.2) (t,x)))
      MemLp F (ENNReal.ofReal p) (recenteredPhysicalCopyLaw Q (r₀*R) y) ∧
        eLpNorm F (ENNReal.ofReal p) (recenteredPhysicalCopyLaw Q (r₀*R) y) ≤
          ENNReal.ofReal (B*R^(-(d : ℝ)/2)) := by
  obtain ⟨D,_,hcut⟩ := exists_paired_energy_ball_cutoff d
  obtain ⟨B,hB,hbound⟩ := physicalCoupling_paired_canonical_integrated_gradient_decay
    d n hd hn L r₀ C (D/2) hC
  refine ⟨Real.sqrt ((2 : ℝ)^d)*B, mul_pos (Real.sqrt_pos.mpr (pow_pos two_pos d)) hB, ?_⟩
  intro Q i u G hum hGm hflow p hp hlate R hR y
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hr₀ : r₀ ≠ 0 := (zero_lt_one.trans_le Q.range_parameter).ne'
  obtain ⟨hμ,_,hfst,hsnd,hEq⟩ := recenteredPhysicalCopy_properties Q (r₀*R) y
  have hEq' : ∀ᵐ A ∂recenteredPhysicalCopyLaw Q (r₀*R) y,
      EqOn (project (r₀ := r₀) Q.ellipticity_parameter A.1)
        (project (r₀ := r₀) Q.ellipticity_parameter A.2) (originBall d (4*R)) := by
    filter_upwards [hEq] with A hA
    apply hA.mono
    intro x hx
    change euclideanNorm x < 8*(r₀*R)/r₀
    rw [show 8*(r₀*R)/r₀ = 8*R by field_simp]
    exact lt_of_lt_of_le hx (by linarith)
  have hopen (s : ℝ) : IsOpen (originBall d s) := by
    unfold originBall euclideanNorm euclideanSq dot
    exact isOpen_lt (by fun_prop) continuous_const
  have heq (s : ℝ) : originBall d s = ball (0 : Vec d) s := by
    simp only [originBall,ball,sub_zero]
  have hvol (s : ℝ) (hs : 0 < s) : 0 < volume.real (originBall d s) := by
    rw [heq]
    exact ball_volume_pos_finite d s hs
  have hc := isCompact_closure_originBall d (4*R)
  letI : IsFiniteMeasure (volume.restrict (originBall d (4*R))) :=
    isFiniteMeasure_restrict.mpr (ne_top_of_le_ne_top
      (hc.measure_ne_top (μ := volume)) (measure_mono subset_closure))
  obtain ⟨χ,hχ,hχb,hχ1,hχD⟩ := hcut (2*R) (by positivity)
  have hχ' : IsSpatialTest (originBall d (4*R)) χ := by
    simpa only [show 2*(2*R) = 4*R by ring] using hχ
  have hχD' (x : Vec d) : euclideanSq (gradient χ x) ≤ ((D/2)/R)^2 := by
    simpa only [show D/(2*R) = (D/2)/R by ring] using hχD x
  have hsub : originBall d (2*R) ⊆ originBall d (4*R) := by
    intro x hx
    change euclideanNorm x < 2*R at hx
    change euclideanNorm x < 4*R
    linarith
  have h := hbound Q i u G hum hGm hflow p hp hlate
    (recenteredPhysicalCopyLaw Q (r₀*R) y) hμ hfst hsnd R hR
    (originBall d (4*R)) (hopen _) hc (hvol _ (by positivity)) hEq'
    χ hχ' hχb hχD' (originBall d (2*R)) (hopen _).measurableSet hsub (hvol _ (by positivity)) hχ1
  have hratio : volume.real (originBall d (4*R)) / volume.real (originBall d (2*R)) =
      (2 : ℝ)^d := by
    rw [heq,heq,show 4*R = 2*(2*R) by ring,
      euclideanBall_volume_real _ (by positivity),
      euclideanBall_volume_real (2*R) (by positivity),mul_pow]
    have hunit := ball_volume_pos_finite d 1 zero_lt_one
    have hpow : (2*R)^d ≠ 0 := pow_ne_zero d (by positivity)
    field_simp
  simpa only [hratio,mul_assoc] using h

end EinsteinRelation.Correctors
