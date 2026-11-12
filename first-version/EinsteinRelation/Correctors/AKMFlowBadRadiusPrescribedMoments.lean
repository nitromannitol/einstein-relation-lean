import EinsteinRelation.Correctors.PrescribedGradientDoubleCylinder
import EinsteinRelation.Correctors.AKMFlowDoubleCylinderMoments
import EinsteinRelation.Correctors.AKMRandomRadiusTail
import EinsteinRelation.Correctors.RandomRadiusCutoffMoments

/-! # Prescribed-time moments on the bad-radius event

Source: `paper/main.tex:798–806`. Local endpoint energy bounds the actual
prescribed-time gradient. Hölder and the random-radius tail recover the
inverse-radius factor on the complementary event.
-/

open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Prescribed-time unit-ball gradient moments on the large-radius event.
The supplied scalar flow and its actual prescribed-time gradient are retained.
Source: `paper/main.tex:798–806`. -/
theorem semigroupFlow_bad_radius_prescribed_unit_moment_le
    (d : ℕ) (K : ℝ) (hK : 0 < K) {χ : Vec d → ℝ}
    (hχ : IsSpatialTest (originBall d 2) χ) (hχb : ∀ x, |χ x| ≤ 1)
    (hχV : ∀ x ∈ originBall d 1, χ x = 1)
    {L : ℝ} (hL : 0 ≤ L) (hχD : ∀ x, euclideanNorm (gradient χ x) ≤ L) :
    ∃ D : ℝ, 0 < D ∧
      ∀ (P : Measure (Coefficient d K)), IsProbabilityMeasure P →
      ∀ (g : Coefficient d K → Vec d → Vec d)
        (u : Coefficient d K → ℝ × Vec d → ℝ)
        (G H : Coefficient d K → ℝ × Vec d → Vec d),
      Measurable (fun z : Coefficient d K × (ℝ × Vec d) => u z.1 z.2) →
      Measurable (fun z : Coefficient d K × (ℝ × Vec d) => G z.1 z.2) →
      Measurable (fun z : Coefficient d K × (ℝ × Vec d) => H z.1 z.2) →
      (∀ᵐ A ∂P, IsSemigroupSolution A (g A) (u A) (G A)) →
      (∀ᵐ A ∂P, ∀ t : ℝ, 0 < t → HasWeakGradient Set.univ
        (fun x => u A (t,x)) (fun x => H A (t,x))) →
      ∀ (X : Coefficient d K → ℝ), Measurable X → (∀ A, 0 ≤ X A) →
      ∀ (s θ : ℝ), 0 < s → 0 < θ → StretchedExponentialBound P s θ X →
      ∀ (m : ℝ), 2 ≤ m → ∀ r : ℝ, 2 ≤ r → ∀ C : ℝ, 0 ≤ C →
      (∀ t : ℝ, r^2 ≤ t → ∀ x : Vec d,
        MemLp (fun A => u A (t,x)) (ENNReal.ofReal (2*m)) P ∧
        eLpNorm (fun A => u A (t,x)) (ENNReal.ofReal (2*m)) P ≤
          ENNReal.ofReal (C * t^(-(1 : ℝ)/2 - (d : ℝ)/4))) →
      MemLp ({A | r < 4*X A}.indicator (fun A =>
        vectorRms volume (originBall d 1) (fun x => H A (3*r^2,x))))
          (ENNReal.ofReal m) P ∧
      eLpNorm ({A | r < 4*X A}.indicator (fun A =>
        vectorRms volume (originBall d 1) (fun x => H A (3*r^2,x))))
          (ENNReal.ofReal m) P ≤
        ENNReal.ofReal
          ((4 * ((2*((2*m)/s)^((2*m)/s))^(1/(2*m))*θ) * D * C / r) *
            (r^2)^(-(1 : ℝ)/2 - (d : ℝ)/4)) := by
  obtain ⟨D₁,hD₁,hend⟩ := semigroupSolution_prescribed_double_cylinder_le
    hK hχ hχb hχV hL hχD
  obtain ⟨D₂,hD₂,hcyl⟩ := semigroupFlow_shifted_double_cylinder_moment_le d K hK
  refine ⟨D₁*D₂,mul_pos hD₁ hD₂,?_⟩
  intro P hP g u G H hum hGm hHm hsol hHw X hXm hX s θ hs hθ htail m hm r hr C hC hval
  have hm0 : 0 < m := zero_lt_two.trans_le hm
  have hm2 : 0 < 2*m := mul_pos two_pos hm0
  have hr0 : 0 < r := by linarith only [hr]
  let E := fun A => vectorRms volume (originBall d 1) (fun x => H A (3*r^2,x))
  let F := fun A => vectorRms volume (Set.Ioo (8 : ℝ) 12 ×ˢ originBall d 2)
    (fun z => G A (z.1+(3*r^2-12),z.2))
  have hEm : Measurable E := by
    have hrep : Measurable (fun z : Coefficient d K × Vec d => H z.1 (3*r^2,z.2)) :=
      hHm.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
    have he : Measurable (fun z : Coefficient d K × Vec d =>
        euclideanSq (H z.1 (3*r^2,z.2))) := by
      unfold euclideanSq dot
      exact Finset.measurable_sum _ fun j _ =>
        ((measurable_pi_apply j).comp hrep).mul ((measurable_pi_apply j).comp hrep)
    have hi := (he.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (originBall d 1))).measurable
    simpa only [E,vectorRms,average_eq,measureReal_restrict_apply_univ,smul_eq_mul] using
      (measurable_const.mul hi).sqrt
  have hdom : ∀ᵐ A ∂P, ‖E A‖ ≤ D₁*‖F A‖ := by
    filter_upwards [hsol,hHw] with A hA hHA
    have hh := (hend A _ (u A) (G A) hA r hr _
      (hHA (3*r^2) (by nlinarith only [hr]))).2
    simpa only [E,F,vectorRms,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)] using hh
  have hF := hcyl P hP g u G hum hGm hsol (2*m) (by linarith only [hm]) r hr C hC hval
  have hELp : MemLp E (ENNReal.ofReal (2*m)) P :=
    hF.1.of_le_mul hEm.aestronglyMeasurable hdom
  have hEnorm : eLpNorm E (ENNReal.ofReal (2*m)) P ≤
      ENNReal.ofReal (D₁*D₂*C*(r^2)^(-(1 : ℝ)/2-(d : ℝ)/4)) := by
    calc
      _ ≤ ENNReal.ofReal D₁ * eLpNorm F (ENNReal.ofReal (2*m)) P :=
        eLpNorm_le_mul_eLpNorm_of_ae_le_mul hdom _
      _ ≤ ENNReal.ofReal D₁ * ENNReal.ofReal
          (D₂*C*(r^2)^(-(1 : ℝ)/2-(d : ℝ)/4)) := mul_le_mul_right hF.2 _
      _ = _ := by rw [← ENNReal.ofReal_mul hD₁.le]; congr 1; ring
  have hXLp := memLp_of_stretchedExponential P hs hθ hm2
    hXm.aestronglyMeasurable (Filter.Eventually.of_forall hX) htail
  have hXnorm := eLpNorm_le_of_stretchedExponential P hs hθ hm2
    (Filter.Eventually.of_forall hX) htail
  have hbad := badRadius_eLpNorm_le hXm hX hm0 hr0 hXLp hELp
  refine ⟨hbad.1,?_⟩
  have hB : 0 ≤ (2*((2*m)/s)^((2*m)/s))^(1/(2*m))*θ := by positivity
  calc
    _ ≤ _ := hbad.2
    _ ≤ ENNReal.ofReal (4/r) *
        (ENNReal.ofReal ((2*((2*m)/s)^((2*m)/s))^(1/(2*m))*θ) *
          ENNReal.ofReal (D₁*D₂*C*(r^2)^(-(1 : ℝ)/2-(d : ℝ)/4))) := by
      exact mul_le_mul_right (mul_le_mul' hXnorm hEnorm) _
    _ = _ := by
      rw [← ENNReal.ofReal_mul hB,
        ← ENNReal.ofReal_mul (div_nonneg (by norm_num) hr0.le)]
      congr 1
      ring

end EinsteinRelation.Correctors
