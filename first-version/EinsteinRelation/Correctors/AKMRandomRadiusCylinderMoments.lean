import EinsteinRelation.Correctors.AKMFlowCylinderGradientMoments
import EinsteinRelation.Correctors.AKMRandomRadiusTail
import EinsteinRelation.Correctors.ParabolicCylinderTranslation
import EinsteinRelation.Correctors.ParabolicUnitScaleGradient
import EinsteinRelation.Correctors.RandomRadiusCutoffMoments

/-! # Random-radius factors for the selected column flow

Source: `paper/main.tex:798–806`. The random radius from Remark 8.8 and
the actual cylinder gradient of the source-selected flow have all finite
moments. Hölder's inequality absorbs their product without changing the
diffusive decay rate. The spatial time-slice comparison keeps its
almost-everywhere time qualifier.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The same source-selected flow satisfies the random-radius unit-ball
comparison and the moment bound on its right-hand side. The constants
precede the law, direction and scale. No positive-time gradient continuity
or prescribed-time estimate is assumed. Source: `paper/main.tex:798–806`. -/
theorem parabolicSemigroupDecay_random_radius_cylinder_moments
    (hflow : ParabolicSemigroupDecay) (hreg : ParabolicLargeScale)
    (d : ℕ) (hd : 2 ≤ d) (K s : ℝ) (hK : 1 < K)
    (hs : 0 < s) (hs2 : s < 2) :
    ∃ L : ℝ, 0 < L ∧ ∃ F : ℝ → ℝ, (∀ m : ℝ, 0 < m → 0 < F m) ∧
      ∃ C : ℝ → ℝ, (∀ m : ℝ, 2 ≤ m → 0 < C m) ∧
      ∀ P : Measure (Coefficient d K), IsAdmissibleLaw P → ∀ i : Fin d,
        ∃ (X : Coefficient d K → ℝ)
          (u : Coefficient d K → ℝ × Vec d → ℝ)
          (G : Coefficient d K → ℝ × Vec d → Vec d),
          Measurable X ∧ (∀ A, 1 ≤ X A) ∧ StretchedExponentialBound P s L X ∧
          Measurable (fun z : Coefficient d K × (ℝ × Vec d) => u z.1 z.2) ∧
          Measurable (fun z : Coefficient d K × (ℝ × Vec d) => G z.1 z.2) ∧
          (∀ᵐ A ∂P, IsSemigroupSolution A
            (fun x => (A x).mulVec (unitVector i)) (u A) (G A)) ∧
          (∀ m : ℝ, 0 < m → ∀ t : ℝ, 1 ≤ t → ∀ x : Vec d,
            MemLp (fun A => u A (t,x)) (ENNReal.ofReal m) P ∧
            eLpNorm (fun A => u A (t,x)) (ENNReal.ofReal m) P ≤
              ENNReal.ofReal (F m * t^(-(1 : ℝ)/2 - (d : ℝ)/4))) ∧
          (∀ᵐ A ∂P, ∀ r : ℝ, 4*X A ≤ r →
            ∀ᵐ τ ∂volume.restrict (Set.Ioo (-((2*X A)^2)/4) 0),
              vectorRms volume (originBall d 1) (fun x => G A (τ+3*r^2,x)) ≤
                L * (X A)^((d : ℝ)/2) * vectorRms volume
                  (Set.Ioo (2*r^2) (3*r^2) ×ˢ originBall d r) (G A)) ∧
          ∀ m : ℝ, 2 ≤ m → ∀ r : ℝ, 1 ≤ r →
            MemLp (fun A => (X A)^((d : ℝ)/2) * vectorRms volume
              (Set.Ioo (2*r^2) (3*r^2) ×ˢ originBall d r) (G A)) (ENNReal.ofReal m) P ∧
            eLpNorm (fun A => (X A)^((d : ℝ)/2) * vectorRms volume
              (Set.Ioo (2*r^2) (3*r^2) ×ˢ originBall d r) (G A)) (ENNReal.ofReal m) P ≤
                ENNReal.ofReal (C m / r * (r^2)^(-(1 : ℝ)/2 - (d : ℝ)/4)) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have ha : 0 < (d : ℝ)/2 := div_pos (zero_lt_two.trans_le hdR) two_pos
  obtain ⟨L,hL,hlarge⟩ := parabolicLargeScale_semigroup_unit_gradient
    hreg d hd K s hK hs (hs2.trans_le hdR)
  obtain ⟨F,hF,hflows⟩ := parabolicSemigroupDecay_actual_column_cylinder_gradient_moments
    hflow d hd K s hK hs hs2
  let B : ℝ → ℝ := fun m =>
    (2 * ((2*m)/(s/((d : ℝ)/2)))^((2*m)/(s/((d : ℝ)/2))))^(1/(2*m)) * L^((d : ℝ)/2)
  refine ⟨L,hL,F,hF,fun m => B m * F (2*m),?_,?_⟩
  · intro m hm
    have hm2 : 0 < 2*m := mul_pos two_pos (zero_lt_two.trans_le hm)
    have hb : 0 < B m := by
      apply mul_pos
      · apply Real.rpow_pos_of_pos
        exact mul_pos two_pos (Real.rpow_pos_of_pos (div_pos hm2 (div_pos hs ha)) _)
      · exact Real.rpow_pos_of_pos hL _
    exact mul_pos hb (hF (2*m) hm2)
  · intro P hP i
    obtain ⟨X,hXm,hX,htail,hcompare⟩ := hlarge P hP
    obtain ⟨u,G,hum,hGm,hsol,hval,hmom⟩ := hflows P hP i
    refine ⟨X,u,G,hXm,hX,htail,hum,hGm,hsol,hval,?_,?_⟩
    · filter_upwards [hcompare,hsol] with A hA hsolA
      intro r hr
      have hr0 : 0 < r := by linarith only [hr, hX A]
      have hb := hA _ _ _ hsolA r hr (3*r^2) (by nlinarith [sq_pos_of_pos hr0])
      simpa only [vectorRms_diffusive_backward_shift] using hb
    · intro m hm r hr
      have hm0 : 0 < m := zero_lt_two.trans_le hm
      have hm2 : 0 < 2*m := mul_pos two_pos hm0
      have hXmoms := radius_rpow_moments_of_stretchedExponential P hXm
        (fun A => zero_le_one.trans (hX A)) hs hL ha hm2 htail
      have hEmoms := hmom (2*m) (by linarith only [hm]) r hr
      haveI := holderTriple_double_ofReal hm0
      refine ⟨hEmoms.1.mul' hXmoms.1, ?_⟩
      have hprod : eLpNorm (fun A => (X A)^((d : ℝ)/2) * vectorRms volume
          (Set.Ioo (2*r^2) (3*r^2) ×ˢ originBall d r) (G A)) (ENNReal.ofReal m) P ≤
          eLpNorm (fun A => (X A)^((d : ℝ)/2)) (ENNReal.ofReal (2*m)) P *
            eLpNorm (fun A => vectorRms volume
              (Set.Ioo (2*r^2) (3*r^2) ×ˢ originBall d r) (G A)) (ENNReal.ofReal (2*m)) P :=
        eLpNorm_smul_le_mul_eLpNorm
          (𝕜 := ℝ) (E := ℝ) (μ := P)
          (p := ENNReal.ofReal (2*m)) (q := ENNReal.ofReal (2*m))
          (r := ENNReal.ofReal m)
          (f := fun A => vectorRms volume
            (Set.Ioo (2*r^2) (3*r^2) ×ˢ originBall d r) (G A))
          (φ := fun A => (X A)^((d : ℝ)/2)) hEmoms.1.1 hXmoms.1.1
      have hBm : 0 ≤ B m := by dsimp only [B]; positivity
      calc
        _ ≤ _ := hprod
        _ ≤ ENNReal.ofReal (B m) *
            ENNReal.ofReal (F (2*m)/r * (r^2)^(-(1 : ℝ)/2 - (d : ℝ)/4)) :=
          mul_le_mul' hXmoms.2 hEmoms.2
        _ = _ := by
          rw [← ENNReal.ofReal_mul hBm]
          congr 1
          ring

end EinsteinRelation.Correctors
