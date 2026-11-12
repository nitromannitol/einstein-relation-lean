import EinsteinRelation.Correctors.SpecifiedFlowPrescribedGradientDecay
import EinsteinRelation.Correctors.PrescribedGradientTimePower

open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport
/-- Prescribed late-time decay for the same supplied scalar flow.
Source: `paper/main.tex:798–806`. -/
theorem specifiedSemigroupFlow_positive_time_gradient_decay
    (hreg : ParabolicLargeScale) (d : ℕ) (hd : 2 ≤ d)
    (K s : ℝ) (hK : 1 < K) (hs : 0 < s) (hs2 : s < 2) :
    ∃ J : ℝ → ℝ, (∀ m : ℝ, 2 ≤ m → 0 < J m) ∧
      ∀ P : Measure (Coefficient d K), IsAdmissibleLaw P →
      ∀ (g : Coefficient d K → Vec d → Vec d)
        (u : Coefficient d K → ℝ × Vec d → ℝ)
        (G H : Coefficient d K → ℝ × Vec d → Vec d),
      Measurable (fun z : Coefficient d K × (ℝ × Vec d) => u z.1 z.2) →
      Measurable (fun z : Coefficient d K × (ℝ × Vec d) => G z.1 z.2) →
      Measurable (fun z : Coefficient d K × (ℝ × Vec d) => H z.1 z.2) →
      (∀ᵐ A ∂P, IsSemigroupSolution A (g A) (u A) (G A)) →
      (∀ᵐ A ∂P, ∀ t : ℝ, 0 < t → HasWeakGradient Set.univ
        (fun x => u A (t,x)) (fun x => H A (t,x))) →
      ∀ F : ℝ → ℝ, (∀ m : ℝ, 0 < m → 0 < F m) →
      (∀ m : ℝ, 0 < m → ∀ t : ℝ, 1 ≤ t → ∀ x : Vec d,
        MemLp (fun A => u A (t,x)) (ENNReal.ofReal m) P ∧
        eLpNorm (fun A => u A (t,x)) (ENNReal.ofReal m) P ≤
          ENNReal.ofReal (F m*t^(-(1 : ℝ)/2-(d : ℝ)/4))) →
      ∀ m : ℝ, 2 ≤ m → ∀ t : ℝ, 12 ≤ t →
        MemLp (fun A => vectorRms volume (originBall d 1) (fun x => H A (t,x)))
          (ENNReal.ofReal m) P ∧
        eLpNorm (fun A => vectorRms volume (originBall d 1) (fun x => H A (t,x)))
          (ENNReal.ofReal m) P ≤
            ENNReal.ofReal (J m*F (2*m)*t^(-(1 : ℝ)-(d : ℝ)/4)) := by
  obtain ⟨J,hJ,hbound⟩ := specifiedSemigroupFlow_prescribed_unit_gradient_decay
    hreg d hd K s hK hs hs2
  refine ⟨fun m => J m*(3 : ℝ)^(1+(d : ℝ)/4),?_,?_⟩
  · intro m hm
    exact mul_pos (hJ m hm) (Real.rpow_pos_of_pos (by norm_num) _)
  intro P hP g u G H hum hGm hHm hsol hHw F hF hval m hm t ht
  let r := Real.sqrt (t/3)
  have ht0 : 0 < t := by linarith only [ht]
  have hr0 : 0 < r := Real.sqrt_pos.mpr (div_pos ht0 (by norm_num))
  have hrsq : r^2 = t/3 := Real.sq_sqrt (by linarith only [ht] : 0 ≤ t/3)
  have hr : 2 ≤ r := by
    have hnr : 0 ≤ r := Real.sqrt_nonneg _
    nlinarith only [hrsq,hnr,ht]
  have htime : 3*r^2 = t := by rw [hrsq]; ring
  have he := hbound P hP g u G H hum hGm hHm hsol hHw F hF hval m hm r hr
  have hrate : J m*F (2*m)/r*(r^2)^(-(1 : ℝ)/2-(d : ℝ)/4) =
      (J m*(3 : ℝ)^(1+(d : ℝ)/4))*F (2*m)*t^(-(1 : ℝ)-(d : ℝ)/4) := by
    have h₁ : (1 : ℝ)/2-(-(1 : ℝ)/2-(d : ℝ)/4) = 1+(d : ℝ)/4 := by ring
    have h₂ : (-(1 : ℝ)/2-(d : ℝ)/4)-1/2 = -(1 : ℝ)-(d : ℝ)/4 := by ring
    simpa only [htime,h₁,h₂,mul_assoc,mul_comm,mul_left_comm] using
      prescribed_decay_radius_to_time (C := J m*F (2*m)) hr0 (-(1 : ℝ)/2-(d : ℝ)/4)
  simpa only [htime,hrate] using he

end EinsteinRelation.Correctors
