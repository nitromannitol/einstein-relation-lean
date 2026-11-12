import EinsteinRelation.Correctors.SpecifiedFlowUniformBoundGradient
import EinsteinRelation.Correctors.SpecifiedFlowPositiveTimeGradient

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- A bounded specified flow with scalar decay has sharp gradient decay at
all prescribed times `t ≥ 1`. This form applies directly to spatially
translated flows and retains their supplied weak gradient. Source:
`paper/main.tex:798–806,850–852`. -/
theorem specifiedSemigroupFlow_bounded_prescribed_gradient_decay
    (hreg : ParabolicLargeScale) (d : ℕ) (hd : 2 ≤ d)
    (K s : ℝ) (hK : 1 < K) (hs : 0 < s) (hs2 : s < 2) :
    ∃ J : ℝ → ℝ, (∀ m : ℝ, 2 ≤ m → 0 < J m) ∧
      ∀ P : Measure (Coefficient d K), IsAdmissibleLaw P →
      ∀ (g : Coefficient d K → Vec d → Vec d)
        (u : Coefficient d K → ℝ × Vec d → ℝ)
        (H : Coefficient d K → ℝ × Vec d → Vec d),
        Measurable (fun z : Coefficient d K × (ℝ × Vec d) => u z.1 z.2) →
        Measurable (fun z : Coefficient d K × (ℝ × Vec d) => H z.1 z.2) →
        (∀ᵐ A ∂P, IsSemigroupSolution A (g A) (u A) (H A)) →
        (∀ᵐ A ∂P, ∀ t : ℝ, 0 < t → HasWeakGradient Set.univ
          (fun x => u A (t,x)) (fun x => H A (t,x))) →
        ∀ B : ℝ, 0 ≤ B →
        (∀ᵐ A ∂P, ∀ t : ℝ, 0 < t → ∀ x : Vec d, |u A (t,x)| ≤ B) →
        ∀ F : ℝ → ℝ, (∀ m : ℝ, 0 < m → 0 < F m) →
        (∀ m : ℝ, 0 < m → ∀ t : ℝ, 1 ≤ t → ∀ x : Vec d,
          MemLp (fun A => u A (t,x)) (ENNReal.ofReal m) P ∧
          eLpNorm (fun A => u A (t,x)) (ENNReal.ofReal m) P ≤
            ENNReal.ofReal (F m*t^(-(1 : ℝ)/2-(d : ℝ)/4))) →
        ∀ (m t : ℝ), 2 ≤ m → 1 ≤ t →
          MemLp (fun A => vectorRms volume (originBall d 1) (fun x => H A (t,x)))
            (ENNReal.ofReal m) P ∧
          eLpNorm (fun A => vectorRms volume (originBall d 1) (fun x => H A (t,x)))
            (ENNReal.ofReal m) P ≤ ENNReal.ofReal
              ((J m*(B+F (2*m)))*t^(-(1 : ℝ)-(d : ℝ)/4)) := by
  obtain ⟨D,hD,hbounded⟩ := specifiedSemigroupFlow_uniform_bound_gradient d K (zero_lt_one.trans hK)
  obtain ⟨J,hJ,hlate⟩ := specifiedSemigroupFlow_positive_time_gradient_decay hreg d hd K s hK hs hs2
  let a : ℝ := 1+(d : ℝ)/4
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  refine ⟨fun m => max (D*(12 : ℝ)^a) (J m),?_,?_⟩
  · intro m hm
    exact (hJ m hm).trans_le (le_max_right _ _)
  intro P hP g u H hum hHm hsol hHw B hB hub F hF hval m t hm ht
  have hF2 : 0 < F (2*m) := hF _ (by linarith only [hm])
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hC : 0 < max (D*(12 : ℝ)^a) (J m) := (hJ m hm).trans_le (le_max_right _ _)
  by_cases htl : 12 ≤ t
  · have he := hlate P hP g u H H hum hHm hHm hsol hHw F hF hval m hm t htl
    refine ⟨he.1,he.2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ht0.le _)
    have hj := le_max_right (D*(12 : ℝ)^a) (J m)
    nlinarith only [hj,hC,hF2,hB]
  · have ht12 : t ≤ 12 := (lt_of_not_ge htl).le
    have he := hbounded P hP.1 g u H H hum hHm hsol hHw B hB hub m t hm ht
    refine ⟨he.1,he.2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    have hpow : (12 : ℝ)^(-a) ≤ t^(-a) :=
      Real.rpow_le_rpow_of_nonpos ht0 ht12 (neg_nonpos.mpr ha)
    have hid : (12 : ℝ)^a*(12 : ℝ)^(-a) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 12),add_neg_cancel,Real.rpow_zero]
    have hsmall : D*B ≤ (D*(12 : ℝ)^a)*B*t^(-a) := by
      calc
        D*B = D*B*((12 : ℝ)^a*(12 : ℝ)^(-a)) := by rw [hid,mul_one]
        _ ≤ D*B*((12 : ℝ)^a*t^(-a)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg (by norm_num) _))
            (mul_nonneg hD.le hB)
        _ = _ := by ring
    have hcoeff : (D*(12 : ℝ)^a)*B ≤ max (D*(12 : ℝ)^a) (J m)*(B+F (2*m)) := by
      have hc := le_max_left (D*(12 : ℝ)^a) (J m)
      nlinarith only [hc,hC,hF2,hB]
    convert hsmall.trans (mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg ht0.le _)) using 1
    congr 2
    dsimp only [a]
    ring

end EinsteinRelation.Correctors
