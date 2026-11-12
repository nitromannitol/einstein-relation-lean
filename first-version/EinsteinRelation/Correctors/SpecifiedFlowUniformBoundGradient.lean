import EinsteinRelation.Correctors.PrescribedGradientRectangularEndpoint
import EinsteinRelation.Correctors.PrescribedRectangularCutoff
import EinsteinRelation.Correctors.PrescribedBallCutoff
import EinsteinRelation.Correctors.PrescribedRectangularMoments

/-! # Uniform gradient moments of a specified semigroup flow

Source: `paper/main.tex:798–806,850–852`. A supplied semigroup flow with a
supplied prescribed-time weak gradient and a uniform sup bound has uniform
unit-ball gradient moments for `t ≥ 1`. The constant does not depend on the
bound, the probability law, or the flow. The scalar energy estimate on a fixed
rectangle transfers through the deterministic endpoint inequality.
-/

open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- A specified semigroup flow with uniformly bounded values has uniform
unit-ball gradient moments for all `t ≥ 1`, with the constant independent of
the bound and of the probability law.
Source: `paper/main.tex:798–806,850–852`. -/
theorem specifiedSemigroupFlow_uniform_bound_gradient (d : Nat) (K : Real) (hK : 0 < K) :
    ∃ D : Real, 0 < D ∧
    ∀ (P : Measure (Coefficient d K)), IsProbabilityMeasure P →
    ∀ (g : Coefficient d K → Vec d → Vec d)
      (u : Coefficient d K → Real × Vec d → Real)
      (G H : Coefficient d K → Real × Vec d → Vec d),
    Measurable (fun z : Coefficient d K × (Real × Vec d) => u z.1 z.2) →
    Measurable (fun z : Coefficient d K × (Real × Vec d) => H z.1 z.2) →
    (∀ᵐ A ∂P, IsSemigroupSolution A (g A) (u A) (G A)) →
    (∀ᵐ A ∂P, ∀ t : Real, 0 < t → HasWeakGradient Set.univ
      (fun x => u A (t,x)) (fun x => H A (t,x))) →
    ∀ B : Real, 0 ≤ B →
    (∀ᵐ A ∂P, ∀ t : Real, 0 < t → ∀ x : Vec d, |u A (t,x)| ≤ B) →
    ∀ (m t : Real), 2 ≤ m → 1 ≤ t →
    MemLp (fun A => vectorRms volume (originBall d 1) (fun x => H A (t,x)))
      (ENNReal.ofReal m) P ∧
    eLpNorm (fun A => vectorRms volume (originBall d 1) (fun x => H A (t,x)))
      (ENNReal.ofReal m) P ≤ ENNReal.ofReal (D*B) := by
  obtain ⟨ζ,M,hM,hζ,hζc,hζs,_,hζ1,hζD⟩ :=
    exists_prescribed_rectangular_cutoff d K
  obtain ⟨χ,N,hN,hχ,hχb,hχ1,hχD⟩ := exists_prescribed_spatial_ball_cutoff d 1 zero_lt_one
  have hχ' : IsSpatialTest (originBall d 2) χ := by simpa only [mul_one] using hχ
  obtain ⟨D,hD,henergy⟩ := semigroupSolution_prescribed_rectangular_scalar_le
    hK ζ hM hζ hζc hζs hζ1 hζD hχ' hχb hχ1 hN hχD
  refine ⟨D,hD,?_⟩
  intro P hP g u G H hum hHm hsol hHw B hB hub m t hm ht
  have hval : ∀ s : ℝ, (1/2 : ℝ) ≤ s → ∀ x : Vec d,
      MemLp (fun A => u A (s,x)) (ENNReal.ofReal m) P ∧
      eLpNorm (fun A => u A (s,x)) (ENNReal.ofReal m) P ≤ ENNReal.ofReal B := by
    intro s hs x
    have hm' : AEStronglyMeasurable (fun A => u A (s,x)) P :=
      (hum.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    have hb : ∀ᵐ A ∂P, ‖u A (s,x)‖ ≤ B := by
      filter_upwards [hub] with A hA
      simpa only [Real.norm_eq_abs] using hA s (by linarith only [hs]) x
    refine ⟨MemLp.of_bound hm' _ hb, ?_⟩
    simpa only [measure_univ, ENNReal.one_rpow, one_mul] using
      eLpNorm_le_of_ae_bound (p := ENNReal.ofReal m) hb
  have hbound : ∀ᵐ A ∂P, vectorRms volume (originBall d 1) (fun x => H A (t,x)) ≤
      D * scalarRms volume (Set.Ioo (1/2 : ℝ) (5/4) ×ˢ originBall d 4)
        (fun z => u A (z.1+(t-1),z.2)) := by
    filter_upwards [hsol,hHw] with A hA hw
    exact henergy A _ (u A) (G A) hA t ht _ (hw t (zero_lt_one.trans_le ht))
  exact prescribed_rectangular_scalar_to_gradient_moments_probability P hP u H hum hHm
    hD.le hB hm ht hval hbound

end EinsteinRelation.Correctors
