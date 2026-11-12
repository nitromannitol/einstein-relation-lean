import EinsteinRelation.Correctors.WeakTimeConstant
import EinsteinRelation.Correctors.PrimitiveTimeWeakEquation

/-! Fundamental theorem from the actual scalar distributional time equation;
source `paper/main.tex:808–816`. -/
open MeasureTheory Filter Topology
namespace EinsteinRelation.Correctors

theorem integral_eq_sub_of_weak_time_derivative {a b : ℝ} (hab : a < b)
    (f g : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc a b))
    (hg : IntegrableOn g (Set.Icc a b))
    (hweak : ∀ η : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      tsupport η ⊆ Set.Ioo a b →
      (∫ t in Set.Ioo a b, f t * deriv η t) =
        -(∫ t in Set.Ioo a b, g t * η t)) :
    (∫ t in Set.Icc a b, g t) = f b - f a := by
  let F : ℝ → ℝ := fun t => ∫ s in a..t, g s
  have hgi : IntervalIntegrable g volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mpr hg
  have hF : ContinuousOn F (Set.Icc a b) := by
    simpa only [Set.uIcc_of_le hab.le] using
      (intervalIntegral.continuousOn_primitive_interval (a := a) (b := b) (f := g) (μ := volume) (by simpa only [Set.uIcc_of_le hab.le] using hg))
  have heq := endpoints_eq_of_integral_mul_deriv_eq_zero hab (fun t => f t-F t)
    (hf.sub hF) (by
      intro η hη hηc hηs
      change (∫ t in a..b, (f t-F t) * deriv η t) = 0
      have hd : Continuous (deriv η) :=
        (hη.of_le (WithTop.coe_le_coe.mpr (le_top (a := (1 : ℕ∞))))).continuous_deriv le_rfl
      have hfη : IntervalIntegrable (fun t => f t * deriv η t) volume a b := (hf.mul hd.continuousOn).intervalIntegrable_of_Icc hab.le
      have hFη : IntervalIntegrable (fun t => F t * deriv η t) volume a b := (hF.mul hd.continuousOn).intervalIntegrable_of_Icc hab.le
      have hfw : (∫ t in a..b, f t * deriv η t) = -(∫ t in a..b, g t * η t) := by
        simpa only [intervalIntegral.integral_of_le hab.le,
          ← integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioo] using
          hweak η hη hηc hηs
      have hFw := intervalPrimitive_weak_equation hab g hgi η hη hηc hηs
      simp_rw [sub_mul]
      rw [intervalIntegral.integral_sub hfη hFη, hfw]
      change -(∫ t in a..b, g t * η t) -
        (∫ t in a..b, (∫ s in a..t, g s) * deriv η t) = 0
      rw [hFw, sub_self])
  have hFa : F a = 0 := intervalIntegral.integral_same
  have hFb : F b = ∫ t in Set.Icc a b, g t := by
    dsimp [F]
    rw [intervalIntegral.integral_of_le hab.le, integral_Icc_eq_integral_Ioc]
  change f b-F b = f a-F a at heq
  rw [hFa, hFb] at heq
  linarith

end EinsteinRelation.Correctors
