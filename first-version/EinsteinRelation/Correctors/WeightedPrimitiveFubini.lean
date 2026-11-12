import EinsteinRelation.Correctors.TimeTriangleFubini
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Fubini for a weighted time primitive; source `paper/main.tex:808–816,833–848`. -/
open MeasureTheory
namespace EinsteinRelation.Correctors

/-- A time primitive paired with a continuous weight equals a pairing with its tail integral. -/
theorem integral_primitive_mul_eq_integral_mul_tail {a b : ℝ} (hab : a ≤ b)
    (V W : ℝ → ℝ) (hV : IntervalIntegrable V volume a b)
    (hW : ContinuousOn W (Set.Icc a b)) :
    (∫ t in a..b, (∫ s in a..t, V s) * W t) =
      ∫ s in a..b, V s * (∫ t in s..b, W t) := by
  have hv : IntegrableOn V (Set.Icc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hV
  have hw : IntegrableOn W (Set.Icc a b) volume := hW.integrableOn_Icc
  have hp : IntegrableOn (fun p : ℝ × ℝ => V p.1 * W p.2)
      (Set.Icc a b ×ˢ Set.Icc a b) (volume.prod volume) := by
    rw [IntegrableOn, ← Measure.prod_restrict]
    exact hv.mul_prod hw
  have hcc (f : ℝ → ℝ) {c e : ℝ} (hce : c ≤ e) :
      (∫ t in c..e, f t) = ∫ t in Set.Icc c e, f t := by
    rw [intervalIntegral.integral_of_le hce, integral_Icc_eq_integral_Ioc]
  rw [hcc _ hab, hcc _ hab]
  calc
    _ = ∫ t in Set.Icc a b, ∫ s in Set.Icc a t, V s * W t := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro t ht
      dsimp only
      rw [hcc V ht.1, integral_mul_const]
    _ = ∫ s in Set.Icc a b, ∫ t in Set.Icc s b, V s * W t :=
      setIntegral_time_triangle_swap _ hp
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro s hs
      dsimp only
      rw [hcc W hs.2, integral_const_mul]

end EinsteinRelation.Correctors
