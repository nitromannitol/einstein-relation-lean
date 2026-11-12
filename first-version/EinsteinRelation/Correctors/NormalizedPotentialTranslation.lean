import EinsteinRelation.Correctors.ScalarGaugeReconstruction
import EinsteinRelation.Correctors.MollifierShiftSourceIdentity
import EinsteinRelation.Calculus.WeakGradientTranslation
import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Translation of normalized continuous weak potentials

Source: `paper/main.tex:948–963`. Equality of the translated weak gradients
identifies two continuous potentials up to a constant. Their zero mollifier
means determine that constant and give the literal shifted-mean identity.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- Translation of a continuous normalized potential produces precisely the
shifted mollifier mean in Proposition 5.3. No covariance of the potentials
or uniqueness assumption is needed. Source: `paper/main.tex:948–963`. -/
theorem normalized_weakPotential_translation {d : ℕ} (hd : 0 < d)
    {R : ℝ} (hR : 0 < R) (y : Vec d)
    (u v : Vec d → ℝ) (G : Vec d → Vec d)
    (hu : HasWeakGradient Set.univ u G)
    (hv : HasWeakGradient Set.univ v (fun x => G (y + x)))
    (huc : Continuous u) (hvc : Continuous v)
    (hun : (∫ z, Calculus.unitMassScaledMollifier d R z * u z) = 0)
    (hvn : (∫ z, Calculus.unitMassScaledMollifier d R z * v z) = 0) :
    v (-y) = u 0 + ∫ z, (Calculus.unitMassScaledMollifier d R z -
      Calculus.unitMassScaledMollifier d R (z - y)) * u z := by
  let ζ := Calculus.unitMassScaledMollifier d R
  have hζc : Continuous ζ := (Entropy.contDiff_unitMassScaledMollifier R).continuous
  have hζs : HasCompactSupport ζ := Entropy.hasCompactSupport_unitMassScaledMollifier hR
  have hζi : Integrable ζ volume := hζc.integrable_of_hasCompactSupport hζs
  have huli : LocallyIntegrable u volume := locallyIntegrableOn_univ.mp (hu ⟨0, hd⟩).1
  have huζ : Integrable (fun z => ζ z * u z) volume :=
    huli.integrable_smul_left_of_hasCompactSupport hζc hζs
  have huyζ : Integrable (fun z => ζ (z - y) * u z) volume :=
    huli.integrable_smul_left_of_hasCompactSupport
      (hζc.comp (continuous_id.sub continuous_const))
      (hζs.comp_homeomorph (Homeomorph.subRight y))
  obtain ⟨c, hc⟩ := weakPotentials_differ_by_constant hd hv (hu.comp_add_left y)
  have heq : v = fun x => u (y + x) + c :=
    MeasureTheory.Measure.eq_of_ae_eq hc hvc
      ((huc.comp (continuous_const.add continuous_id)).add continuous_const)
  have hchange : (∫ z, ζ z * u (y + z)) = ∫ z, ζ (z - y) * u z := by
    have ht := integral_add_left_eq_self (μ := (volume : Measure (Vec d)))
      (fun z => ζ (z - y) * u z) y
    simpa only [add_sub_cancel_left] using ht
  have huys : Integrable (fun z => ζ z * u (y + z)) volume := by
    have hli := locallyIntegrableOn_univ.mp ((hu.comp_add_left y) ⟨0, hd⟩).1
    exact hli.integrable_smul_left_of_hasCompactSupport hζc hζs
  have hcval : c = -(∫ z, ζ (z - y) * u z) := by
    have hn : (∫ z, ζ z * (u (y + z) + c)) = 0 := by
      change (∫ z, ζ z * v z) = 0 at hvn
      simpa only [heq] using hvn
    simp_rw [mul_add] at hn
    rw [integral_add huys (hζi.mul_const c), integral_mul_const,
      Entropy.integral_unitMassScaledMollifier' hR, one_mul, hchange] at hn
    linarith only [hn]
  rw [congrFun heq (-y)]
  simp only [add_neg_cancel]
  rw [hcval]
  simp_rw [sub_mul]
  rw [integral_sub huζ huyζ, hun]
  ring

end EinsteinRelation.Correctors
