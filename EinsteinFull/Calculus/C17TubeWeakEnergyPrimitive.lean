import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

open MeasureTheory Filter Set
open scoped Topology

namespace EinsteinFull.Calculus

/-- An integrable function on an open bounded interval has a continuous global
primitive that agrees with its interval integral and has the prescribed
derivative almost everywhere on the interval. -/
theorem c17_integrableOn_continuous_primitive {a b : ℝ}
    (g : ℝ → ℝ) (hg : IntegrableOn g (Ioo a b)) :
    ∃ P : ℝ → ℝ, Continuous P ∧
      (∀ t ∈ Ioo a b, P t = ∫ s in a..t, g s) ∧
      ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt P (g t) t := by
  let G := (Ioo a b).indicator g
  have hG : Integrable G volume := hg.integrable_indicator measurableSet_Ioo
  let P : ℝ → ℝ := fun t => ∫ s in a..t, G s
  refine ⟨P, intervalIntegral.continuous_primitive (fun _ _ => hG.intervalIntegrable) a, ?_, ?_⟩
  · intro t ht
    apply intervalIntegral.integral_congr_Ioo_of_le ht.1.le
    intro s hs
    exact indicator_of_mem (show s ∈ Ioo a b from ⟨hs.1, lt_trans hs.2 ht.2⟩) g
  · have hd := LocallyIntegrable.ae_hasDerivAt_integral hG.locallyIntegrable
    filter_upwards [ae_restrict_of_ae hd, ae_restrict_mem measurableSet_Ioo] with t ht hmem
    simpa only [P, G, indicator_of_mem hmem] using ht a

/-- Integration by parts for the primitive of integrable data and a smooth
function vanishing at both endpoints. -/
theorem c17_primitive_interval_integration_by_parts {a b : ℝ}
    (g ψ : ℝ → ℝ) (hg : Integrable g volume)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (ha : ψ a = 0) (hb : ψ b = 0) :
    (∫ t in a..b, (∫ s in a..t, g s) * deriv ψ t) =
      -(∫ t in a..b, g t * ψ t) := by
  let P : ℝ → ℝ := fun t => ∫ s in a..t, g s
  have hP : AbsolutelyContinuousOnInterval P a b :=
    hg.intervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hψac : AbsolutelyContinuousOnInterval ψ a b :=
    (hψ.of_le (by simp)).contDiffOn.absolutelyContinuousOnInterval
  have hp := hP.integral_mul_deriv_eq_deriv_mul hψac
  have hd : ∀ᵐ t, deriv P t = g t := by
    filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hg.locallyIntegrable] with t ht
    exact (ht a).deriv
  have heq : (∫ t in a..b, deriv P t * ψ t) = ∫ t in a..b, g t * ψ t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hd] with t ht _
    rw [ht]
  simpa only [ha, hb, mul_zero, sub_self, zero_sub, heq, P] using hp

/-- The interval primitive satisfies the weak integration-by-parts identity
against tests supported in the open interval. -/
theorem c17_primitive_compact_test_integration_by_parts {a b : ℝ} (hab : a < b)
    (g ψ : ℝ → ℝ) (hg : IntegrableOn g (Ioo a b))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hsp : tsupport ψ ⊆ Ioo a b) :
    (∫ t in Ioo a b, (∫ s in a..t, g s) * deriv ψ t) =
      -(∫ t in Ioo a b, g t * ψ t) := by
  let G := (Ioo a b).indicator g
  have hG : Integrable G volume := hg.integrable_indicator measurableSet_Ioo
  have ha : ψ a = 0 := image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl a) (hsp h).1)
  have hb : ψ b = 0 := image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl b) (hsp h).2)
  have hleft : (∫ t in a..b, (∫ s in a..t, G s) * deriv ψ t) =
      ∫ t in Ioo a b, (∫ s in a..t, g s) * deriv ψ t := by
    rw [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    dsimp only
    congr 1
    apply intervalIntegral.integral_congr_Ioo_of_le ht.1.le
    intro s hs
    exact indicator_of_mem (show s ∈ Ioo a b from ⟨hs.1, lt_trans hs.2 ht.2⟩) g
  have hright : (∫ t in a..b, G t * ψ t) = ∫ t in Ioo a b, g t * ψ t := by
    rw [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    dsimp only
    rw [show G t = g t from indicator_of_mem ht g]
  rw [← hleft, ← hright]
  exact c17_primitive_interval_integration_by_parts G ψ hG hψ ha hb

end EinsteinFull.Calculus
