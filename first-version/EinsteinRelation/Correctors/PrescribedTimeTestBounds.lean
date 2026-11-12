import EinsteinRelation.Correctors.CompactTestPairingContinuity
import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Distributional bounds at prescribed positive times

Source: `paper/main.tex:798–806`. Continuity of the scalar flow extends
uniform a.e. time bounds for compact spatial test pairings to both endpoints.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- A continuous bound holding at almost every interior time holds at
both endpoints as well. Source: `paper/main.tex:798–806`. -/
theorem continuousOn_le_of_ae_Ioo {a b B : ℝ} (hab : a < b)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a b))
    (hb : ∀ᵐ t ∂volume.restrict (Set.Ioo a b), f t ≤ B) :
    ∀ t ∈ Set.Icc a b, f t ≤ B := by
  have he : f =ᵐ[volume.restrict (Set.Icc a b)] fun t => min (f t) B := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact hb.mono fun t ht => (min_eq_left ht).symm
  have heq := Measure.eqOn_Icc_of_ae_eq volume hab.ne he hf
    (fun t ht => (hf t ht).min continuousWithinAt_const)
  intro t ht
  rw [heq ht]
  exact min_le_right _ _

/-- Every distributional coordinate-derivative bound persists at a
prescribed endpoint of a positive time interval.
Source: `paper/main.tex:798–806`. -/
theorem continuous_flow_test_bound_on_closed_interval {d : ℕ} (i : Fin d)
    {u : ℝ × Vec d → ℝ} (hu : ContinuousOn u (Set.Ioi 0 ×ˢ Set.univ))
    {a b B : ℝ} (ha : 0 < a) (hab : a < b)
    {U : Set (Vec d)}
    (hb : ∀ ψ : Vec d → ℝ, IsSpatialTest U ψ →
      ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
        |∫ x in U, u (t,x) * coordinateDerivative i ψ x| ≤
          B * (eLpNorm ψ 2 (volume.restrict U)).toReal) :
    ∀ t ∈ Set.Icc a b, ∀ ψ : Vec d → ℝ, IsSpatialTest U ψ →
      |∫ x in U, u (t,x) * coordinateDerivative i ψ x| ≤
        B * (eLpNorm ψ 2 (volume.restrict U)).toReal := by
  intro t ht ψ hψ
  have hd : Continuous (coordinateDerivative i ψ) :=
    (hψ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdc : HasCompactSupport (coordinateDerivative i ψ) :=
    hψ.2.1.fderiv_apply ℝ (unitVector i)
  have he (s : ℝ) : (∫ x in U, u (s,x) * coordinateDerivative i ψ x) =
      ∫ x, u (s,x) * coordinateDerivative i ψ x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hxs : x ∉ tsupport ψ := fun h => hx (hψ.2.2 h)
    simp only [coordinateDerivative, fderiv_of_notMem_tsupport (𝕜 := ℝ) hxs,
      ContinuousLinearMap.zero_apply, mul_zero]
  have hc := (continuousOn_compact_test_pairing u hu hd hdc).abs.mono
    (show Set.Icc a b ⊆ Set.Ioi 0 from fun _ hs => ha.trans_le hs.1)
  have hbe : ∀ᵐ s ∂volume.restrict (Set.Ioo a b),
      |∫ x, u (s,x) * coordinateDerivative i ψ x| ≤
        B * (eLpNorm ψ 2 (volume.restrict U)).toReal := by
    simpa only [he] using hb ψ hψ
  rw [he]
  exact continuousOn_le_of_ae_Ioo hab hc hbe t ht

end EinsteinRelation.Correctors
