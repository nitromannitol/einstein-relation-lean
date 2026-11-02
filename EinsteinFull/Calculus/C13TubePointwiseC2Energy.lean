import EinsteinFull.Calculus.C13TubeNativeC2Energy
import Mathlib.MeasureTheory.Measure.OpenPos

open EinsteinRelation PDE MeasureTheory Filter EinsteinFull.External.Source.GMP
open scoped Topology

namespace EinsteinFull.Calculus

/-- Joint continuity on the cylinder makes the actual weighted cutoff mass continuous. -/
@[nolint unusedArguments]
theorem c13_actual_C2_cutoff_mass_continuous {d : ℕ} {κ R a b : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (ρ : EinsteinRelation.Vec d → ℝ) (α : EinsteinRelation.Vec d → EinsteinRelation.Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × EinsteinRelation.Vec d → ℝ)
    (hu : ContinuousOn u (Set.Ioo a b ×ˢ sourceBall 0 R))
    (F : ℝ → ℝ) (hF : Continuous F)
    (χ : EinsteinRelation.Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ sourceBall 0 R) :
    ContinuousOn (fun t => ∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * F (u (t,x)))
      (Set.Ioo a b) := by
  let U : Set (EinsteinRelation.Vec d) := sourceBall 0 R
  let H : ℝ → EinsteinRelation.Vec d → ℝ := fun t x => χ x ^ 2 * F (u (t,x))
  have hU : IsOpen U := by
    have hc : Continuous (fun x : EinsteinRelation.Vec d => euclideanNorm x) := by
      unfold euclideanNorm euclideanSq dot
      exact Real.continuous_sqrt.comp (continuous_finsetSum _
        (fun j _ => (continuous_apply j).mul (continuous_apply j)))
    unfold U sourceBall
    exact isOpen_lt (hc.comp (continuous_id.sub continuous_const)) continuous_const
  have hH : ContinuousOn H.uncurry (Set.Ioo a b ×ˢ Set.univ) := by
    intro z hz
    by_cases hx : z.2 ∈ U
    · have hzU : z ∈ Set.Ioo a b ×ˢ U := ⟨hz.1, hx⟩
      have hzu : ContinuousAt u z := hu.continuousAt ((isOpen_Ioo.prod hU).mem_nhds hzU)
      exact (((hχ.continuous.comp continuous_snd).pow 2).continuousAt.mul (hF.continuousAt.comp hzu)).continuousWithinAt
    · have hxK : z.2 ∉ tsupport χ := fun hxK => hx (hχU hxK)
      have hn : ∀ᶠ w : ℝ × EinsteinRelation.Vec d in 𝓝 z, w.2 ∉ tsupport χ :=
        continuous_snd.continuousAt (((isClosed_tsupport χ).isOpen_compl).mem_nhds hxK)
      apply (continuousWithinAt_const : ContinuousWithinAt (fun _ : ℝ × EinsteinRelation.Vec d => (0 : ℝ)) _ z).congr_of_eventuallyEq_of_mem ?_ hz
      filter_upwards [hn.filter_mono nhdsWithin_le_nhds] with w hw
      change χ w.2 ^ 2 * F (u w) = 0
      rw [image_eq_zero_of_notMem_tsupport hw]
      simp
  have hzero : ∀ t x, t ∈ Set.Ioo a b → x ∉ tsupport χ → H t x = 0 := by
    intro t x ht hx
    simp [H, image_eq_zero_of_notMem_tsupport hx]
  have hρ : IntegrableOn ρ (tsupport χ) (volume : Measure (EinsteinRelation.Vec d)) := by
    apply IntegrableOn.of_bound hχc.measure_lt_top hell.1.aestronglyMeasurable κ⁻¹
    exact ae_of_all _ (fun x => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hκ.le.trans (hell.2.2 x).1)] using
        (hell.2.2 x).2.1)
  have hc := continuousOn_integral_bilinear_of_locally_integrable_of_compact_support
    (ContinuousLinearMap.lsmul ℝ ℝ) hχc hH hzero (hρ.restrict (t := U))
  simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, H, mul_assoc, U] using hc

/-- The literal C² cutoff mass satisfies the energy balance at every interior time. -/
theorem c13_actual_weighted_C2_energy_every_time {d : ℕ}
    {κ R a b : ℝ} (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (ρ : EinsteinRelation.Vec d → ℝ) (α : EinsteinRelation.Vec d → EinsteinRelation.Mat d)
    (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × EinsteinRelation.Vec d → ℝ) (G : ℝ × EinsteinRelation.Vec d → EinsteinRelation.Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ContinuousOn u (Set.Ioo a b ×ˢ sourceBall 0 R))
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hF0 : F 0 = 0)
    (M : ℝ) (hM : 0 ≤ M) (hder : ∀ r, |deriv (deriv F) r| ≤ M)
    (χ : EinsteinRelation.Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ sourceBall 0 R) :
    ∀ s ∈ Set.Ioo a b, ∀ t ∈ Set.Ioo a b,
      (∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * F (u (t,x))) -
      (∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * F (u (s,x))) =
      -(∫ r in s..t, ∫ x in sourceBall 0 R,
        χ x ^ 2 * deriv (deriv F) (u (r,x)) *
          dot ((α x).mulVec (G (r,x))) (G (r,x)) +
        2 * χ x * deriv F (u (r,x)) * dot ((α x).mulVec (G (r,x)))
          (fun j => fderiv ℝ χ x (unitVector j))) := by
  obtain ⟨E, hE, hae, hbalance⟩ :=
    c13_actual_weighted_C2_continuous_energy hκ hR hab ρ α hell u G hcal
      F hF hF0 M hM hder χ hχ hχc hχU
  have hm := c13_actual_C2_cutoff_mass_continuous hκ hR hab ρ α hell u hu
    F hF.continuous χ hχ hχc hχU
  have heq := MeasureTheory.Measure.eqOn_Ioo_of_ae_eq volume hae hE hm
  intro s hs t ht
  simpa only [heq ht, heq hs] using hbalance s hs t ht

end EinsteinFull.Calculus
