import EinsteinRelation.Correctors.TimeEnergyCauchy
import EinsteinRelation.TimeChange.EuclideanTransport
import Mathlib.MeasureTheory.Integral.Prod

/-! Spatially integrated time Cauchy–Schwarz, `paper/main.tex:844–849`. -/

open MeasureTheory Set
namespace EinsteinRelation.Correctors

/-- Integrating time Cauchy–Schwarz in space retains the literal Bochner
integral and the total space-time dissipation; `paper/main.tex:844–849`. -/
theorem integral_norm_time_integral_sq_le_energy
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace X] (ν : Measure X) [SigmaFinite ν]
    {T : ℝ} (hT : 0 ≤ T) {g : ℝ × X → E}
    (hg : MemLp g 2 ((volume.restrict (Icc 0 T)).prod ν)) :
    (∫ x, ‖∫ t in Icc (0 : ℝ) T, g (t,x)‖^2 ∂ν) ≤
      T * ∫ t in Icc (0 : ℝ) T, ∫ x, ‖g (t,x)‖^2 ∂ν := by
  let μ := volume.restrict (Icc (0 : ℝ) T)
  have hsq : Integrable (fun z => ‖g z‖^2) (μ.prod ν) :=
    (memLp_two_iff_integrable_sq hg.norm.aestronglyMeasurable).mp hg.norm
  have hslice : ∀ᵐ x ∂ν, MemLp (fun t => g (t,x)) 2 μ := by
    filter_upwards [hg.aestronglyMeasurable.prodMk_right, hsq.prod_left_ae] with x hx hs
    exact (memLp_two_iff_integrable_sq_norm hx).mpr hs
  have hbound : ∀ᵐ x ∂ν,
      ‖∫ t in Icc (0 : ℝ) T, g (t,x)‖^2 ≤ T * ∫ t in Icc (0 : ℝ) T, ‖g (t,x)‖^2 := by
    filter_upwards [hslice] with x hx
    exact norm_time_integral_sq_le_energy hT _ hx
  have hi : Integrable (fun x => ∫ t, ‖g (t,x)‖^2 ∂μ) ν := hsq.integral_prod_right
  have hl : AEStronglyMeasurable (fun x => ‖∫ t, g (t,x) ∂μ‖^2) ν :=
    hg.aestronglyMeasurable.prod_swap.integral_prod_right'.norm.pow 2
  have hli : Integrable (fun x => ‖∫ t, g (t,x) ∂μ‖^2) ν :=
    (hi.const_mul T).mono' hl (by
      filter_upwards [hbound] with x hx
      simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hx)
  calc
    _ ≤ ∫ x, T * ∫ t, ‖g (t,x)‖^2 ∂μ ∂ν := integral_mono_ae hli (hi.const_mul T) hbound
    _ = T * ∫ x, ∫ t, ‖g (t,x)‖^2 ∂μ ∂ν := integral_const_mul _ _
    _ = _ := congrArg (fun z => T*z) (integral_integral_swap hsq).symm

/-- Time Cauchy–Schwarz in the manuscript's Euclidean norm, with the
same space-time vector field on both sides; `paper/main.tex:844–849`. -/
theorem integral_euclideanSq_time_integral_le {d : ℕ} {X : Type*}
    [MeasurableSpace X] (ν : Measure X) [SigmaFinite ν]
    {T : ℝ} (hT : 0 ≤ T) {G : ℝ × X → Vec d}
    (hG : MemLp G 2 ((volume.restrict (Icc 0 T)).prod ν)) :
    (∫ x, euclideanSq (∫ t in Icc (0 : ℝ) T, G (t,x)) ∂ν) ≤
      T * ∫ t in Icc (0 : ℝ) T, ∫ x, euclideanSq (G (t,x)) ∂ν := by
  let L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  have hsq (v : Vec d) : euclideanSq v = ‖L v‖^2 := by
    change euclideanSq v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖^2
    rw [← TimeChange.euclideanNorm_eq_norm_toLp]
    exact (Real.sq_sqrt (show 0 ≤ euclideanSq v by
      unfold euclideanSq dot
      exact Finset.sum_nonneg (fun _ _ => mul_self_nonneg _))).symm
  have hi (x : X) : L (∫ t in Icc (0 : ℝ) T, G (t,x)) =
      ∫ t in Icc (0 : ℝ) T, L (G (t,x)) := (L.integral_comp_comm _).symm
  simp_rw [hsq, hi]
  exact integral_norm_time_integral_sq_le_energy ν hT
    (hG.continuousLinearMap_comp L.toContinuousLinearMap)

end EinsteinRelation.Correctors
