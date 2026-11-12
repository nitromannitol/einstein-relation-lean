import EinsteinRelation.Correctors.ParabolicPrescribedGradient
import EinsteinRelation.Correctors.LocalWeakGradientUniqueness
import EinsteinRelation.Correctors.SpatialWeakLocalization
import EinsteinRelation.Correctors.SemigroupPrescribedGradient

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport
/-- Extend the actual good-radius comparison to a prescribed whole-space
weak gradient of the same scalar flow. Source: `paper/main.tex:798–806`. -/
theorem semigroupSolution_good_radius_prescribed_unit_le
    {d : ℕ} {K : ℝ} {A : Coefficient d K} {g : Vec d → Vec d}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsSemigroupSolution A g u G) {r X L : ℝ}
    (hr : 1 ≤ r) (hX : 1 ≤ X) (hL : 0 ≤ L) (hgood : 4*X ≤ r)
    (hcomp : ∀ᵐ τ ∂volume.restrict (Set.Ioo (-((2*X)^2)/4) 0),
      vectorRms volume (originBall d 1) (fun x => G (τ+3*r^2,x)) ≤
        L * X^((d : ℝ)/2) * vectorRms volume
          (Set.Ioo (2*r^2) (3*r^2) ×ˢ originBall d r) G)
    {H : Vec d → Vec d}
    (hH : HasWeakGradient Set.univ (fun x => u (3*r^2,x)) H) :
    MemLp (fun x => euclideanNorm (H x)) 2 (volume.restrict (originBall d 1)) ∧
    vectorRms volume (originBall d 1) H ≤
      Real.sqrt d * L * X^((d : ℝ)/2) * vectorRms volume
        (Set.Ioo (2*r^2) (3*r^2) ×ˢ originBall d r) G := by
  let U := originBall d 1
  have hopen : IsOpen U := by
    unfold U originBall euclideanNorm euclideanSq dot
    exact isOpen_lt (by fun_prop) continuous_const
  have hcompact := isCompact_closure_originBall d 1
  letI : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr
    (ne_top_of_le_ne_top (hcompact.measure_ne_top (μ := volume)) (measure_mono subset_closure))
  let a := 3*r^2-X^2
  let b := 3*r^2
  let B := L*X^((d : ℝ)/2)*vectorRms volume
    (Set.Ioo (2*r^2) (3*r^2) ×ˢ originBall d r) G
  have ha : 0 < a := by dsimp only [a]; nlinarith only [hgood,hX,hr]
  have hab : a < b := by dsimp only [a,b]; nlinarith only [hX]
  have hlocal := hsol.2.1 a b 1 ha hab zero_lt_one
  have hb : ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
      vectorRms volume U (fun x => G (t,x)) ≤ B := by
    have ht := (ae_restrict_Ioo_add_right_iff
      (a := -((2*X)^2)/4) (b := 0) (c := b)
      (p := fun t => vectorRms volume U (fun x => G (t,x)) ≤ B)).mp hcomp
    have hl : -((2*X)^2)/4+b = a := by dsimp only [a,b]; ring
    simpa only [hl,zero_add] using ht
  have hus : ∀ t ∈ Set.Icc a b, MemLp (fun x => u (t,x)) 2 (volume.restrict U) :=
    fun t ht => semigroupSolution_scalar_memLp_on_precompact hsol hcompact (ha.trans_le ht.1)
  obtain ⟨J,hJ,hJL,hJb⟩ := continuous_flow_exists_weakGradient_of_ae_rms_bound
    hsol.1 ha hab (show 0 ≤ B from mul_nonneg
      (mul_nonneg hL (Real.rpow_nonneg (zero_le_one.trans hX) _)) (Real.sqrt_nonneg _))
    hus hlocal.2.2.2.1 (parabolicSolution_gradient_slice_memLp hlocal) hb b ⟨hab.le,le_rfl⟩
  have heq : J =ᵐ[volume.restrict U] H := by
    filter_upwards [ae_all_iff.mpr fun j => weakPartialDerivative_ae_eq_on_open hopen
      (hJ j) (hasWeakGradient_mono (Set.subset_univ U) hH j)] with x hx
    exact funext hx
  have heqn := heq.mono fun x hx => congrArg euclideanNorm hx
  have hHL := (memLp_congr_ae heqn).mp hJL
  rw [eLpNorm_congr_ae heqn,
    eLpNorm_euclideanNorm_toReal_eq_volume_mul_rms volume U H hHL] at hJb
  have hV : 0 < Real.sqrt ((volume U).toReal) := by
    apply Real.sqrt_pos.mpr
    simpa only [U,originBall_eq_gt_ball,Measure.real] using
      paired_ball_volume_pos_finite (d := d) zero_lt_one
  refine ⟨hHL,?_⟩
  apply (mul_le_mul_iff_right₀ hV).mp
  convert hJb using 1
  dsimp only [B,U]
  ring

end EinsteinRelation.Correctors
