import EinsteinRelation.Correctors.SemigroupPrescribedGradient
import EinsteinRelation.Correctors.AKMHeatKernelLocalGaussian
import EinsteinRelation.Correctors.ParabolicLocalStripEnergy

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Local scalar kernel energies decay quadratically in the initial point.
Source: AKM E.1 (E.7); `paper/main.tex:787–792,850`. -/
theorem akm_heatKernel_local_scalar_gaussian_energy {d : ℕ} {K : ℝ}
    (hK : 0 < K) {A : Coefficient d K}
    {P : ℝ → Vec d → Vec d → ℝ}
    {X Y : ℝ → Vec d → Vec d → Vec d}
    {H : ℝ → Vec d → Vec d → Mat d} {C : ℝ → ℝ}
    (hP : HeatKernelProperties A P X Y H C)
    {a b R : ℝ} (ha : 0 < a) (hab : a < b) (hR : 0 < R) :
    ∃ D κ : ℝ, 0 ≤ D ∧ 0 < κ ∧ ∀ y : Vec d,
      (∫ z in Set.Ioo a b ×ˢ originBall d R, (P z.1 z.2 y)^2) ≤
        D * Real.exp (-(2*κ) * euclideanSq y) := by
  obtain ⟨D,κ,hD,hκ,hbound⟩ := akm_heatKernel_local_gaussian_envelope hK hP ha hab hR
  let S := Set.Ioo a b ×ˢ originBall d R
  have hcomp := isCompact_closure_originBall d R
  letI : IsFiniteMeasure (volume.restrict (originBall d R)) :=
    isFiniteMeasure_restrict.mpr (ne_top_of_le_ne_top
      (hcomp.measure_ne_top (μ := volume)) (measure_mono subset_closure))
  have hvol : (volume : Measure (ℝ × Vec d)).restrict S =
      (volume.restrict (Set.Ioo a b)).prod (volume.restrict (originBall d R)) := by
    simp only [S,Measure.prod_restrict,← Measure.volume_eq_prod]
  letI : IsFiniteMeasure (volume.restrict S) := by rw [hvol]; infer_instance
  have hSm : MeasurableSet S := by
    apply measurableSet_Ioo.prod
    unfold originBall euclideanNorm euclideanSq dot
    exact measurableSet_lt (by fun_prop) measurable_const
  refine ⟨D^2 * volume.real S,κ,mul_nonneg (sq_nonneg _) measureReal_nonneg,hκ,?_⟩
  intro y
  have hsol := (hP.2.2.1 y).1 a b R ha hab hR
  calc
    _ ≤ ∫ _z in S, D^2 * Real.exp (-(2*κ)*euclideanSq y) := by
      apply integral_mono_ae hsol.1.integrable_sq (integrable_const _)
      filter_upwards [ae_restrict_mem hSm] with z hz
      have hh := pow_le_pow_left₀ (abs_nonneg _) (hbound z.1 hz.1 z.2 hz.2 y) 2
      rw [sq_abs,mul_pow] at hh
      convert hh using 1
      simp_rw [pow_two]
      rw [← Real.exp_add]
      congr 2
      ring
    _ = _ := by simp only [integral_const,measureReal_restrict_apply_univ,smul_eq_mul]; ring

/-- Local gradient kernel energies have an integrable Gaussian envelope
in the initial point. Source: AKM E.1 (E.1), (E.7)–(E.8);
`paper/main.tex:787–792,850`. -/
theorem akm_heatKernel_local_solution_gradient_gaussian_energy {d : ℕ} {K : ℝ}
    (hK : 0 < K) {A : Coefficient d K}
    {P : ℝ → Vec d → Vec d → ℝ}
    {X Y : ℝ → Vec d → Vec d → Vec d}
    {H : ℝ → Vec d → Vec d → Mat d} {C : ℝ → ℝ}
    (hP : HeatKernelProperties A P X Y H C)
    {Z : ℝ → Vec d → Vec d → Vec d}
    (hZsol : ∀ y, IsFundamentalSolution A y
      (fun z => P z.1 z.2 y) (fun z => Z z.1 z.2 y))
    {a b R : ℝ} (ha : 0 < a) (hab : a < b) (hR : 0 < R) :
    ∃ D κ : ℝ, 0 ≤ D ∧ 0 < κ ∧ ∀ y : Vec d,
      (∫ z in Set.Ioo a b ×ˢ originBall d R, euclideanNorm (Z z.1 z.2 y)^2) ≤
        D * Real.exp (-(2*κ) * euclideanSq y) := by
  obtain ⟨E,hE,henergy⟩ := parabolicSolution_local_strip_gradient_energy hK ha hab hR
  obtain ⟨D,κ,hD,hκ,hscalar⟩ := akm_heatKernel_local_scalar_gaussian_energy hK hP
    (half_pos ha) (by linarith : a/2 < b+a/2) (by positivity : 0 < 2*R)
  refine ⟨E*D,κ,mul_nonneg hE hD,hκ,?_⟩
  intro y
  exact (henergy A _ _ ((hZsol y).1 (a/2) (b+a/2) (2*R)
    (half_pos ha) (by linarith) (by positivity))).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hscalar y) hE)

end EinsteinRelation.Correctors
