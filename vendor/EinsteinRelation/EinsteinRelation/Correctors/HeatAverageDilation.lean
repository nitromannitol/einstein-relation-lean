import EinsteinRelation.Correctors.HeatKernelScaling
import EinsteinRelation.External.AKMCorrectorOscillation

/-! Source: `paper/main.tex:716-723`. Physical transport of heat-centering constants. -/
namespace EinsteinRelation.Correctors
open MeasureTheory External.AKM

/-- Heat centering commutes with the physical space and amplitude dilation. -/
theorem scalarHeatAverage_dilation {d : ℕ} (u : Vec d → ℝ)
    (r c s : ℝ) (hr : 0 < r) (hs : 0 < s) (y : Vec d) :
    scalarHeatAverage (fun x => c * u (r⁻¹ • x)) y (r * s) =
      c * scalarHeatAverage u (r⁻¹ • y) s := by
  unfold scalarHeatAverage heatKernel
  simp only

  have hsq : (r * s) ^ 2 = r ^ 2 * s ^ 2 := by ring
  rw [hsq]

  have htemp : (fun (z : Vec d) => euclideanHeatKernel (r ^ 2 * s ^ 2) (z - y) * (c * u (r⁻¹ • z))) =
      (fun (z : Vec d) => c * (euclideanHeatKernel (r ^ 2 * s ^ 2) (z - y) * u (r⁻¹ • z))) := by
    ext z; ring
  rw [htemp]

  rw [integral_const_mul]

  have h_main : (∫ z : Vec d, euclideanHeatKernel (r ^ 2 * s ^ 2) (z - y) * u (r⁻¹ • z)) =
      (∫ z : Vec d, euclideanHeatKernel (s ^ 2) (z - (r⁻¹ • y)) * u z) := by

    set f := fun (z : Vec d) => euclideanHeatKernel (r ^ 2 * s ^ 2) (r • z - y) * u z with hf
    have h_f_inv : ∀ z, f (r⁻¹ • z) = euclideanHeatKernel (r ^ 2 * s ^ 2) (z - y) * u (r⁻¹ • z) := by
      intro z
      dsimp [f]
      have h : r • (r⁻¹ • z) = z := by
        rw [smul_smul]
        field_simp [hr.ne']
        simp
      rw [h]
    have hchange := Measure.integral_comp_inv_smul_of_nonneg (μ := volume) f hr.le

    have h_finrank : Module.finrank ℝ (Vec d) = d := by
      simp
    rw [h_finrank] at hchange

    have hLHS : (∫ z : Vec d, f (r⁻¹ • z)) = (∫ z : Vec d, euclideanHeatKernel (r ^ 2 * s ^ 2) (z - y) * u (r⁻¹ • z)) := by
      rw [integral_congr_ae (ae_of_all _ h_f_inv)]
    rw [hLHS] at hchange

    rw [hchange]

    have hfz : ∀ z, f z = (r ^ d)⁻¹ * (euclideanHeatKernel (s ^ 2) (z - (r⁻¹ • y)) * u z) := by
      intro z
      dsimp [f]
      have hs_sq_pos : 0 < s ^ 2 := pow_pos hs 2
      have hscale := euclideanHeatKernel_scale hr hs_sq_pos (z - (r⁻¹ • y))
      have hsub : r • z - y = r • (z - (r⁻¹ • y)) := by
        rw [smul_sub, smul_smul]
        field_simp [hr.ne']
        simp
      calc
        euclideanHeatKernel (r ^ 2 * s ^ 2) (r • z - y) * u z
            = euclideanHeatKernel (r ^ 2 * s ^ 2) (r • (z - (r⁻¹ • y))) * u z := by rw [hsub]
        _ = ((r ^ d)⁻¹ * euclideanHeatKernel (s ^ 2) (z - (r⁻¹ • y))) * u z := by rw [hscale]
        _ = (r ^ d)⁻¹ * (euclideanHeatKernel (s ^ 2) (z - (r⁻¹ • y)) * u z) := by ring
    rw [integral_congr_ae (ae_of_all _ hfz)]

    rw [integral_const_mul]

    simp_rw [smul_eq_mul]

    have hpow : r ^ d ≠ 0 := pow_ne_zero d hr.ne'
    field_simp [hpow]
  rw [h_main]
/-- The physical tensor heat center has the same range dilation and
amplitude, entry by entry. -/
theorem fluxHeatAverage_dilation {d : ℕ} (S : Vec d → Mat d)
    (r c s : ℝ) (hr : 0 < r) (hs : 0 < s) (y : Vec d) :
    fluxHeatAverage (fun x => c • S (r⁻¹ • x)) y (r * s) =
      c • fluxHeatAverage S (r⁻¹ • y) s := by
  ext j k
  exact scalarHeatAverage_dilation (fun x => S x j k) r c s hr hs y

end EinsteinRelation.Correctors
