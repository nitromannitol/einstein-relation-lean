import EinsteinFull.Blueprint.Foundation.node_corrector_u2D_construction
import EinsteinFull.Blueprint.Foundation.node_eq_u2E_reduced_u2D_bounds_u23_derivatives
import EinsteinFull.Blueprint.G3.node_corrector_u2D_construction_u23_smooth_u2D_moments
import EinsteinFull.Calculus.C2SmoothMomentsAssembly

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.Correctors

/-- Source: `paper/main.tex:794,880–885`. The actual canonical gradient has
all moments by physical-ball Schauder and source energy moments; Gaussian
averaging retains the actual anisotropic homogenized kernel. -/
@[nolint unusedArguments] -- Retain the exact graph interface; the canonical APIs suffice.
theorem node_corrector_u2D_construction_u23_smooth_u2D_moments_of_deps
    (_hconstruction : node_corrector_u2D_constructionStmt)
    (_hderivatives : node_eq_u2E_reduced_u2D_bounds_u23_derivativesStmt) :
    node_corrector_u2D_construction_u23_smooth_u2D_momentsStmt := by
  intro d hd D p hp
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  let q : ℝ := max p 2
  have hq : 0 < q := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hR : 0 < D.dependenceRange := zero_lt_one.trans_le D.one_le_dependenceRange
  obtain ⟨Cp, hCp, hpoint⟩ := canonicalCorrector_pointwise_positive_moments d hd
    D.ellipticity D.dependenceRange p D.one_le_ellipticity hR hp0
  obtain ⟨Cq, hCq, hpointq⟩ := canonicalCorrector_pointwise_positive_moments d hd
    D.ellipticity D.dependenceRange q D.one_le_ellipticity hR hq
  let M : ℝ := Cq ^ (1 / q)
  have hM : 0 ≤ M := Real.rpow_nonneg hCq.le _
  obtain ⟨Cg, hCg, hgauss⟩ := correctorGaussian_moments_of_pointwise p hp M hM
  refine ⟨max Cp Cg, lt_max_of_lt_left hCp, ?_⟩
  intro Q _hsmooth i z
  have hmp : MemLp (fun ω => correctorGradient Q i ω) (ENNReal.ofReal p) (reducedLaw Q) :=
    (correctorGradient_memLp_iff_finite_moment Q i hp0).mpr
      ((hpoint Q i).trans_lt ENNReal.ofReal_lt_top)
  have hmq : MemLp (fun ω => correctorGradient Q i ω) (ENNReal.ofReal q) (reducedLaw Q) :=
    (correctorGradient_memLp_iff_finite_moment Q i hq).mpr
      ((hpointq Q i).trans_lt ENNReal.ofReal_lt_top)
  have hnorm : eLpNorm (fun ω => correctorGradient Q i ω)
      (ENNReal.ofReal q) (reducedLaw Q) ≤ ENNReal.ofReal M := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (ENNReal.ofReal_ne_zero_iff.mpr hq) ENNReal.ofReal_ne_top hmq.aestronglyMeasurable,
      ENNReal.toReal_ofReal hq.le]
    have heq : (∫⁻ ω, ‖correctorGradient Q i ω‖ₑ ^ q ∂reducedLaw Q) =
        ∫⁻ ω, ENNReal.ofReal (‖correctorGradient Q i ω‖ ^ q) ∂reducedLaw Q := by
      apply lintegral_congr
      intro ω
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq.le]
    rw [heq]
    calc
      _ ≤ (ENNReal.ofReal Cq) ^ (1 / q) := ENNReal.rpow_le_rpow (hpointq Q i) (by positivity)
      _ = _ := ENNReal.ofReal_rpow_of_nonneg hCq.le (by positivity)
  have hmt := hmp.comp_measurePreserving
    (measurePreserving_translate (reducedEnvironmentLaw Q) (reducedEnvironmentLaw_stationary Q) z)
  refine ⟨hmt, ?_, ?_⟩
  · have hi := hmt.integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.mpr hp0)
      ENNReal.ofReal_ne_top
    simp only [ENNReal.toReal_ofReal hp0.le] at hi
    change Integrable (fun ω => ‖correctorGradient Q i (translate z ω)‖ ^ p)
      (reducedLaw Q) at hi
    apply le_trans (b := Cp) _ (le_max_left _ _)
    apply (ENNReal.ofReal_le_ofReal_iff hCp.le).mp
    rw [ofReal_integral_eq_lintegral_ofReal hi
      (ae_of_all _ fun _ => Real.rpow_nonneg (norm_nonneg _) _),
      lintegral_correctorGradient_translate]
    exact hpoint Q i
  · intro r hr
    obtain ⟨hi, hm, hb⟩ := hgauss d hd _ _ Q i hmq hnorm z r (zero_lt_one.trans_le hr)
    exact ⟨hi, hm, hb.trans (le_max_right _ _)⟩

end EinsteinFull.Blueprint
