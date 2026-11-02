import EinsteinFull.Calculus.C6CoarseRawVectorRate
import EinsteinFull.Calculus.C3CoarseCenteringContraction
import EinsteinFull.Calculus.C6CoarseGaussianCommutatorIntegrable

open MeasureTheory
open scoped ENNReal

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM

/-- The exact coarse-identification root follows from smooth corrector moments. -/
theorem node_p_u3A_covariance_u23_coarse_u2D_identification_of_deps
    (hmom : node_corrector_u2D_construction_u23_smooth_u2D_momentsStmt) :
    node_p_u3A_covariance_u23_coarse_u2D_identificationStmt := by
  intro d hd D
  obtain ⟨C, hC, hraw⟩ := covarianceCoarse_raw_vector_L2_bound hmom d hd D
  refine ⟨C, hC, ?_⟩
  intro Q hs r hr x
  have hm := fun j k => coarseEntry_signed_aestronglyMeasurable d hd D Q hs r hr x j k
  refine ⟨?_, covarianceCoarse_error_memLp_two hd D Q r hr x hm, ?_⟩
  · intro j k
    exact ⟨coarse_gaussian_commutator_integrable hmom d hd D Q hs r hr x j k,
      (covarianceCoarse_entry_memLp_four hd D Q r hr x j k (hm j k)).mono_exponent
        (by norm_num : (2 : ENNReal) ≤ 4)⟩
  · exact (covarianceCoarse_actual_centering_L2_contraction d hd D Q hs r hr x).trans
      (hraw Q hs r hr x)

end EinsteinFull.Blueprint
