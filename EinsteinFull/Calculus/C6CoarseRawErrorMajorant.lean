import EinsteinFull.Calculus.C6CoarseAffineResidualBound
import EinsteinFull.Calculus.C6CoarsePhysicalGaussianFlux
import EinsteinFull.Calculus.C4CoarsePhysicalErrorCoordinate
import EinsteinFull.Calculus.C6CoarseGaussianCommutatorIntegrable
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM
open EinsteinRelation.Correctors EinsteinRelation.ReductionImageV3
open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinFull.External.Source.AKM
/-- A single L² majorant bounds every literal physical coarse-error entry,
with a structural constant chosen before the environment law. -/
theorem covarianceCoarse_raw_error_L2_majorant :
    ∀ (hmom : node_corrector_u2D_construction_u23_smooth_u2D_momentsStmt)
      (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ C : ℝ, 0 < C ∧
    ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      HasSmoothBounds D Q → ∀ r : ℝ, D.dependenceRange ≤ r → ∀ x : Vec d,
      ∃ W : FieldPair d → ℝ,
        MemLp W 2 (reducedLaw Q) ∧
        eLpNorm W 2 (reducedLaw Q) ≤ ENNReal.ofReal (C * r ^ (-(d : ℝ))) ∧
        ∀ᵐ ω ∂reducedLaw Q, ∀ j k : Fin d,
          |(∫ z : Vec d, heatKernel 0 r z *
              commutatorObservation Q j k (translate (x-z) ω)) -
            covarianceCoarseEntry D Q r x j k ω| ≤ W ω := by
  classical
  intro hmom d hd D
  obtain ⟨C₀, hC₀, hC⟩ := coarse_actual_affine_residual_L2_bound hmom d hd D
  let κ := ellipticityScale D.ellipticity
  let ρ := D.dependenceRange
  have hκ : 0 < κ := ellipticityScale_pos D.one_le_ellipticity
  have hρ : 0 < ρ := lt_of_lt_of_le zero_lt_one D.one_le_dependenceRange
  refine ⟨(d : ℝ) * κ⁻¹ * C₀ * ρ ^ (d : ℝ), by
    have hd0 : 0 < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
    positivity, ?_⟩
  intro Q hs r hr x
  have hr0 : 0 < r := lt_of_lt_of_le hρ hr
  have hscl : 1 ≤ r / ρ := (le_div_iff₀ hρ).2 (by simpa using hr)
  have hscl0 : 0 < r / ρ := div_pos hr0 hρ
  choose φ hid hφ using hC Q hs
  choose V hVm hVn hVa using fun i => hφ i (ρ⁻¹ • x) (r / ρ) hscl
  let P := fun ω : PhysicalField d D.ellipticity =>
    κ⁻¹ * ∑ i : Fin d, |V i (project (r₀ := ρ) Q.ellipticity_parameter ω)|
  let W := fun ω : FieldPair d =>
    if h : ω ∈ physicalReducedRange D.ellipticity then P (inverseReducePhysical ⟨ω, h⟩)
    else 0
  let T := fun ω : PhysicalField d D.ellipticity => reduce ω.1
  have hemb : MeasurableEmbedding T :=
    (Probability.measurableEmbedding_reduce d).comp
      (MeasurableEmbedding.subtype_coe
        (Sharpness.measurableSet_isRegular_fieldPair D.ellipticity))
  have hT : MeasurePreserving T (physicalReferenceLaw Q) (reducedLaw Q) :=
    measurePreserving_physicalReduction Q
  have hWT : W ∘ T = P := by
    funext ω
    have hω : reduce ω.1 ∈ physicalReducedRange D.ellipticity := ⟨ω.1, ω.2, rfl⟩
    have hInv : inverseReducePhysical ⟨reduce ω.1, hω⟩ = ω :=
      inverseReduce_reducePhysical ω
    simp only [W, T, Function.comp_apply, dite_eq_left hω, hInv]
  have hVP (i : Fin d) : MemLp
      (fun ω : PhysicalField d D.ellipticity =>
        |V i (project (r₀ := ρ) Q.ellipticity_parameter ω)|) 2 (physicalReferenceLaw Q) :=
    ((hVm i).comp_measurePreserving (measurePreserving_akmProject Q)).abs
  have hPm : MemLp P 2 (physicalReferenceLaw Q) :=
    (memLp_finsetSum _ (fun i _ => hVP i)).const_mul κ⁻¹
  have hWm : MemLp W 2 (reducedLaw Q) := by
    rw [← hT.map_eq]
    apply hemb.memLp_map_measure_iff.mpr
    rw [hWT]
    exact hPm
  refine ⟨W, hWm, ?_, ?_⟩
  · have hVnorm (i : Fin d) : eLpNorm
        (fun ω : PhysicalField d D.ellipticity =>
          |V i (project (r₀ := ρ) Q.ellipticity_parameter ω)|) 2 (physicalReferenceLaw Q) ≤
        ENNReal.ofReal (C₀ * (r / ρ) ^ (-(d : ℝ))) := by
      change eLpNorm (fun ω : PhysicalField d D.ellipticity =>
        ‖V i (project (r₀ := ρ) Q.ellipticity_parameter ω)‖) 2 _ ≤ _
      have hn := eLpNorm_norm (V i ∘ project (r₀ := ρ) Q.ellipticity_parameter)
        ((hVm i).comp_measurePreserving
          (measurePreserving_akmProject Q)).aestronglyMeasurable (p := (2 : ℝ≥0∞))
      change eLpNorm (fun ω => ‖V i (project (r₀ := ρ) Q.ellipticity_parameter ω)‖)
        2 (physicalReferenceLaw Q) = _ at hn
      rw [hn]
      exact (eLpNorm_comp_measurePreserving (hVm i).aestronglyMeasurable
        (measurePreserving_akmProject Q)).trans_le (hVn i)
    have hsum : eLpNorm
        (fun ω : PhysicalField d D.ellipticity =>
          ∑ i : Fin d, |V i (project (r₀ := ρ) Q.ellipticity_parameter ω)|)
        2 (physicalReferenceLaw Q) ≤
        ENNReal.ofReal ((d : ℝ) * (C₀ * (r / ρ) ^ (-(d : ℝ)))) := by
      calc
        _ ≤ ∑ i : Fin d, eLpNorm
            (fun ω : PhysicalField d D.ellipticity =>
              |V i (project (r₀ := ρ) Q.ellipticity_parameter ω)|) 2
            (physicalReferenceLaw Q) := by
          have heq : (fun ω : PhysicalField d D.ellipticity =>
              ∑ i : Fin d, |V i (project (r₀ := ρ) Q.ellipticity_parameter ω)|) =
              ∑ i : Fin d, (fun ω => |V i (project (r₀ := ρ) Q.ellipticity_parameter ω)|) := by
            funext ω
            simp only [Finset.sum_apply]
          rw [heq]
          exact (eLpNorm_sum_le (p := (2 : ℝ≥0∞)) (by norm_num)
              (f := fun i : Fin d => fun ω : PhysicalField d D.ellipticity =>
                |V i (project (r₀ := ρ) Q.ellipticity_parameter ω)|)
              (s := Finset.univ) (μ := physicalReferenceLaw Q))
        _ ≤ ∑ _i : Fin d, ENNReal.ofReal (C₀ * (r / ρ) ^ (-(d : ℝ))) :=
          Finset.sum_le_sum (fun i _ => hVnorm i)
        _ = _ := by simp [ENNReal.ofReal_mul, Nat.cast_nonneg]
    calc
      _ = eLpNorm P 2 (physicalReferenceLaw Q) := by
        rw [← hT.map_eq, hemb.eLpNorm_map_measure, hWT]
      _ = ENNReal.ofReal κ⁻¹ * eLpNorm
          (fun ω : PhysicalField d D.ellipticity =>
            ∑ i : Fin d, |V i (project (r₀ := ρ) Q.ellipticity_parameter ω)|)
          2 (physicalReferenceLaw Q) := by
        have he := (eLpNorm_const_smul κ⁻¹
            (fun ω : PhysicalField d D.ellipticity =>
              ∑ i : Fin d, |V i (project (r₀ := ρ) Q.ellipticity_parameter ω)|)
            2 (physicalReferenceLaw Q))
        change eLpNorm (fun ω : PhysicalField d D.ellipticity =>
          κ⁻¹ * ∑ i : Fin d, |V i (project (r₀ := ρ) Q.ellipticity_parameter ω)|)
          2 (physicalReferenceLaw Q) = _ at he
        simpa only [Real.enorm_eq_ofReal_abs, abs_of_pos (inv_pos.mpr hκ)] using he
      _ ≤ ENNReal.ofReal κ⁻¹ *
          ENNReal.ofReal ((d : ℝ) * (C₀ * (r / ρ) ^ (-(d : ℝ)))) :=
        mul_le_mul' le_rfl hsum
      _ = _ := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hκ.le)]
        congr 1
        rw [Real.div_rpow hr0.le hρ.le, Real.rpow_neg hρ.le, div_inv_eq_mul]
        ring
  · rw [← hT.map_eq, hemb.ae_map_iff]
    have hres (i : Fin d) :=
      (measurePreserving_akmProject Q).quasiMeasurePreserving.ae (hVa i)
    have hflux (i : Fin d) := coarseCorrector_physical_gaussian_flux_identity
      D Q i (φ i) (hid i) (ρ⁻¹ • x) (r / ρ) hscl0
    have hint (i : Fin d) : ∀ᵐ ω ∂physicalReferenceLaw Q,
        Integrable (fun y : Vec d => heatKernel 0 r y •
          (fun j => commutatorObservation Q j i (translate (x-y) (reduce ω.1)))) := by
      have hi : ∀ᵐ ω ∂reducedLaw Q, ∀ j : Fin d,
          Integrable (fun y : Vec d => heatKernel 0 r y *
            commutatorObservation Q j i (translate (x-y) ω)) :=
        (ae_all_iff).2 (fun j => coarse_gaussian_commutator_integrable hmom d hd D Q hs r hr x j i)
      filter_upwards [(measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae hi]
        with ω hω
      exact (integrable_pi_iff).2 hω
    filter_upwards [ae_all_iff.mpr hres, ae_all_iff.mpr hflux, ae_all_iff.mpr hint]
      with ω hω hf hi
    intro j i
    let a := project (r₀ := ρ) Q.ellipticity_parameter ω
    let A := κ • homogenizedCoefficient Q
    let B := coarsenedCoefficient a A (ρ⁻¹ • x) (r / ρ)
    let U := ∫ y, heatKernel (ρ⁻¹ • x) (r / ρ) y • (unitVector i + (φ i).grad a y)
    let F := ∫ y, heatKernel (ρ⁻¹ • x) (r / ρ) y •
      (a y).mulVec (unitVector i + (φ i).grad a y)
    have hcoord := coarse_physical_error_coordinate_identity D Q ω i j x r U F (hi i)
    have hflux' : F - A.mulVec U = κ • ∫ y, heatKernel 0 r y •
        (fun k => commutatorObservation Q k i (translate (x-y) (reduce ω.1))) := by
      have hfx := hf i
      have hx : ρ • (ρ⁻¹ • x) = x := by rw [smul_smul, mul_inv_cancel₀ hρ.ne', one_smul]
      have hrr : ρ * (r / ρ) = r := by field_simp
      rw [hx, hrr] at hfx
      refine hfx.trans (congrArg (fun v : Vec d => κ • v) ?_)
      calc
        _ = ∫ y, heatKernel x r (x-y) •
            (fun k => commutatorObservation Q k i (translate (x-y) (reduce ω.1))) :=
          (integral_sub_left_eq_self (fun y => heatKernel x r y •
            (fun k => commutatorObservation Q k i (translate y (reduce ω.1)))) volume x).symm
        _ = _ := by
          apply integral_congr_ae
          exact ae_of_all _ fun y => by
            have hk : heatKernel x r (x-y) = heatKernel 0 r y := by
              unfold heatKernel
              rw [show x-y-x = -y by abel, sub_zero, euclideanHeatKernel_neg]
            change heatKernel x r (x-y) •
              (fun k => commutatorObservation Q k i (translate (x-y) (reduce ω.1))) = _
            rw [hk]
    have he := hcoord hflux'
    change |(∫ z, heatKernel 0 r z *
      commutatorObservation Q j i (translate (x-z) (reduce ω.1))) -
      covarianceCoarseEntry D Q r x j i (reduce ω.1)| ≤ W (T ω)
    rw [he]
    have hWP : W (T ω) = P ω := congrFun hWT ω
    rw [hWP]
    change |κ⁻¹ * (F - A.mulVec U - B.mulVec (unitVector i)) j| ≤ _
    rw [abs_mul, abs_of_pos (inv_pos.mpr hκ)]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hκ.le)
    calc
      _ ≤ euclideanNorm (F - A.mulVec U - B.mulVec (unitVector i)) := by
        let v := F - A.mulVec U - B.mulVec (unitVector i)
        have hv : v j * v j ≤ ∑ k, v k * v k :=
          Finset.single_le_sum (f := fun k => v k * v k)
            (fun k _ => mul_self_nonneg (v k)) (Finset.mem_univ j)
        change |v j| ≤ euclideanNorm v
        unfold euclideanNorm euclideanSq dot
        apply Real.abs_le_sqrt
        simpa only [sq] using hv
      _ ≤ V i a := hω i
      _ ≤ |V i a| := le_abs_self _
      _ ≤ ∑ k : Fin d, |V k a| := Finset.single_le_sum (f := fun k => |V k a|)
        (fun k _ => abs_nonneg _) (Finset.mem_univ i)
end EinsteinFull.Blueprint
