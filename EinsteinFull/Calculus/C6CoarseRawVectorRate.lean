import EinsteinFull.Calculus.C6CoarseRawErrorMajorant
import EinsteinFull.Blueprint.G3.Proofs.C6CoarseIdentification
import EinsteinFull.Calculus.ParabolicBridgeOsc
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM
open EinsteinRelation.Correctors EinsteinRelation.ReductionImageV3
open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinFull.External.Source.AKM
/-- The literal raw matrix-clock error has the structural coarse L² decay rate. -/
theorem covarianceCoarse_raw_vector_L2_bound :
    ∀ (hmom : node_corrector_u2D_construction_u23_smooth_u2D_momentsStmt)
      (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ C : ℝ, 0 < C ∧
    ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      HasSmoothBounds D Q → ∀ r : ℝ, D.dependenceRange ≤ r → ∀ x : Vec d,
      covarianceL2Size (reducedLaw Q)
        (fun ω (a : JointObservationIndex d) => match a with
          | .inl (j, k) =>
            (∫ z : Vec d, heatKernel 0 r z *
              commutatorObservation Q j k (translate (x-z) ω)) -
                covarianceCoarseEntry D Q r x j k ω
          | .inr _ => 0) ≤ C * r ^ (-(d : ℝ)) := by
  classical
  intro hmom d hd D
  obtain ⟨C₀, hC₀, hmajor⟩ := covarianceCoarse_raw_error_L2_majorant hmom d hd D
  let N : ℝ := Fintype.card (JointObservationIndex d)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  refine ⟨(Real.sqrt N + 1) * C₀, mul_pos (by positivity) hC₀, ?_⟩
  intro Q hs r hr x
  obtain ⟨W, hWm, hWn, hWa⟩ := hmajor Q hs r hr x
  let v : FieldPair d → JointObservationIndex d → ℝ := fun ω a => match a with
    | .inl (j, k) =>
      (∫ z : Vec d, heatKernel 0 r z *
        commutatorObservation Q j k (translate (x-z) ω)) -
          covarianceCoarseEntry D Q r x j k ω
    | .inr _ => 0
  have hv : ∀ᵐ ω ∂reducedLaw Q, ∀ a, (v ω a) ^ 2 ≤ (W ω) ^ 2 := by
    filter_upwards [hWa] with ω hω a
    have habs : |v ω a| ≤ |W ω| := by
      cases a with
      | inl jk => exact (hω jk.1 jk.2).trans (le_abs_self _)
      | inr u => simpa only [v, abs_zero] using abs_nonneg (W ω)
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (v ω a)) (abs_nonneg (W ω))).2 habs
  have hvec : ∀ᵐ ω ∂reducedLaw Q,
      (covarianceVectorSize (v ω)) ^ 2 ≤ N * (W ω) ^ 2 := by
    filter_upwards [hv] with ω hω
    rw [covarianceVectorSize, Real.sq_sqrt (Finset.sum_nonneg fun a _ => sq_nonneg _)]
    calc
      _ ≤ ∑ _a : JointObservationIndex d, (W ω) ^ 2 :=
        Finset.sum_le_sum fun a _ => hω a
      _ = N * (W ω) ^ 2 := by simp only [Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, N]
  have hint : (∫ ω, (covarianceVectorSize (v ω)) ^ 2 ∂reducedLaw Q) ≤
      N * ∫ ω, (W ω) ^ 2 ∂reducedLaw Q := by
    rw [← integral_const_mul]
    exact integral_mono_of_nonneg (ae_of_all _ fun ω => sq_nonneg _)
      (hWm.integrable_sq.const_mul N) hvec
  have hB : 0 ≤ C₀ * r ^ (-(d : ℝ)) :=
    mul_nonneg hC₀.le (Real.rpow_nonneg (le_trans (le_trans zero_le_one D.one_le_dependenceRange) hr) _)
  have hWsqrt : Real.sqrt (∫ ω, (W ω) ^ 2 ∂reducedLaw Q) ≤
      C₀ * r ^ (-(d : ℝ)) := by
    rw [EinsteinFull.ParabolicBridge.sqrt_integral_sq_eq _ hWm]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hWn).trans_eq
      (ENNReal.toReal_ofReal hB)
  change Real.sqrt (∫ ω, (covarianceVectorSize (v ω)) ^ 2 ∂reducedLaw Q) ≤ _
  calc
    _ ≤ Real.sqrt (N * ∫ ω, (W ω) ^ 2 ∂reducedLaw Q) := Real.sqrt_le_sqrt hint
    _ = Real.sqrt N * Real.sqrt (∫ ω, (W ω) ^ 2 ∂reducedLaw Q) := Real.sqrt_mul hN _
    _ ≤ Real.sqrt N * (C₀ * r ^ (-(d : ℝ))) :=
      mul_le_mul_of_nonneg_left hWsqrt (Real.sqrt_nonneg _)
    _ ≤ (Real.sqrt N + 1) * C₀ * r ^ (-(d : ℝ)) := by
      nlinarith [Real.sqrt_nonneg N]
end EinsteinFull.Blueprint
