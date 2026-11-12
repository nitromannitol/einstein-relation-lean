import EinsteinRelation.External.AKMLocalCorrectors
import EinsteinRelation.Correctors.ScalarRmsTriangle
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory
open ENNReal
namespace EinsteinRelation.Correctors
open External.AKM

private theorem abs_coord_le_euclideanNorm' {d : ℕ} (v : Vec d) (j : Fin d) :
    |v j| ≤ euclideanNorm v := by
  unfold euclideanNorm euclideanSq dot
  apply Real.abs_le_sqrt
  have h := Finset.single_le_sum (f := fun k => v k * v k)
    (fun k _ => mul_self_nonneg (v k)) (Finset.mem_univ j)
  simpa only [sq] using h

private theorem euclideanSq_nonneg {d : ℕ} (x : Vec d) : 0 ≤ euclideanSq x := by
  rw [euclideanSq, dot]
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))

private theorem sqrt_integral_euclideanSq_eq {d : ℕ} {U : Set (Vec d)}
    [IsFiniteMeasure (volume.restrict U)] (G : Vec d → Vec d) :
    Real.sqrt (∫ x in U, euclideanSq (G x)) =
      Real.sqrt ((volume U).toReal) * vectorRms volume U G := by
  by_cases hVzero : (volume U).toReal = 0
  · have h_int_zero : ∫ x in U, euclideanSq (G x) = 0 := by
      have h_fin : (volume.restrict U) Set.univ < ∞ :=
        (inferInstance : IsFiniteMeasure (volume.restrict U)).measure_univ_lt_top
      have h_vol_zero : volume U = 0 := by
        rcases (ENNReal.toReal_eq_zero_iff (volume U)).mp hVzero with (h | h)
        · exact h
        · have h_fin' : volume U < ∞ := by
            rw [Measure.restrict_apply_univ] at h_fin
            exact h_fin
          exact (h_fin'.ne h).elim
      simp [h_vol_zero]
    simp [hVzero, h_int_zero]
  · have hvol_pos : 0 < (volume U).toReal :=
      lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hVzero)
    simp only [vectorRms, average_eq, Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
    rw [← Real.sqrt_mul hvol_pos.le, ← mul_assoc, mul_inv_cancel₀ hVzero, one_mul]

private theorem sqrt_integral_sq_eq_eLpNorm_toReal {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (f : X → ℝ) (hf : MemLp f 2 μ) :
    Real.sqrt (∫ x, f x ^ 2 ∂μ) = (eLpNorm f 2 μ).toReal := by
  rw [hf.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
    ENNReal.toReal_ofReal (by positivity), Real.sqrt_eq_rpow]
  congr 1
  · refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  · simp

/-- A spatial energy RMS bounds every normalized distributional derivative test.
Source: `paper/main.tex:798–806`; the local a.e. bound before taking time traces. -/
theorem weakGradient_test_bound_vectorRms {d : ℕ}
    {U : Set (Vec d)} [IsFiniteMeasure (volume.restrict U)]
    {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hw : HasWeakGradient U u G)
    (hG : MemLp (fun x => euclideanNorm (G x)) 2 (volume.restrict U))
    (i : Fin d) {ψ : Vec d → ℝ} (hψ : IsSpatialTest U ψ) :
    |∫ x in U, u x * coordinateDerivative i ψ x| ≤
      Real.sqrt ((volume U).toReal) * vectorRms volume U G *
        (eLpNorm ψ 2 (volume.restrict U)).toReal := by
  -- From the weak gradient, get the pairing identity
  have h_eq := (hw i).2.2 ψ hψ
  -- h_eq : (∫ x in U, u x * coordinateDerivative i ψ x) = -(∫ x in U, (G x i) * ψ x)
  rw [h_eq, abs_neg]
  -- Now we need: |∫ x in U, (G x i) * ψ x| ≤ ...
  -- Get MemLp for ψ (from smooth + compact support)
  have hψ_cont : Continuous ψ := hψ.1.continuous
  have hψ_memLp : MemLp ψ 2 (volume.restrict U) :=
    hψ_cont.memLp_of_hasCompactSupport hψ.2.1
  -- Get MemLp for G x i from hG and the pointwise bound
  have hG_i_bound : ∀ x, |G x i| ≤ euclideanNorm (G x) := fun x =>
    abs_coord_le_euclideanNorm' (G x) i
  have hG_i_memLp : MemLp (fun x => G x i) 2 (volume.restrict U) := by
    refine MemLp.mono' hG ?_ (ae_of_all _ hG_i_bound)
    -- Need AEStronglyMeasurable (fun x => G x i)
    -- From hw i, we have LocallyIntegrableOn (fun x => G x i) U volume
    have h_loc : LocallyIntegrableOn (fun x => G x i) U volume := (hw i).2.1
    -- LocallyIntegrableOn gives AEStronglyMeasurable
    exact h_loc.aestronglyMeasurable
  -- Apply Cauchy-Schwarz inequality
  have h_cauchy_sq := cauchy_schwarz_integral hG_i_memLp hψ_memLp
  -- h_cauchy_sq : (∫ x, (G x i) * ψ x ∂(volume.restrict U))^2 ≤ ...
  -- This is the same as (∫ x in U, (G x i) * ψ x)^2 ≤ ...
  set I := ∫ x in U, (G x i) * ψ x
  set A := ∫ x in U, (G x i)^2
  set B := ∫ x in U, ψ x ^ 2
  have hA_nonneg : 0 ≤ A := integral_nonneg (fun x => sq_nonneg _)
  have hB_nonneg : 0 ≤ B := integral_nonneg (fun x => sq_nonneg _)
  -- From Cauchy-Schwarz, we get |I| ≤ sqrt(A) * sqrt(B)
  have h_abs_le : |I| ≤ Real.sqrt A * Real.sqrt B := by
    have h_sq : I ^ 2 ≤ (Real.sqrt A * Real.sqrt B) ^ 2 := by
      calc
        I ^ 2 ≤ A * B := h_cauchy_sq
        _ = (Real.sqrt A) ^ 2 * (Real.sqrt B) ^ 2 := by
          rw [Real.sq_sqrt hA_nonneg, Real.sq_sqrt hB_nonneg]
        _ = (Real.sqrt A * Real.sqrt B) ^ 2 := by ring
    have h_nonneg : 0 ≤ Real.sqrt A * Real.sqrt B :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have h_abs_sq : |I| ^ 2 ≤ (Real.sqrt A * Real.sqrt B) ^ 2 := by
      rw [sq_abs]
      exact h_sq
    nlinarith
  -- Now relate sqrt(A) to vectorRms and sqrt(B) to eLpNorm
  -- Step 1: A ≤ ∫ euclideanSq (G x)
  have hA_le : A ≤ ∫ x in U, euclideanSq (G x) := by
    refine integral_mono (hG_i_memLp.integrable_sq) ?_ (fun x => ?_)
    · -- integrability of euclideanSq (G x)
      have hG_sq_int : Integrable (fun x => (euclideanNorm (G x)) ^ 2) (volume.restrict U) :=
        hG.integrable_sq
      have h_eq_sq : (fun x => euclideanSq (G x)) = (fun x => (euclideanNorm (G x)) ^ 2) := by
        ext x
        have h := euclideanSq_nonneg (G x)
        dsimp [euclideanSq, euclideanNorm] at h ⊢
        rw [Real.sq_sqrt h]
      rw [h_eq_sq]
      exact hG_sq_int
    · -- pointwise inequality: (G x i)^2 ≤ euclideanSq (G x)
      rw [euclideanSq, dot]
      have h := Finset.single_le_sum (f := fun k => G x k * G x k)
        (fun k _ => mul_self_nonneg (G x k)) (Finset.mem_univ i)
      simpa only [sq] using h
  -- Step 2: Relate sqrt(A) to vectorRms
  have h_sqrt_A_le : Real.sqrt A ≤ vectorRms volume U G * Real.sqrt ((volume U).toReal) := by
    calc
      Real.sqrt A ≤ Real.sqrt (∫ x in U, euclideanSq (G x)) := Real.sqrt_le_sqrt hA_le
      _ = Real.sqrt ((volume U).toReal) * vectorRms volume U G :=
        sqrt_integral_euclideanSq_eq G
      _ = vectorRms volume U G * Real.sqrt ((volume U).toReal) := mul_comm _ _
  -- Step 3: Relate sqrt(B) to eLpNorm
  have h_sqrt_B : Real.sqrt B = (eLpNorm ψ 2 (volume.restrict U)).toReal := by
    -- B = ∫_U ψ^2, which is definitionally ∫ ψ^2 ∂(volume.restrict U)
    exact sqrt_integral_sq_eq_eLpNorm_toReal ψ hψ_memLp
  -- Combine everything
  calc
    |I| ≤ Real.sqrt A * Real.sqrt B := h_abs_le
    _ ≤ (vectorRms volume U G * Real.sqrt ((volume U).toReal)) * Real.sqrt B := by
      gcongr
    _ = Real.sqrt ((volume U).toReal) * vectorRms volume U G * Real.sqrt B := by ring
    _ = Real.sqrt ((volume U).toReal) * vectorRms volume U G *
        (eLpNorm ψ 2 (volume.restrict U)).toReal := by rw [h_sqrt_B]

end EinsteinRelation.Correctors
