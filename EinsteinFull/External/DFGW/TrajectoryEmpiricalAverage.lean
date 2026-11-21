import EinsteinFull.External.DFGW.TrajectoryMeanErgodicL1
import EinsteinFull.External.DFGW.ShiftInvariance

/-! # Empirical trajectory averages

The normalized sum of any integrable trajectory observable over a positive time grid converges
in probability to its mean.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Empirical averages of an integrable observable over a positive trajectory grid converge
in probability to its mean. -/
theorem tendstoInMeasure_shift_empiricalAverage (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (hμ : μ Set.univ ≠ ⊤) (hPfin : P Set.univ ≠ ⊤) {t : ℝ≥0} (ht : 0 < t)
    (f : C(ℝ, S) → ℝ) (hf : Integrable f P) :
    TendstoInMeasure P (fun (n : ℕ) η => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
      f (Draft.dfgwShift ((k • t : ℝ≥0) : ℝ) η)) atTop (fun _ => ∫ η, f η ∂P) := by
  let : IsProbabilityMeasure P := hP.probability
  let F : Lp ℝ 1 P := (memLp_one_iff_integrable.mpr hf).toLp f
  let U := trajectoryShiftOperatorL1 hP t
  let M := trajectoryMeanOperator hP hPfin
  let hshift : MeasurePreserving (Draft.dfgwShift (S := S) t) P P :=
    ⟨measurable_shift _, hP.stationary _⟩
  have hF : F =ᵐ[P] f := MemLp.coeFn_toLp (memLp_one_iff_integrable.mpr hf)
  have hit (k : ℕ) : U^[k] F =ᵐ[P]
      fun η => f (Draft.dfgwShift ((k • t : ℝ≥0) : ℝ) η) := by
    induction k with
    | zero =>
      filter_upwards [hF] with η hη
      simpa only [Function.iterate_zero_apply, zero_nsmul, NNReal.coe_zero, shift_zero] using hη
    | succ k ih =>
      have hi := hshift.quasiMeasurePreserving.ae ih
      filter_upwards [Lp.coeFn_compMeasurePreserving (U^[k] F) hshift, hi] with η ha hb
      change U (U^[k] F) η = (U^[k] F) (Draft.dfgwShift t η) at ha
      rw [Function.iterate_succ_apply', ha, hb, shift_shift]
      simp only [succ_nsmul, NNReal.coe_add, add_comm]
  have hitall : ∀ᵐ η ∂P, ∀ k : ℕ, U^[k] F η =
      f (Draft.dfgwShift ((k • t : ℝ≥0) : ℝ) η) := ae_all_iff.mpr hit
  have hleft (n : ℕ) : (birkhoffAverage ℝ U id n F : Lp ℝ 1 P) =ᵐ[P]
      fun η => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
        f (Draft.dfgwShift ((k • t : ℝ≥0) : ℝ) η) := by
    have hsmul := Lp.coeFn_smul (n : ℝ)⁻¹ (∑ k ∈ Finset.range n, U^[k] F)
    have hsum := Lp.coeFn_finsetSum (Finset.range n) (fun k => U^[k] F)
    filter_upwards [hsmul, hsum, hitall] with η ha hb hc
    simp only [birkhoffAverage, birkhoffSum, id_eq]
    rw [ha]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hb]
    simp only [Finset.sum_apply, hc]
  have hright : M F =ᵐ[P] fun _ => ∫ η, f η ∂P := by
    have hint : L1.integralCLM F = ∫ η, f η ∂P := by
      rw [← L1.integral_eq, L1.integral_eq_integral]
      exact integral_congr_ae hF
    have hsmul := Lp.coeFn_smul (∫ η, f η ∂P)
      (indicatorConstLp 1 MeasurableSet.univ hPfin (1 : ℝ))
    have hone := indicatorConstLp_coeFn (p := 1) (hs := MeasurableSet.univ)
      (hμs := hPfin) (c := (1 : ℝ))
    filter_upwards [hsmul, hone] with η ha hb
    change (L1.integralCLM F • indicatorConstLp 1 MeasurableSet.univ hPfin (1 : ℝ)) η = _
    rw [hint, ha]
    simp only [Pi.smul_apply]
    rw [hb]
    simp only [Set.indicator_univ, smul_eq_mul, mul_one]
  have h := tendstoInMeasure_of_tendsto_Lp
    (tendsto_shift_birkhoffAverage_L1 hP hcoord hμ hPfin ht F)
  exact TendstoInMeasure.congr hleft hright h

end EinsteinFull.External.DFGW
