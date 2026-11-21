import EinsteinFull.External.DFGW.FutureIndicatorProjection

/-! # Past projections of future observables

Every square-integrable future observable has a past conditional expectation determined by the
current state.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Every square-integrable future-coordinate observable has a state-determined past projection. -/
theorem future_mem_stateDeterminedPast (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (f : Lp ℝ 2 P)
    (hf : AEStronglyMeasurable[Draft.dfgwCoordSigma (Set.Ici 0)] f P) :
    f ∈ stateDeterminedPast P := by
  let : IsProbabilityMeasure P := hP.probability
  let L := stateDeterminedPast P
  have hscale (B : Set C(ℝ, S)) (hB : MeasurableSet B) (c : ℝ) :
      indicatorConstLp 2 hB (measure_ne_top P B) c =
        c • indicatorConstLp 2 hB (measure_ne_top P B) (1 : ℝ) := by
    apply Lp.ext
    filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hB)
      (hμs := measure_ne_top P B) (c := c),
      indicatorConstLp_coeFn (p := 2) (hs := hB)
        (hμs := measure_ne_top P B) (c := (1 : ℝ)),
      Lp.coeFn_smul c (indicatorConstLp 2 hB (measure_ne_top P B) (1 : ℝ))] with x hc h1 hs
    rw [hs, hc]
    simp only [Pi.smul_apply]
    rw [h1]
    by_cases hx : x ∈ B <;> simp [hx, smul_eq_mul]
  have hall := Lp.induction_stronglyMeasurable (μ := P) (p := 2) futureCoordSigma_le
    (by simp : (2 : ℝ≥0∞) ≠ ⊤) (fun f : Lp ℝ 2 P => f ∈ L)
    (by
      intro c B hB hfin
      change indicatorConstLp 2 (futureCoordSigma_le B hB) hfin.ne c ∈ L
      rw [hscale]
      exact L.smul_mem c (future_indicator_mem_stateDeterminedPast hP B hB (measure_ne_top P B)))
    (by
      intro a b ha hb ham hbm hdisj hla hlb
      exact L.add_mem hla hlb)
    (by
      change IsClosed ((fun f : lpMeas ℝ ℝ (Draft.dfgwCoordSigma (Set.Ici 0)) 2 P =>
        (f : Lp ℝ 2 P)) ⁻¹' (L : Set (Lp ℝ 2 P)))
      exact (isClosed_stateDeterminedPast P).preimage continuous_subtype_val)
  exact hall f hf

end EinsteinFull.External.DFGW
