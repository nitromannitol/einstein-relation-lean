import EinsteinFull.External.DFGW.FutureProjection
import Mathlib.MeasureTheory.Function.FactorsThrough

/-! # State representatives of future conditional expectations

The Markov projection of a future `L²` observable has a square-integrable state representative
with the same mean.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The conditional expectation of a future `L²` observable has a state `L²` representative
with the same mean. -/
theorem exists_state_condExp_future (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (Z : Lp ℝ 2 P)
    (hZ : AEStronglyMeasurable[Draft.dfgwCoordSigma (Set.Ici 0)] Z P) :
    ∃ g : Lp ℝ 2 μ,
      P[Z | Draft.dfgwCoordSigma (Set.Iic 0)] =ᵐ[P] (fun η : C(ℝ, S) => g (η 0)) ∧
      (∫ x, g x ∂μ) = ∫ η, Z η ∂P := by
  let : IsProbabilityMeasure P := hP.probability
  let : IsProbabilityMeasure μ := hP.invariant_probability
  have heval : Measurable[Draft.dfgwTrajectoryMeasurableSpace (S := S), inferInstance]
      (fun η : C(ℝ, S) => η 0) := (continuous_eval_const 0).measurable
  let hK : MeasurableSpace.comap (fun η : C(ℝ, S) => η 0) inferInstance ≤
      Draft.dfgwTrajectoryMeasurableSpace (S := S) :=
    heval.comap_le
  let hσ := (Draft.dfgwPast (S := S)).le 0
  let Q := pastProjection P Z
  have hfix : stateProjection P Q = Q := future_mem_stateDeterminedPast hP Z hZ
  have hm : AEStronglyMeasurable[MeasurableSpace.comap (fun η : C(ℝ, S) => η 0) inferInstance] Q P := by
    have h := aestronglyMeasurable_condExpL2 (𝕜 := ℝ) hK Q
    change AEStronglyMeasurable[MeasurableSpace.comap (fun η : C(ℝ, S) => η 0) inferInstance] (stateProjection P Q) P at h
    rwa [hfix] at h
  obtain ⟨v, hvsm, hv⟩ := hm
  obtain ⟨g, hgsm, hg⟩ := hvsm.exists_eq_measurable_comp
  have hvcomp : Q =ᵐ[P] (fun η : C(ℝ, S) => g (η 0)) := by
    filter_upwards [hv] with η hη
    simpa only [hg, Function.comp_apply] using hη
  have hqmem : MemLp (fun η : C(ℝ, S) => g (η 0)) 2 P :=
    MemLp.ae_eq hvcomp (Lp.memLp Q)
  have hgmem : MemLp g 2 μ := by
    have hmap : MemLp g 2 (P.map (fun η : C(ℝ, S) => η 0)) :=
      (memLp_map_measure_iff (μ := P) hgsm.aestronglyMeasurable heval.aemeasurable).2 hqmem
    rwa [hP.marginal 0] at hmap
  let G : Lp ℝ 2 μ := hgmem.toLp g
  have hG' : (fun η : C(ℝ, S) => G (η 0)) =ᵐ[P] fun η => g (η 0) :=
    ((show MeasurePreserving (fun η : C(ℝ, S) => η 0) P μ from
      ⟨heval, hP.marginal 0⟩).quasiMeasurePreserving.ae
        (MemLp.coeFn_toLp hgmem))
  have hc : Q =ᵐ[P] P[Z | Draft.dfgwCoordSigma (Set.Iic 0)] := by
    change (condExpL2 ℝ ℝ hσ Z : Lp ℝ 2 P) =ᵐ[P] _
    have hz : (Lp.memLp Z).toLp Z = Z := Lp.toLp_coeFn Z (Lp.memLp Z)
    have h := (Lp.memLp Z).condExpL2_ae_eq_condExp (𝕜 := ℝ) hσ
    rwa [hz] at h
  have hGm : AEStronglyMeasurable (G : S → ℝ)
      (P.map (fun η : C(ℝ, S) => η 0)) := by
    rw [hP.marginal 0]
    exact Lp.aestronglyMeasurable G
  have hGint : (∫ x, G x ∂μ) = ∫ η, G (η 0) ∂P := by
    calc
      _ = ∫ x, G x ∂(P.map (fun η : C(ℝ, S) => η 0)) := by rw [hP.marginal 0]
      _ = _ := integral_map heval.aemeasurable hGm
  refine ⟨G, hc.symm.trans (hvcomp.trans hG'.symm), ?_⟩
  rw [hGint]
  calc
    _ = ∫ η, Q η ∂P := integral_congr_ae (hG'.trans hvcomp.symm)
    _ = ∫ η, P[Z | Draft.dfgwCoordSigma (Set.Iic 0)] η ∂P := integral_congr_ae hc
    _ = _ := @integral_condExp C(ℝ, S) ℝ (Draft.dfgwCoordSigma (Set.Iic 0))
      (Draft.dfgwTrajectoryMeasurableSpace (S := S)) P (Z : C(ℝ, S) → ℝ) _ _ _ hσ
      (@IsFiniteMeasure.toSigmaFinite C(ℝ, S) (Draft.dfgwCoordSigma (Set.Iic 0))
        (P.trim hσ) (isFiniteMeasure_trim hσ))

end EinsteinFull.External.DFGW
