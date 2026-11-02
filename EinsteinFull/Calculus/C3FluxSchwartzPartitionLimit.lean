import EinsteinFull.Calculus.CarverSFluxGeneralTestGain
import EinsteinFull.Calculus.K6KernelAverageLp

open MeasureTheory Filter EinsteinRelation
open scoped Topology ENNReal

namespace EinsteinFull.Blueprint

 theorem c3_schwartz_average_lp_bound_of_finite_partition_bounds
    {d : ℕ} {Λ r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀)
    (r : ℝ) (hr : 0 < r) (ψ : SchwartzMap (Vec d) ℂ)
    (J : Lp ℂ 2 (reducedLaw Q)) (p B : ℝ)
    (hfinite : ∀ S : Finset (Fin d → ℤ),
      let b := fun z : Fin d → ℤ => centeredComplexLp Q (∫ y : Vec d,
        ((fluxPartitionCutoff r (y - fun i => r * (z i : ℝ)) : ℂ) * ψ (-y)) •
          complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J)
      MemLp (∑ z ∈ S, (b z : FieldPair d → ℂ)) (ENNReal.ofReal p) (reducedLaw Q) ∧
      (eLpNorm (∑ z ∈ S, (b z : FieldPair d → ℂ))
        (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ B) :
    MemLp (stationarySchwartzAverage Q ψ (centeredComplexLp Q J) : FieldPair d → ℂ)
      (ENNReal.ofReal p) (reducedLaw Q) ∧
    (eLpNorm (stationarySchwartzAverage Q ψ (centeredComplexLp Q J) : FieldPair d → ℂ)
      (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ B := by
  let b := fun z : Fin d → ℤ => centeredComplexLp Q (∫ y : Vec d,
    ((fluxPartitionCutoff r (y - fun i => r * (z i : ℝ)) : ℂ) * ψ (-y)) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J)
  have hB : 0 ≤ B := by
    have h := (hfinite ∅).2
    simpa using h
  have hcoe (S : Finset (Fin d → ℤ)) :
      ((∑ z ∈ S, b z : Lp ℂ 2 (reducedLaw Q)) : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
        ∑ z ∈ S, (b z : FieldPair d → ℂ) := by
    induction S using Finset.induction_on with
    | empty => simpa using (Lp.coeFn_zero ℂ 2 (reducedLaw Q))
    | @insert a S ha ih =>
      simp only [Finset.sum_insert ha]
      filter_upwards [Lp.coeFn_add (b a) (∑ z ∈ S, b z), ih] with x hx hi
      simp only [hx, hi, Pi.add_apply]
  have hball (S : Finset (Fin d → ℤ)) :
      (∑ z ∈ S, b z) ∈ EinsteinFull.Calculus.K6.lpBall (reducedLaw Q)
        (ENNReal.ofReal p) (ENNReal.ofReal B) := by
    have hf := hfinite S
    change eLpNorm ((∑ z ∈ S, b z : Lp ℂ 2 (reducedLaw Q)) : FieldPair d → ℂ) _ _ ≤ _
    rw [eLpNorm_congr_ae (hcoe S)]
    rw [← ENNReal.ofReal_toReal hf.1.eLpNorm_ne_top]
    exact ENNReal.ofReal_le_ofReal hf.2
  have hlim := flux_schwartz_centered_partition_hasSum Q hr ψ J
  have hmem : stationarySchwartzAverage Q ψ (centeredComplexLp Q J) ∈
      EinsteinFull.Calculus.K6.lpBall (reducedLaw Q) (ENNReal.ofReal p) (ENNReal.ofReal B) :=
    (EinsteinFull.Calculus.K6.isClosed_lpBall _ _ _).mem_of_tendsto hlim
      (Filter.Eventually.of_forall hball)
  have hnorm : eLpNorm (stationarySchwartzAverage Q ψ (centeredComplexLp Q J) : FieldPair d → ℂ)
      (ENNReal.ofReal p) (reducedLaw Q) ≤ ENNReal.ofReal B := hmem
  refine ⟨lt_of_le_of_lt hnorm ENNReal.ofReal_lt_top, ?_⟩
  exact (ENNReal.toReal_le_toReal (lt_of_le_of_lt hnorm ENNReal.ofReal_lt_top).ne
    ENNReal.ofReal_ne_top).2 hnorm |>.trans_eq (ENNReal.toReal_ofReal hB)

end EinsteinFull.Blueprint
