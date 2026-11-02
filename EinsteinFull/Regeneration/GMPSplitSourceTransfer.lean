import EinsteinFull.External.Source.GMPSplitCoupling
import EinsteinRelation.Probability.FiniteHistoryMeasurability
import Mathlib.Probability.Independence.Integration

/-! Internal transfers of GMP's literal fixed-environment split-coupling
properties to the existing actual path/coin predicates. These proofs construct
no joint environment kernel and assume no regeneration factorization. -/

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration
open EinsteinRelation EinsteinRelation.Regeneration
open EinsteinFull.External.Source.GMP

/-- The literal singleton coin marginal extracted from the source iid law. -/
theorem source_split_coin_measure {d : ℕ}
    {P : Vec d → Measure (Path d)} {Δ : ℝ≥0} {δ R : ℝ} {i : Fin d}
    {K : Vec d → Measure (CoupledSample d)}
    (hK : IsSourceSplitCoupling P Δ δ R i K) (x : Vec d) (n : ℕ) (b : Bool) :
    K x {z | z.2 n = b} = ENNReal.ofReal (if b then δ else 1 - δ) := by
  have h := (hK x).2.2.1 {n} (fun _ => b)
  simpa only [Finset.prod_singleton, Finset.mem_singleton, forall_eq] using h

/-- The source future-sequence independence supplies the exact finite-history
fresh-coin test identity used by the frozen coupling predicate. This transfer
constructs no environment-measurable kernel and assumes no factorization. -/
theorem source_split_fresh_bits {d : ℕ} {P : Vec d → Measure (Path d)}
    {Δ : ℝ≥0} {δ R : ℝ} {i : Fin d}
    (K : CoupledQuenchedLaws d) (ω : FieldPair d)
    (hK : IsSourceSplitCoupling P Δ δ R i (fun x => K (x, ω)))
    (hδ : 0 ≤ δ) (x : Vec d) :
    FreshBitsAt Δ δ K (x, ω) := by
  letI : IsProbabilityMeasure (K (x, ω)) := (hK x).1
  intro n H hH _hb
  let χ : CoupledSample d → ℝ := fun z => if z.2 n = true then 1 else 0
  have hs : MeasurableSet {z : CoupledSample d | z.2 n = true} :=
    measurableSet_eq_fun ((measurable_pi_apply n).comp measurable_snd) measurable_const
  have hχ : Measurable χ := by
    exact measurable_const.ite hs measurable_const
  have hχfuture : @Measurable (CoupledSample d) ℝ
      (MeasurableSpace.comap
        (fun z : CoupledSample d => fun m : ℕ => z.2 (n + m)) inferInstance)
      inferInstance χ := by
    have hfuture : @Measurable (CoupledSample d) (ℕ → Bool)
        (MeasurableSpace.comap
          (fun z : CoupledSample d => fun m : ℕ => z.2 (n + m)) inferInstance)
        inferInstance (fun z => fun m : ℕ => z.2 (n + m)) := Measurable.of_comap_le le_rfl
    have hn : @Measurable (CoupledSample d) Bool
        (MeasurableSpace.comap
          (fun z : CoupledSample d => fun m : ℕ => z.2 (n + m)) inferInstance)
        inferInstance (fun z => z.2 n) := by
      exact (measurable_pi_apply 0).comp hfuture
    exact measurable_const.ite (measurableSet_eq_fun hn measurable_const) measurable_const
  have hind : ProbabilityTheory.IndepFun H χ (K (x, ω)) := by
    exact ProbabilityTheory.indep_of_indep_of_le_right
      (ProbabilityTheory.indep_of_indep_of_le_left ((hK x).2.2.2.1 n).symm
        hH.comap_le) hχfuture.comap_le
  have hχint : (∫ z, χ z ∂K (x, ω)) = δ := by
    have heq : χ = Set.indicator {z : CoupledSample d | z.2 n = true}
        (fun _ => (1 : ℝ)) := by
      funext z
      simp only [χ, Set.indicator, Set.mem_setOf_eq]
    rw [heq, integral_indicator_const (1 : ℝ) hs, smul_eq_mul, mul_one, measureReal_def,
      source_split_coin_measure hK x n true]
    simp only [↓reduceIte, ENNReal.toReal_ofReal hδ]
  change (∫ z, H z * χ z ∂K (x, ω)) = δ * ∫ z, H z ∂K (x, ω)
  rw [hind.integral_fun_mul_eq_mul_integral
    (hH.mono (EinsteinRelation.Probability.finiteHistorySigma_le Δ n) le_rfl).aestronglyMeasurable
    hχ.aestronglyMeasurable, hχint, mul_comm]

end EinsteinFull.Regeneration
