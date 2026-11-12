import EinsteinRelation.Environment.CoefficientRestriction
import EinsteinRelation.Probability.LocalSigma
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

open MeasureTheory
namespace EinsteinRelation.Localization

/-- Observing the actual reduced pair `(a,μ)` on any set gives exactly the
physical joint observation `(a₀,V)`. Source main.tex198–207,234–248. This uses
actual inverse formulas, not an implicit identification of the two pairs. -/
theorem localSigma_comap_reduce {d : ℕ} (U : Set (Vec d)) :
    (localSigma U).comap reduce = localSigma U := by
  let g : Mat d × ℝ → Mat d × ℝ := fun p =>
    (Real.exp (-2 * p.2) • p.1, Real.exp (-2 * p.2))
  let h : Mat d × ℝ → Mat d × ℝ := fun p =>
    (p.2⁻¹ • p.1, -(Real.log p.2) / 2)
  have hg : Measurable g := by
    exact (((Real.continuous_exp.comp (continuous_const.mul continuous_snd)).smul
      continuous_fst).prodMk (Real.continuous_exp.comp
      (continuous_const.mul continuous_snd))).measurable
  have hh : Measurable h := by
    exact (measurable_snd.inv.smul measurable_fst).prodMk
      (((Real.measurable_log.comp measurable_snd).neg).div_const 2)
  have hinv (p : Mat d × ℝ) : h (g p) = p := by
    apply Prod.ext
    · change (Real.exp (-2*p.2))⁻¹ • (Real.exp (-2*p.2) • p.1) = p.1
      rw [smul_smul, inv_mul_cancel₀ (Real.exp_ne_zero _), one_smul]
    · change -(Real.log (Real.exp (-2*p.2))) / 2 = p.2
      rw [Real.log_exp]
      ring
  unfold localSigma
  rw [MeasurableSpace.comap_iSup]
  apply iSup_congr
  intro x
  rw [MeasurableSpace.comap_comp]
  change MeasurableSpace.comap (fun ω : FieldPair d =>
    (reducedCoefficient ω x, clockDensity ω x)) _ =
    MeasurableSpace.comap (fun ω : FieldPair d => (ω.1 x, ω.2 x)) _
  let A : FieldPair d → Mat d × ℝ := fun ω => (ω.1 x, ω.2 x)
  have hB : (fun ω : FieldPair d => (reducedCoefficient ω x, clockDensity ω x)) = g ∘ A := rfl
  rw [hB]
  apply le_antisymm
  · rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hg.comap_le
  · have heq : A = h ∘ (g ∘ A) := funext fun ω => (hinv (A ω)).symm
    change (inferInstance : MeasurableSpace (Mat d × ℝ)).comap A ≤ _
    conv_lhs => rw [heq]
    rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hh.comap_le

/-- Actual finite range transports to the image law of the full reduced pair,
with the same strict gap and arbitrary Borel observation sets. -/
theorem finiteRange_map_reduce {d : ℕ} {r₀ : ℝ} (Q : Measure (FieldPair d))
    (hQ : HasFiniteRange r₀ Q) : HasFiniteRange r₀ (Q.map reduce) := by
  have hm : Continuous (fun ω : FieldPair d => (reduce ω).1) := continuous_reducedMatrixField
  have hs : Continuous (fun ω : FieldPair d => (reduce ω).2) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact Real.continuous_exp.comp
      (continuous_const.mul (continuous_fst.snd.eval continuous_snd))
  have hred : Measurable (reduce (d := d)) := (hm.prodMk hs).measurable
  intro U W hU hW hgap
  have hind : ProbabilityTheory.Indep ((localSigma U).comap reduce)
      ((localSigma W).comap reduce) Q := by
    rw [localSigma_comap_reduce, localSigma_comap_reduce]
    exact hQ U W hU hW hgap
  rw [ProbabilityTheory.Indep_iff]
  intro s t hsm htm
  have hs' : MeasurableSet s := Probability.localSigma_le_borel U s hsm
  have ht' : MeasurableSet t := Probability.localSigma_le_borel W t htm
  rw [Measure.map_apply hred (hs'.inter ht'), Measure.map_apply hred hs',
    Measure.map_apply hred ht', Set.preimage_inter]
  exact (ProbabilityTheory.Indep_iff _ _ _).1 hind _ _ ⟨s, hsm, rfl⟩ ⟨t, htm, rfl⟩
end EinsteinRelation.Localization
