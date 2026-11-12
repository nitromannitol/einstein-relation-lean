import EinsteinRelation.Probability.ConjugateKernel

/-!
# Transport of the actual semigroup quadratic form

Source `paper/main.tex:406–408`. A spatial coordinate change conjugates
the transition kernel and rescales the reversible measure by one
positive constant. The short-time form is rescaled by precisely that
constant, with no measurability assumption on a chosen representative.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinRelation.External.GantertSection7Support

/-- A measurable coordinate change and constant measure scaling transport
all the actual semigroup difference quotients. -/
theorem semigroupFormDifferenceQuotient_conjugate {d : ℕ}
    (ω ω' : FieldPair d) (hd : 2 ≤ d) (lam : ℝ)
    (e : Vec d ≃ᵐ Vec d) (c : ℝ) (hc : 0 ≤ c)
    (hm : (physicalReversibleMeasure ω' hd lam).map e =
      ENNReal.ofReal c • physicalReversibleMeasure ω hd lam)
    (K : ℝ≥0 → Kernel (Vec d) (Vec d)) (t : ℝ≥0) (f : Vec d → ℝ) :
    semigroupFormDifferenceQuotient ω' hd lam (fun t => Probability.conjugateKernel e (K t)) t f =
      c * semigroupFormDifferenceQuotient ω hd lam K t (fun y => f (e.symm y)) := by
  let g : Vec d → ℝ := fun y =>
    (f (e.symm y) - ∫ z, f (e.symm z) ∂K t y) * f (e.symm y)
  have hi := integral_map_equiv (μ := physicalReversibleMeasure ω' hd lam) e g
  rw [hm, integral_smul_measure, ENNReal.toReal_ofReal hc] at hi
  have hi' : (∫ x, (f x - ∫ y, f (e.symm y) ∂K t (e x)) * f x
      ∂physicalReversibleMeasure ω' hd lam) =
      c * ∫ x, (f (e.symm x) - ∫ y, f (e.symm y) ∂K t x) * f (e.symm x)
        ∂physicalReversibleMeasure ω hd lam := by
    simpa only [g, e.symm_apply_apply, smul_eq_mul] using hi.symm
  simp only [semigroupFormDifferenceQuotient, Probability.integral_conjugateKernel]
  rw [hi']
  ring

/-- Weighted square integrability is transported by the same positive
coordinate change, even for representatives measurable only almost everywhere. -/
theorem memLp_comp_symm_of_map_eq_smul {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] (e : α ≃ᵐ α) (μ ν : Measure α)
    (c : ℝ≥0∞) (hc0 : c ≠ 0) (hct : c ≠ ∞) (hm : μ.map e = c • ν)
    (f : α → E) (p : ℝ≥0∞) (hf : MemLp f p μ) :
    MemLp (fun y => f (e.symm y)) p ν := by
  have h : MemLp (fun y => f (e.symm y)) p (μ.map e) := by
    apply e.memLp_map_measure_iff.mpr
    simpa only [Function.comp_def, e.symm_apply_apply] using hf
  rw [hm] at h
  have h' := h.smul_measure (c := c⁻¹) (by simpa using hc0)
  simpa only [smul_smul, ENNReal.inv_mul_cancel hc0 hct, one_smul] using h'


end EinsteinRelation.External.GantertSection7Support
