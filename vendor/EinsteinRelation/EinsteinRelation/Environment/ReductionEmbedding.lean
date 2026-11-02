import EinsteinRelation.Environment.FieldMeasurability
import EinsteinRelation.Probability.ReductionLocality
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! # Actual joint reduction as a measurable embedding

Source `paper/main.tex:198–207,234–248`. The literal map (a₀,V) ↦ (exp(-2V)a₀,
exp(-2V)) is injective; positivity of the actual exponential and real logarithm
recover the physical pair. Polish compact-open carriers give a measurable
embedding. Its measurable left inverse reconstructs every physical sample
exactly, and the first consumer checks translation compatibility on that image.
No inverse is asserted for arbitrary raw reduced pairs, and no H¹ transport is
assumed; that transport must consume these proved properties.
-/

noncomputable section
namespace EinsteinRelation.Probability

theorem injective_reduce {d : ℕ} : Function.Injective (reduce (d := d)) := by
  intro ω η heq
  apply Prod.ext
  · apply ContinuousMap.ext
    intro x
    have hμ := congrArg (fun ρ : FieldPair d => ρ.2 x) heq
    change clockDensity ω x = clockDensity η x at hμ
    have hA := congrArg (fun ρ : FieldPair d => ρ.1 x) heq
    change clockDensity ω x • ω.1 x = clockDensity η x • η.1 x at hA
    rw [← hμ] at hA
    have hi := congrArg (fun A : Mat d => (clockDensity ω x)⁻¹ • A) hA
    simpa only [smul_smul, inv_mul_cancel₀ (clockDensity_pos ω x).ne', one_smul] using hi
  · apply ContinuousMap.ext
    intro x
    have hμ := congrArg (fun ρ : FieldPair d => ρ.2 x) heq
    change Real.exp (-2 * ω.2 x) = Real.exp (-2 * η.2 x) at hμ
    have hV := Real.exp_injective hμ
    linarith

theorem measurableEmbedding_reduce (d : ℕ) :
    MeasurableEmbedding (reduce (d := d)) := by
  letI : PolishSpace (CoefficientField d) := Localization.coefficientField_polish d
  letI : PolishSpace (FieldPair d) := inferInstance
  exact continuous_reduce.measurableEmbedding injective_reduce

theorem exists_measurable_leftInverse_reduce (d : ℕ) :
    ∃ D : FieldPair d → FieldPair d, Measurable D ∧ Function.LeftInverse D reduce := by
  have h := measurableEmbedding_reduce d
  exact ⟨h.invFun, h.measurable_invFun, h.leftInverse_invFun⟩

/-- The actual reconstructed physical sample respects translated reduced observations. -/
theorem leftInverse_reduce_translate {d : ℕ} (D : FieldPair d → FieldPair d)
    (hD : Function.LeftInverse D reduce) (ω : FieldPair d) (x : Vec d) :
    D (translate x (reduce ω)) = translate x ω := by
  rw [← reduce_translate]
  exact hD (translate x ω)

end EinsteinRelation.Probability
