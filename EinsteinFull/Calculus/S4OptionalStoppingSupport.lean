import MarkovProcess.Path.OptionalStopping
import Mathlib.Probability.Process.Stopping

/-!
# Optional stopping on an event of the stopped σ-algebra

From the unconditional continuous-time optional stopping theorem of `MarkovProcess`:
for stopping times `σ ≤ τ ≤ K`, a martingale `M` that is locally bounded with right continuous
orbits, and an event `B` of the σ-algebra of the strict past of `σ`,
`∫_B M_τ = ∫_B M_σ`.
-/

open MeasureTheory
open scoped NNReal Classical

namespace EinsteinFull

theorem isStoppingTime_piecewise_mem {Ω : Type*} {m : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m}
    {σ τ : Ω → ℝ≥0} (hσ : IsStoppingTime ℱ fun ω => (σ ω : WithTop ℝ≥0))
    (hτ : IsStoppingTime ℱ fun ω => (τ ω : WithTop ℝ≥0)) (hστ : ∀ ω, σ ω ≤ τ ω)
    {B : Set Ω} (hB : MeasurableSet[hσ.measurableSpace] B) :
    IsStoppingTime ℱ fun ω => ((B.piecewise τ σ ω : ℝ≥0) : WithTop ℝ≥0) := by
  intro t
  have hBt : MeasurableSet[ℱ t] (B ∩ {ω | (σ ω : WithTop ℝ≥0) ≤ t}) := hB.2 t
  have hσt : MeasurableSet[ℱ t] {ω | (σ ω : WithTop ℝ≥0) ≤ t} := hσ t
  have hτt : MeasurableSet[ℱ t] {ω | (τ ω : WithTop ℝ≥0) ≤ t} := hτ t
  have hset : {ω | ((B.piecewise τ σ ω : ℝ≥0) : WithTop ℝ≥0) ≤ t} =
      (B ∩ {ω | (σ ω : WithTop ℝ≥0) ≤ t}) ∩ {ω | (τ ω : WithTop ℝ≥0) ≤ t} ∪
        ({ω | (σ ω : WithTop ℝ≥0) ≤ t} \ (B ∩ {ω | (σ ω : WithTop ℝ≥0) ≤ t})) := by
    ext ω
    have hQP : (τ ω : WithTop ℝ≥0) ≤ t → (σ ω : WithTop ℝ≥0) ≤ t :=
      fun h => (WithTop.coe_le_coe.2 (hστ ω)).trans h
    by_cases hx : ω ∈ B <;> simp [Set.piecewise, hx] <;> tauto
  rw [hset]
  exact (hBt.inter hτt).union (hσt.diff hBt)

theorem setIntegral_stoppedValue_eq {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {ℱ : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M ℱ μ)
    (hbound : ∀ v : ℝ≥0, ∃ C : ℝ, ∀ t ≤ v, ∀ ω, ‖M t ω‖ ≤ C)
    (hright : ∀ (ω : Ω) (v : ℝ≥0),
      ContinuousWithinAt (fun t : ℝ≥0 => M t ω) (Set.Ici v) v)
    {σ τ : Ω → ℝ≥0} (hσ : IsStoppingTime ℱ fun ω => (σ ω : WithTop ℝ≥0))
    (hτ : IsStoppingTime ℱ fun ω => (τ ω : WithTop ℝ≥0)) (hστ : ∀ ω, σ ω ≤ τ ω)
    {K : ℝ≥0} (hσK : ∀ ω, σ ω ≤ K) (hτK : ∀ ω, τ ω ≤ K)
    (hσint : Integrable (fun ω => M (σ ω) ω) μ) (hτint : Integrable (fun ω => M (τ ω) ω) μ)
    {B : Set Ω} (hB : MeasurableSet[hσ.measurableSpace] B) :
    ∫ ω in B, M (τ ω) ω ∂μ = ∫ ω in B, M (σ ω) ω ∂μ := by
  have hBm : MeasurableSet B := hσ.measurableSpace_le B hB
  have hT := isStoppingTime_piecewise_mem hσ hτ hστ hB
  have hTK : ∀ ω, B.piecewise τ σ ω ≤ K := fun ω => by
    by_cases hx : ω ∈ B <;> simp [Set.piecewise, hx, hσK ω, hτK ω]
  have e1 := MarkovProcess.integral_stoppedValue_eq_of_locallyBounded hM hbound hright hT hTK
  have e2 := MarkovProcess.integral_stoppedValue_eq_of_locallyBounded hM hbound hright hσ hσK
  have hsplit : ∀ ω, M (B.piecewise τ σ ω) ω =
      B.indicator (fun ω => M (τ ω) ω) ω + Bᶜ.indicator (fun ω => M (σ ω) ω) ω := by
    intro ω
    by_cases hx : ω ∈ B <;> simp [Set.piecewise, hx]
  have h1 : ∫ ω, M (B.piecewise τ σ ω) ω ∂μ =
      ∫ ω in B, M (τ ω) ω ∂μ + ∫ ω in Bᶜ, M (σ ω) ω ∂μ := by
    simp only [hsplit]
    rw [integral_add (hτint.indicator hBm) (hσint.indicator hBm.compl),
      integral_indicator hBm, integral_indicator hBm.compl]
  have h2 : ∫ ω in B, M (σ ω) ω ∂μ + ∫ ω in Bᶜ, M (σ ω) ω ∂μ = ∫ ω, M (σ ω) ω ∂μ :=
    integral_add_compl hBm hσint
  linarith [e1, e2, h1, h2]

end EinsteinFull
