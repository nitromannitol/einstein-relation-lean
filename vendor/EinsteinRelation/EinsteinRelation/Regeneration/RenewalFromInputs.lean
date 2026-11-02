import EinsteinRelation.Probability.LocalSigma
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Measure.Map

/-!
# Generic steps of the renewal identity (Lemma 3.1)

Source `paper/main.tex` lines 342–426 (`regen.renewal`). Two steps of its proof use neither the
trial construction nor the coupled kernel, only environment σ-algebras and the law of a shifted
record:

* Step 3 (`paper/main.tex` lines 381–411): the expectation of a product of an environment function
  observed on `U` and one observed on `W` factorizes when the two observations are independent.
  This is `integral_mul_eq_of_indep_localSigma`.
* Step 4 (`paper/main.tex` lines 413–425): a law invariant under the regeneration shift is
  preserved along the record sequence, so every later record has that law.
  This is `map_succ_eq_of_shift_invariant`.

The renewal identity itself is not stated or proved in this module.
-/

open MeasureTheory

namespace EinsteinRelation.Regeneration.Renewal

/-- Finite-range factorization (`paper/main.tex` lines 399–403, Step 3). If the observations on
`U` and on `W` are independent under the environment law `Q`, then for functions `A` and `B` of
the environment that are measurable for the local σ-algebras of `U` and `W`, the expectation of
`A * B` is the product of the expectations. -/
theorem integral_mul_eq_of_indep_localSigma {d : ℕ} (Q : Measure (FieldPair d))
    (U W : Set (Vec d))
    (hI : ProbabilityTheory.Indep (EinsteinRelation.localSigma U)
      (EinsteinRelation.localSigma W) Q)
    (A B : FieldPair d → ℝ) (hA : Measurable[EinsteinRelation.localSigma U] A)
    (hB : Measurable[EinsteinRelation.localSigma W] B) :
    (∫ ω, A ω * B ω ∂Q) = (∫ ω, A ω ∂Q) * ∫ ω, B ω ∂Q := by
  have hAm : Measurable A :=
    hA.mono (EinsteinRelation.Probability.localSigma_le_borel U) le_rfl
  have hBm : Measurable B :=
    hB.mono (EinsteinRelation.Probability.localSigma_le_borel W) le_rfl
  have hind : ProbabilityTheory.Indep (MeasurableSpace.comap A inferInstance)
      (MeasurableSpace.comap B inferInstance) Q :=
    ProbabilityTheory.indep_of_indep_of_le_right
      (ProbabilityTheory.indep_of_indep_of_le_left hI hA.comap_le) hB.comap_le
  exact ((ProbabilityTheory.IndepFun_iff_Indep A B Q).mpr hind).integral_fun_mul_eq_mul_integral
    hAm.aestronglyMeasurable hBm.aestronglyMeasurable

/-- Iteration of a shift-invariant law (`paper/main.tex` lines 413–425, Step 4). Let the record
sequence `X j` advance by a measurable shift `Θ` almost everywhere, `X (j + 1) = Θ ∘ X j`. If
the first record has law `ν` and `ν` is invariant under `Θ`, then every later record `X (j + 1)`
has law `ν`. -/
theorem map_succ_eq_of_shift_invariant {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (μ : Measure Ω) (X : ℕ → Ω → α) (Θ : α → α) (hΘ : Measurable Θ)
    (ν : Measure α) (hν : Measure.map Θ ν = ν)
    (hX : ∀ j, AEMeasurable (X j) μ)
    (hshift : ∀ j, X (j + 1) =ᵐ[μ] Θ ∘ X j)
    (h1 : Measure.map (X 1) μ = ν) :
    ∀ j : ℕ, Measure.map (X (j + 1)) μ = ν := by
  intro j
  induction j with
  | zero => exact h1
  | succ j ih =>
    have hΘa : AEMeasurable Θ (Measure.map (X (j + 1)) μ) := hΘ.aemeasurable
    rw [Measure.map_congr (hshift (j + 1)),
      ← AEMeasurable.map_map_of_aemeasurable hΘa (hX (j + 1)), ih, hν]

end EinsteinRelation.Regeneration.Renewal
