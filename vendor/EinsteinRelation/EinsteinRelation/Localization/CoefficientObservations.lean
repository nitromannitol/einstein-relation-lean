import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Metrizable.ContinuousMap
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import EinsteinRelation.Environment.CoefficientRestriction

/-! # Actual coefficient-only observations

For the open-set coefficient sigma algebra in `paper/main.tex:757–759,876–881`,
compact-open Borel restriction observations agree with the sigma algebra generated
by all reduced-coefficient evaluations. The proof uses countable dense evaluation
and Lusin–Souslin. It identifies Borel sigma algebras, not topologies. Full and
restricted canonical coefficient spaces are standard Borel; no new assumption is
introduced for the conditional-copy construction.
-/

open MeasureTheory
open scoped Uniformity

noncomputable section

namespace EinsteinRelation.Localization

theorem restrictionFunctionSpace_polish {d : ℕ} (U : Set (Vec d)) (hU : IsOpen U) :
    PolishSpace C(U, Mat d) := by
  letI : LocallyCompactSpace U := hU.locallyCompactSpace
  letI : SecondCountableTopology (Mat d) := inferInstanceAs (SecondCountableTopology (Fin d → Fin d → ℝ))
  letI : UniformSpace (Mat d) := inferInstanceAs (UniformSpace (Fin d → Fin d → ℝ))
  letI : CompleteSpace (Mat d) := inferInstanceAs (CompleteSpace (Fin d → Fin d → ℝ))
  haveI : SigmaCompactSpace U := inferInstance
  haveI : CompleteSpace C(U, Mat d) := inferInstance
  letI : Filter.IsCountablyGenerated (𝓤 (Mat d)) :=
    inferInstanceAs (Filter.IsCountablyGenerated (𝓤 (Fin d → Fin d → ℝ)))
  haveI : Filter.IsCountablyGenerated (𝓤 C(U, Mat d)) := inferInstance
  haveI : SecondCountableTopology C(U, Mat d) := inferInstance
  infer_instance

theorem borel_restriction_eq_evaluationSigma {d : ℕ} (U : Set (Vec d)) (hU : IsOpen U) :
    borel C(U, Mat d) =
      ⨆ x : U, MeasurableSpace.comap (fun F : C(U, Mat d) => F x) (borel (Mat d)) := by
  letI : MeasurableSpace C(U, Mat d) := borel C(U, Mat d)
  letI : BorelSpace C(U, Mat d) := ⟨rfl⟩
  letI : PolishSpace C(U, Mat d) := restrictionFunctionSpace_polish U hU
  obtain ⟨D : Set U, hDcount, hDdense⟩ := TopologicalSpace.exists_countable_dense U
  letI : Countable D := hDcount.to_subtype
  let E : C(U, Mat d) → (D → Mat d) := fun F x => F x.1
  have hEcont : Continuous E := continuous_pi fun x => continuous_eval_const x.1
  have hEinj : Function.Injective E := by
    intro F G hFG
    apply ContinuousMap.injective_restrict hDdense
    apply ContinuousMap.ext
    intro x
    exact congrFun hFG x
  letI : SecondCountableTopology (Mat d) := inferInstanceAs (SecondCountableTopology (Fin d → Fin d → ℝ))
  have hEmb : MeasurableEmbedding E := hEcont.measurableEmbedding hEinj
  apply le_antisymm
  · have hle : MeasurableSpace.comap E (inferInstance : MeasurableSpace (D → Mat d)) ≤
        ⨆ x : U, MeasurableSpace.comap (fun F : C(U, Mat d) => F x) (borel (Mat d)) := by
      change MeasurableSpace.comap E
        (⨆ x : D, MeasurableSpace.comap (fun F : D → Mat d => F x) (borel (Mat d))) ≤ _
      rw [MeasurableSpace.comap_iSup]
      apply iSup_le
      intro x
      rw [MeasurableSpace.comap_comp]
      exact le_iSup_of_le x.1 le_rfl
    simpa only [hEmb.comap_eq] using hle
  · apply iSup_le
    intro x
    exact (continuous_eval_const x : Continuous (fun F : C(U, Mat d) => F x)).measurable.comap_le

/-- Continuity of the literal reduced-coefficient observation. -/
theorem continuous_coefficientRestriction {d : ℕ} (U : Set (Vec d)) :
    Continuous (coefficientRestriction U) := by
  change Continuous (fun ω : FieldPair d => (reducedMatrixField ω).restrict U)
  exact (ContinuousMap.continuous_restrict U).comp continuous_reducedMatrixField

/-- The open-domain canonical observation carries exactly the source sigma algebra. -/
theorem coefficientSigma_eq_comap_restriction {d : ℕ} (U : Set (Vec d)) (hU : IsOpen U) :
    coefficientSigma U = MeasurableSpace.comap (coefficientRestriction U) (borel C(U, Mat d)) := by
  rw [borel_restriction_eq_evaluationSigma U hU, MeasurableSpace.comap_iSup]
  unfold coefficientSigma
  apply iSup_congr
  intro x
  rw [MeasurableSpace.comap_comp]
  rfl

/-- The observation is measurable for its actual compact-open Borel target. -/
theorem measurable_coefficientRestriction {d : ℕ} (U : Set (Vec d)) :
    @Measurable (FieldPair d) C(U, Mat d) inferInstance (borel C(U, Mat d))
      (coefficientRestriction U) :=
  (continuous_coefficientRestriction U).borel_measurable

/-- The canonical coefficient space itself is Polish in compact-open topology. -/
theorem coefficientField_polish (d : ℕ) : PolishSpace (CoefficientField d) := by
  letI : SecondCountableTopology (Mat d) :=
    inferInstanceAs (SecondCountableTopology (Fin d → Fin d → ℝ))
  letI : UniformSpace (Mat d) := inferInstanceAs (UniformSpace (Fin d → Fin d → ℝ))
  letI : CompleteSpace (Mat d) := inferInstanceAs (CompleteSpace (Fin d → Fin d → ℝ))
  letI : Filter.IsCountablyGenerated (𝓤 (Mat d)) :=
    inferInstanceAs (Filter.IsCountablyGenerated (𝓤 (Fin d → Fin d → ℝ)))
  infer_instance

theorem coefficientField_standardBorel (d : ℕ) : StandardBorelSpace (CoefficientField d) := by
  letI : PolishSpace (CoefficientField d) := coefficientField_polish d
  infer_instance

theorem coefficientRestriction_standardBorel {d : ℕ} (U : Set (Vec d)) (hU : IsOpen U) :
    @StandardBorelSpace C(U, Mat d) (borel C(U, Mat d)) := by
  letI : MeasurableSpace C(U, Mat d) := borel C(U, Mat d)
  letI : BorelSpace C(U, Mat d) := ⟨rfl⟩
  letI : PolishSpace C(U, Mat d) := restrictionFunctionSpace_polish U hU
  infer_instance

end EinsteinRelation.Localization
