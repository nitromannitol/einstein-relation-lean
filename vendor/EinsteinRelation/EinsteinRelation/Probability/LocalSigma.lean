import EinsteinRelation.Environment.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Local environment observables

The joint restriction σ-algebra is the one from `regen.future`,
`paper/main.tex:331–340`. These lemmas only transport locality; the
regeneration factorization and occupation estimates remain separate obligations.
-/

namespace EinsteinRelation.Probability

/-- Enlarging the observed set enlarges its joint restriction σ-algebra. -/
theorem localSigma_mono {d : ℕ} {U W : Set (Vec d)} (hUW : U ⊆ W) :
    localSigma U ≤ localSigma W := by
  unfold localSigma
  apply iSup_le
  intro x
  exact le_iSup_of_le ⟨x.1, hUW x.2⟩ le_rfl

/-- Joint field restrictions are measurable for the canonical Borel law. -/
theorem localSigma_le_borel {d : ℕ} (U : Set (Vec d)) :
    localSigma U ≤ (inferInstance : MeasurableSpace (FieldPair d)) := by
  unfold localSigma
  apply iSup_le
  intro x
  have ha : Continuous (fun ω : FieldPair d => ω.1 x) :=
    (continuous_eval_const (x : Vec d)).comp continuous_fst
  have hμ : Continuous (fun ω : FieldPair d => ω.2 x) :=
    (continuous_eval_const (x : Vec d)).comp continuous_snd
  exact (ha.prodMk hμ).measurable.comap_le

/-- A translated local observable sees the translated observation set. -/
theorem localSigma_translate_comap_le {d : ℕ} (x : Vec d) (U : Set (Vec d)) :
    (localSigma U).comap (translate x) ≤ localSigma ((fun y => x + y) '' U) := by
  unfold localSigma
  rw [MeasurableSpace.comap_iSup]
  apply iSup_le
  intro y
  rw [MeasurableSpace.comap_comp]
  exact le_iSup_of_le ⟨x + y.1, ⟨y.1, y.2, rfl⟩⟩ le_rfl

/-- Joint continuity for the compact-open topology on coefficient pairs. -/
theorem continuous_translate {d : ℕ} :
    Continuous (fun p : Vec d × FieldPair d => translate p.1 p.2) := by
  apply Continuous.prodMk
  · apply ContinuousMap.continuous_of_continuous_uncurry
    exact (continuous_fst.snd.fst).eval (continuous_fst.fst.add continuous_snd)
  · apply ContinuousMap.continuous_of_continuous_uncurry
    exact (continuous_fst.snd.snd).eval (continuous_fst.fst.add continuous_snd)

/-- Fixed translations are measurable for the canonical coefficient law. -/
theorem measurable_translate {d : ℕ} (x : Vec d) : Measurable (translate x) :=
  (continuous_translate.comp (continuous_const.prodMk continuous_id)).measurable

/-- Restriction locality is preserved when evaluating a translated observable. -/
theorem measurable_translate_local {d : ℕ} (x : Vec d) (U : Set (Vec d)) :
    @Measurable (FieldPair d) (FieldPair d)
      (localSigma ((fun y => x + y) '' U)) (localSigma U) (translate x) :=
  Measurable.of_comap_le (localSigma_translate_comap_le x U)

/-- Stationarity gives the expected integral identity for translated observables. -/
theorem integral_translate {d : ℕ} (Q : MeasureTheory.Measure (FieldPair d))
    (hQ : IsStationary Q) (x : Vec d) (f : FieldPair d → ℝ) (hf : Measurable f) :
    (∫ ω, f (translate x ω) ∂Q) = ∫ ω, f ω ∂Q := by
  have h := MeasureTheory.integral_map (μ := Q) (measurable_translate x).aemeasurable
    hf.stronglyMeasurable.aestronglyMeasurable
  rw [hQ x] at h
  exact h.symm

end EinsteinRelation.Probability
