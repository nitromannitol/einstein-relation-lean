import EinsteinRelation.Diffusion.Basic
import EinsteinRelation.Probability.ProbabilityPart
import EinsteinRelation.Probability.ReductionLocality
import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Integral.Prod

/-! # The actual environment process and its exponential occupation law

Actual environment process and exponentially averaged occupation law from
`paper/main.tex:220–252,493–500,501–530`.
The canonical environment law here is PHYSICAL. Reduced observations explicitly
compose with `reduce`, which commutes with the actual spatial translation.
No absolute continuity, density, forward equation, occupation bound or weak
resolvent identity is assumed or claimed by this measure construction.
-/

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace EinsteinRelation.EnvironmentProcess

/-- Actual joint annealed environment/path law at starting point zero. -/
def annealedPathLaw {d : ℕ} (Q : Measure (FieldPair d)) (P : QuenchedPathLaws d) :
    Measure (FieldPair d × Path d) :=
  Q.compProd (Probability.probabilityPart (originLaw P))

/-- The physical field pair seen from the path at a finite time. -/
def physicalEnvironmentObservation {d : ℕ} (t : ℝ≥0) (z : FieldPair d × Path d) :
    FieldPair d := translate (z.2 t) z.1

/-- Reduced observations always evaluate both a and mu via the actual reduction. -/
theorem reduce_physicalEnvironmentObservation {d : ℕ} (t : ℝ≥0)
    (z : FieldPair d × Path d) :
    reduce (physicalEnvironmentObservation t z) = translate (z.2 t) (reduce z.1) :=
  reduce_translate z.1 (z.2 t)

theorem measurable_physicalEnvironmentObservation {d : ℕ} (t : ℝ≥0) :
    Measurable (physicalEnvironmentObservation (d := d) t) :=
  Probability.continuous_translate.measurable.comp
    (((continuous_eval_const t).measurable.comp measurable_snd).prodMk measurable_fst)

/-- Literal finite-time environment law, without introducing a density prematurely. -/
def environmentTimeLaw {d : ℕ} (Q : Measure (FieldPair d)) (P : QuenchedPathLaws d)
    (t : ℝ≥0) : Measure (FieldPair d) :=
  (annealedPathLaw Q P).map (physicalEnvironmentObservation t)

/-- Joint time/environment/path observation under the exponential time law. -/
def timedPhysicalObservation {d : ℕ} (p : ℝ × (FieldPair d × Path d)) : FieldPair d :=
  physicalEnvironmentObservation p.1.toNNReal p.2

theorem measurable_timedPhysicalObservation {d : ℕ} :
    Measurable (timedPhysicalObservation (d := d)) := by
  have heval : Measurable (fun p : Path d × ℝ≥0 => p.1 p.2) :=
    (ContinuousEval.continuous_eval (F := Path d) (X := ℝ≥0) (Y := Vec d)).measurable
  exact Probability.continuous_translate.measurable.comp
    ((heval.comp (measurable_snd.snd.prodMk
      (measurable_real_toNNReal.comp measurable_fst))).prodMk measurable_snd.fst)

/-- Actual exponential resolvent occupation measure. For s>0 the existing
expMeasure has density s exp(-s t) on t>=0 and no negative-time mass. -/
def resolventEnvironmentLaw {d : ℕ} (Q : Measure (FieldPair d)) (P : QuenchedPathLaws d)
    (s : ℝ) : Measure (FieldPair d) :=
  ((ProbabilityTheory.expMeasure s).prod (annealedPathLaw Q P)).map timedPhysicalObservation

theorem annealedPathLaw_isProbabilityMeasure {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (P : QuenchedPathLaws d)
    (hP : ∀ᵐ ω ∂Q, IsProbabilityMeasure (P (0, ω))) :
    IsProbabilityMeasure (annealedPathLaw Q P) :=
  Probability.isProbabilityMeasure_compProd_probabilityPart Q (originLaw P) hP

theorem environmentTimeLaw_isProbabilityMeasure {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (P : QuenchedPathLaws d)
    (hP : ∀ᵐ ω ∂Q, IsProbabilityMeasure (P (0, ω))) (t : ℝ≥0) :
    IsProbabilityMeasure (environmentTimeLaw Q P t) := by
  letI := annealedPathLaw_isProbabilityMeasure Q P hP
  unfold environmentTimeLaw
  exact inferInstance

theorem resolventEnvironmentLaw_isProbabilityMeasure {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (P : QuenchedPathLaws d)
    (hP : ∀ᵐ ω ∂Q, IsProbabilityMeasure (P (0, ω))) (s : ℝ) (hs : 0 < s) :
    IsProbabilityMeasure (resolventEnvironmentLaw Q P s) := by
  letI := annealedPathLaw_isProbabilityMeasure Q P hP
  letI := ProbabilityTheory.isProbabilityMeasure_expMeasure hs
  unfold resolventEnvironmentLaw
  exact inferInstance

/-- First genuine quenched/annealed test consumer of the actual process law. -/
theorem integral_environmentTimeLaw {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (P : QuenchedPathLaws d)
    (hP : ∀ᵐ ω ∂Q, IsProbabilityMeasure (P (0, ω))) (t : ℝ≥0)
    (F : FieldPair d → ℝ) (hF : Measurable F) (hb : ∃ C : ℝ, ∀ ω, |F ω| ≤ C) :
    (∫ ω, F ω ∂environmentTimeLaw Q P t) =
      ∫ ω, ∫ γ, F (translate (γ t) ω) ∂P (0, ω) ∂Q := by
  rw [environmentTimeLaw, integral_map
    (measurable_physicalEnvironmentObservation t).aemeasurable hF.aestronglyMeasurable]
  exact Probability.integral_compProd_probabilityPart Q (originLaw P) hP
    (fun z => F (physicalEnvironmentObservation t z))
    (hF.comp (measurable_physicalEnvironmentObservation t))
    (by obtain ⟨C, hC⟩ := hb; exact ⟨C, fun z => hC _⟩)

/-- The exponentially averaged occupation law has its actual time/quenched formula.
This is measure-level Fubini; no density or occupation estimate is supplied. -/
theorem integral_resolventEnvironmentLaw {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (P : QuenchedPathLaws d)
    (hP : ∀ᵐ ω ∂Q, IsProbabilityMeasure (P (0, ω))) (s : ℝ) (hs : 0 < s)
    (F : FieldPair d → ℝ) (hF : Measurable F) (hb : ∃ C : ℝ, ∀ ω, |F ω| ≤ C) :
    (∫ ω, F ω ∂resolventEnvironmentLaw Q P s) =
      ∫ t, ∫ ω, ∫ γ, F (translate (γ t.toNNReal) ω) ∂P (0, ω) ∂Q
        ∂ProbabilityTheory.expMeasure s := by
  letI := annealedPathLaw_isProbabilityMeasure Q P hP
  letI := ProbabilityTheory.isProbabilityMeasure_expMeasure hs
  have hm : Measurable (fun z : ℝ × (FieldPair d × Path d) => F (timedPhysicalObservation z)) :=
    hF.comp measurable_timedPhysicalObservation
  obtain ⟨C, hC⟩ := hb
  have hint : Integrable (fun z : ℝ × (FieldPair d × Path d) => F (timedPhysicalObservation z))
      ((ProbabilityTheory.expMeasure s).prod (annealedPathLaw Q P)) := by
    refine ⟨hm.aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := C) ?_⟩
    exact ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using hC _
  rw [resolventEnvironmentLaw, integral_map measurable_timedPhysicalObservation.aemeasurable
    hF.aestronglyMeasurable, integral_prod _ hint]
  apply integral_congr_ae
  exact ae_of_all _ fun t => Probability.integral_compProd_probabilityPart Q (originLaw P) hP
    (fun z => F (physicalEnvironmentObservation t.toNNReal z))
    (hF.comp (measurable_physicalEnvironmentObservation t.toNNReal))
    ⟨C, fun z => hC _⟩

end EinsteinRelation.EnvironmentProcess
