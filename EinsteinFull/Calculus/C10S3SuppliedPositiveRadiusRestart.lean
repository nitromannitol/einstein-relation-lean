import EinsteinFull.Calculus.U5RegularStoppingRestart
import EinsteinFull.Calculus.U6BoundedPhysicalResolvent
import EinsteinFull.Calculus.C19S3CleanGuardPrefixStopping

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.SpatialDirichlet

/-- The supplied quenched law restarts at the next finite even passage on the
literal finite failed-guard prefix. -/
theorem c10_realization_positive_radius_guard_prefix_restart
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (r : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd Λ hΛ ω hω lam h0 h1)
    (hfdd : ∀ I : Finset ℝ≥0,
      r.pathLaw.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (R a : ℝ) (hR : 0 < R) (i : Fin d)
    (N : ℕ) (x : Vec d)
    (hprefix : let T : Path d → ℝ≥0∞ := fun γ =>
        Regeneration.passageSequence Δ lam R a γ i (2 * N)
      let hT := coupling_scope_isStoppingTime_passageSequence Δ hΔ lam R a hR i (2 * N)
      MeasurableSet[hT.measurableSpace] {γ | T γ < ⊤ ∧ ∀ k < N,
        Regeneration.passageSequence Δ lam R a γ i (2 * k) ≠ ⊤ ∧
          ¬Regeneration.IsGoodPassage Δ lam R a γ i (2 * k)}) :
    let T : Path d → ℝ≥0∞ := fun γ => Regeneration.passageSequence Δ lam R a γ i (2 * N)
    let E : Set (Path d) := {γ | T γ < ⊤ ∧ ∀ k < N,
      Regeneration.passageSequence Δ lam R a γ i (2 * k) ≠ ⊤ ∧
        ¬Regeneration.IsGoodPassage Δ lam R a γ i (2 * k)}
    ((r.pathLaw x).restrict E).map
        (fun γ => MarkovProcess.ContinuousPath.shift ((T γ).untopD 0) γ) =
      Measure.bind ((r.pathLaw x).restrict E)
        (fun γ => r.pathLaw (γ ((T γ).untopD 0))) := by
  let T : Path d → ℝ≥0∞ := fun γ => Regeneration.passageSequence Δ lam R a γ i (2 * N)
  let E : Set (Path d) := {γ | T γ < ⊤ ∧ ∀ k < N,
    Regeneration.passageSequence Δ lam R a γ i (2 * k) ≠ ⊤ ∧
      ¬Regeneration.IsGoodPassage Δ lam R a γ i (2 * k)}
  let hT := coupling_scope_isStoppingTime_passageSequence Δ hΔ lam R a hR i (2 * N)
  letI : IsMarkovKernel r.pathLaw := r.pathLaw_isMarkovKernel
  have h := u5_regular_signed_extended_stopping_restart hd ω lam Λ hΛ hω r.pathLaw
    hfdd T hT x E hprefix
    (fun γ hγ => hγ.1)
  exact h

/-- The supplied quenched law restarts at the next finite even passage on the
literal finite failed-guard prefix. -/
theorem c10_realization_positive_radius_guard_prefix_restart_proved
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (r : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd Λ hΛ ω hω lam h0 h1)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (R a : ℝ) (hR : 0 < R) (i : Fin d)
    (N : ℕ) (x : Vec d)
 :
    let T : Path d → ℝ≥0∞ := fun γ => Regeneration.passageSequence Δ lam R a γ i (2 * N)
    let E : Set (Path d) := {γ | T γ < ⊤ ∧ ∀ k < N,
      Regeneration.passageSequence Δ lam R a γ i (2 * k) ≠ ⊤ ∧
        ¬Regeneration.IsGoodPassage Δ lam R a γ i (2 * k)}
    ((r.pathLaw x).restrict E).map
        (fun γ => MarkovProcess.ContinuousPath.shift ((T γ).untopD 0) γ) =
      Measure.bind ((r.pathLaw x).restrict E)
        (fun γ => r.pathLaw (γ ((T γ).untopD 0))) := by
  exact c10_realization_positive_radius_guard_prefix_restart hd ω lam Λ hΛ hω h0 h1 r
    (u6_arbitrary_supplied_gmp_canonical_FDD hd ω lam Λ hΛ hω h0 h1 r)
    Δ hΔ R a hR i N x (guard_prefix_stopped_measurable Δ hΔ lam R a hR i N)

/-- The supplied quenched law restarts at the next finite even passage on the
literal finite failed-guard prefix. -/
theorem c10_same_quenched_positive_radius_guard_prefix_restart
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (r : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd Λ hΛ ω hω lam h0 h1)
    (P : QuenchedPathLaws d) (hsame : ∀ x, P (x, ω) = r.pathLaw x)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (R a : ℝ) (hR : 0 < R) (i : Fin d)
    (N : ℕ) (x : Vec d)
 :
    let T : Path d → ℝ≥0∞ := fun γ => Regeneration.passageSequence Δ lam R a γ i (2 * N)
    let E : Set (Path d) := {γ | T γ < ⊤ ∧ ∀ k < N,
      Regeneration.passageSequence Δ lam R a γ i (2 * k) ≠ ⊤ ∧
        ¬Regeneration.IsGoodPassage Δ lam R a γ i (2 * k)}
    ((P (x, ω)).restrict E).map
        (fun γ => MarkovProcess.ContinuousPath.shift ((T γ).untopD 0) γ) =
      Measure.bind ((P (x, ω)).restrict E)
        (fun γ => P (γ ((T γ).untopD 0), ω)) := by
  simpa only [hsame] using
    c10_realization_positive_radius_guard_prefix_restart_proved hd ω lam Λ hΛ hω h0 h1 r
      Δ hΔ R a hR i N x

/-- The supplied quenched law restarts at the next finite even passage on the
literal finite failed-guard prefix. -/
theorem c10_regeneration_guard_prefix_restart
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (h0 : 0 < lam) (h1 : lam ≤ 1)
    (r : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd Λ hΛ ω hω lam h0.le h1)
    (l a : ℝ) (hl : 0 < l)
    (N : ℕ) (x : Vec d)
 :
    let Δ := Regeneration.Renewal.regenDelta lam
    let R := l / lam
    let i := Regeneration.Renewal.forceCoord hd
    let T : Path d → ℝ≥0∞ := fun γ => Regeneration.passageSequence Δ lam R a γ i (2 * N)
    let E : Set (Path d) := {γ | T γ < ⊤ ∧ ∀ k < N,
      Regeneration.passageSequence Δ lam R a γ i (2 * k) ≠ ⊤ ∧
        ¬Regeneration.IsGoodPassage Δ lam R a γ i (2 * k)}
    ((r.pathLaw x).restrict E).map
        (fun γ => MarkovProcess.ContinuousPath.shift ((T γ).untopD 0) γ) =
      Measure.bind ((r.pathLaw x).restrict E)
        (fun γ => r.pathLaw (γ ((T γ).untopD 0))) := by
  exact c10_realization_positive_radius_guard_prefix_restart_proved hd ω lam Λ hΛ hω h0.le h1 r
    (Regeneration.Renewal.regenDelta lam) (EinsteinRelation.regenDelta_pos h0)
    (l / lam) a (div_pos hl h0) (Regeneration.Renewal.forceCoord hd) N x

end EinsteinFull.Blueprint
