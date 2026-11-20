import EinsteinFull.Regeneration.GMPUniformExitMinorization
import EinsteinFull.Regeneration.KilledSurvivalIteration
import EinsteinFull.Regeneration.CoordinateSlabExit
import EinsteinFull.Blueprint.Foundation.Proofs.SbxS7FiniteTrialSupport

/-!
# One-step slab escape for regular GMP paths

The source endpoint window lies strictly beyond the positive face of any
slab of the same radius containing the starting point. Its minorization
therefore supplies a uniform one-step escape probability.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open EinsteinRelation.Regeneration EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support
open EinsteinFull.External.Source.GMP
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- A source endpoint minorization bounds one-step slab survival. -/
theorem gmp_slab_survival_le_of_source_minorization
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω} {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1}
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)
    (τ : ℝ≥0) (δ R : ℝ) (i : Fin d) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : 0 < R)
    (hminor : HasSourceMinorization (fun x => G.pathLaw x) τ δ R i) (c : Vec d) :
    ∀ x, G.pathLaw x {γ : Path d | ∀ t : ℝ≥0, t ≤ τ → γ t ∈ coordinateSlab i c R} ≤
      ENNReal.ofReal (1 - δ) := by
  intro x
  have : IsMarkovKernel G.pathLaw := G.pathLaw_isMarkovKernel
  by_cases hx : x ∈ coordinateSlab i c R
  · let B := endpointBall i R x
    let E : Set (Path d) := {γ | γ τ ∈ B}
    have hB : MeasurableSet B :=
      (isOpen_lt ((Calculus.Feller.continuous_euclideanNorm d).comp
        (continuous_id.sub continuous_const)) continuous_const).measurableSet
    have hE : MeasurableSet E := hB.preimage (continuous_eval_const τ).measurable
    have hcond : ProbabilityTheory.cond (volume : Measure (Vec d)) B B = 1 :=
      ProbabilityTheory.cond_apply_self (endpointBall_volume_pos i R hR x).ne'
        (endpointBall_volume_ne_top i R hR x)
    have hminor' := hminor x B hB
    rw [hcond, mul_one] at hminor'
    have hsuccess : ENNReal.ofReal δ ≤ G.pathLaw x E := by
      calc
        ENNReal.ofReal δ ≤ ENNReal.ofReal (2 * δ) := ENNReal.ofReal_le_ofReal (by linarith)
        _ ≤ G.pathLaw x {γ | (∀ t : ℝ≥0, t ≤ τ → γ t ∈ couplingRegion i R x) ∧
          γ τ ∈ B} := hminor'
        _ ≤ G.pathLaw x E := measure_mono (fun _ h => h.2)
    have hreal := ENNReal.toReal_mono (measure_ne_top (G.pathLaw x) E) hsuccess
    rw [ENNReal.toReal_ofReal hδ.le] at hreal
    have hwin : δ * (G.pathLaw x).real Set.univ ≤ (G.pathLaw x).real (Set.univ ∩ E) := by
      simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one, Set.univ_inter]
        using hreal
    have hbound := EinsteinFull.Blueprint.ConditionalTrialExhaustion.measure_sdiff_le_of_success_measure
      (G.pathLaw x) Set.univ E hE δ hδ1 hwin
    have hsub : {γ : Path d | ∀ t : ℝ≥0, t ≤ τ → γ t ∈ coordinateSlab i c R} ⊆
        Set.univ \ E := by
      intro γ hγ
      refine ⟨Set.mem_univ _, ?_⟩
      intro he
      have hb := (endpointBall_coordinate_bounds i R x (γ τ) he).1
      have hs := hγ τ le_rfl
      change |γ τ i - c i| < R at hs
      change |x i - c i| < R at hx
      have hs' := (abs_lt.mp hs).2
      have hx' := (abs_lt.mp hx).1
      linarith
    simpa only [measure_univ, mul_one] using (measure_mono hsub).trans hbound
  · have hnull : G.pathLaw x {γ : Path d | γ 0 ≠ x} = 0 := by
      exact ae_iff.mp (G.pathLaw_starts_at x)
    have hzero : G.pathLaw x {γ : Path d |
        ∀ t : ℝ≥0, t ≤ τ → γ t ∈ coordinateSlab i c R} = 0 := by
      apply measure_mono_null _ hnull
      intro γ hγ hstart
      apply hx
      simpa only [hstart] using hγ 0 (zero_le : 0 ≤ τ)
    rw [hzero]
    exact zero_le

end EinsteinFull.Regeneration
