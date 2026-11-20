import EinsteinFull.Regeneration.GMPFiniteExit
import EinsteinFull.Regeneration.GMPUniformSlabEscape
import EinsteinFull.Regeneration.ExitBallProbability

/-!
# Bounded-domain exhaustion of GMP slab exits

The source minorization gives almost-sure finite slab exit, so finite exit
probabilities are limits of their bounded-domain counterparts.
-/

open Filter MeasureTheory ProbabilityTheory EinsteinRelation
open EinsteinRelation.Regeneration EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal Topology

namespace EinsteinFull.Regeneration

/-- Every reduced GMP path exits each fixed source-scale slab almost surely. -/
theorem gmp_ae_source_slab_exit_ne_top
    (d : ℕ) (hd : 2 ≤ d) (Λ r l : ℝ) (hl : 1 ≤ l)
    (Q : EnvironmentLaw d Λ r) (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (ω : FieldPair d) (hω : IsRegular (sourceReducedBound Λ) (zeroPotentialReducedPair ω))
    (G : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ)
      (one_le_sourceReducedBound Q.ellipticity_parameter) (zeroPotentialReducedPair ω)
      hω μ hμ.le hμ1) (c x : Vec d) :
    ∀ᵐ γ ∂G.pathLaw x, MarkovProcess.ContinuousPath.exitTime
      (coordinateSlab (Renewal.forceCoord hd) c (l / μ)) γ ≠ ⊤ := by
  obtain ⟨δ, hδ, hδ1, hminor⟩ := uniform_regular_gmp_source_minorization d hd Λ r l hl
  let i := Renewal.forceCoord hd
  let R := l / μ
  let Δ := Renewal.regenDelta μ
  let U := coordinateSlab i c R
  have hR : 0 < R := div_pos (lt_of_lt_of_le zero_lt_one hl) hμ
  have hstep : ∀ y, G.pathLaw y {γ : Path d |
      ∀ t : ℝ≥0, t ≤ Δ → γ t ∈ U} ≤ ENNReal.ofReal (1 - δ) :=
    gmp_slab_survival_le_of_source_minorization G Δ δ R i hδ hδ1.le hR
      (hminor Q μ hμ hμ1 ω hω G) c
  exact gmp_ae_exitTime_ne_top_of_survival_bound G U (isOpen_coordinateSlab i c R) Δ δ hδ hδ1.le hstep x

/-- Source slab exit-event probabilities are limits of bounded-domain exit events. -/
theorem gmp_slab_exit_event_tendsto_ball
    (d : ℕ) (hd : 2 ≤ d) (Λ r l : ℝ) (hl : 1 ≤ l)
    (Q : EnvironmentLaw d Λ r) (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (ω : FieldPair d) (hω : IsRegular (sourceReducedBound Λ) (zeroPotentialReducedPair ω))
    (G : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ)
      (one_le_sourceReducedBound Q.ellipticity_parameter) (zeroPotentialReducedPair ω)
      hω μ hμ.le hμ1) (c x y : Vec d) (B : Set (Vec d)) (hB : MeasurableSet B) :
    Tendsto (fun n : ℕ => G.pathLaw x (finiteExitEvent
      (coordinateSlab (Renewal.forceCoord hd) c (l / μ) ∩ Metric.ball y n) B)) atTop
      (𝓝 (G.pathLaw x (finiteExitEvent (coordinateSlab (Renewal.forceCoord hd) c (l / μ)) B))) := by
  let : IsMarkovKernel G.pathLaw := G.pathLaw_isMarkovKernel
  exact tendsto_finiteExitEvent_ball (Vec d) (G.pathLaw x)
    (coordinateSlab (Renewal.forceCoord hd) c (l / μ)) B
    (isOpen_coordinateSlab _ _ _) hB y
    (gmp_ae_source_slab_exit_ne_top d hd Λ r l hl Q μ hμ hμ1 ω hω G c x)

end EinsteinFull.Regeneration
