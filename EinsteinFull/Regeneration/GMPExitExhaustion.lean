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

/-- Bounded-domain exit probabilities converge to the literal positive slab-exit probability. -/
theorem gmp_positive_slab_exit_tendsto_ball
    (d : ℕ) (hd : 2 ≤ d) (Λ r l : ℝ) (hl : 1 ≤ l)
    (Q : EnvironmentLaw d Λ r) (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (ω : FieldPair d) (hω : IsRegular (sourceReducedBound Λ) (zeroPotentialReducedPair ω))
    (G : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ)
      (one_le_sourceReducedBound Q.ellipticity_parameter) (zeroPotentialReducedPair ω)
      hω μ hμ.le hμ1) (x y : Vec d) :
    let i := Renewal.forceCoord hd
    let B : Set (Vec d) := {z | z i - x i = l / μ}
    Tendsto (fun n : ℕ => G.pathLaw x (finiteExitEvent
      (coordinateSlab i x (l / μ) ∩ Metric.ball y n) B)) atTop
      (𝓝 (G.pathLaw x {γ | coordinateSlabExit γ i (l / μ) ≠ ⊤ ∧
        γ (coordinateSlabExit γ i (l / μ)).toNNReal i - γ 0 i = l / μ})) := by
  dsimp only
  let i := Renewal.forceCoord hd
  let B : Set (Vec d) := {z | z i - x i = l / μ}
  have hB : MeasurableSet B :=
    (isClosed_eq ((continuous_apply i).sub continuous_const) continuous_const).measurableSet
  have hlim := gmp_slab_exit_event_tendsto_ball d hd Λ r l hl Q μ hμ hμ1 ω hω G x x y B hB
  have hae : finiteExitEvent (coordinateSlab i x (l / μ)) B =ᵐ[G.pathLaw x]
      {γ | coordinateSlabExit γ i (l / μ) ≠ ⊤ ∧
        γ (coordinateSlabExit γ i (l / μ)).toNNReal i - γ 0 i = l / μ} := by
    filter_upwards [G.pathLaw_starts_at x] with γ hstart
    change γ 0 = x at hstart
    have heq : coordinateSlabExit γ i (l / μ) =
        MarkovProcess.ContinuousPath.exitTime (coordinateSlab i x (l / μ)) γ := by
      simp only [coordinateSlabExit, hstart]
    by_cases hfin : MarkovProcess.ContinuousPath.exitTime (coordinateSlab i x (l / μ)) γ = ⊤
    · simp [finiteExitEvent, heq, hfin]
    · have htime := MarkovProcess.ContinuousPath.untopD_exitTimeTop_eq_toNNReal
        (coordinateSlab i x (l / μ)) γ hfin
      simp only [finiteExitEvent, Set.mem_ofPred_eq, lt_top_iff_ne_top, htime,
        heq, B, hstart]
  have hevent := measure_congr hae
  rw [hevent] at hlim
  exact hlim

/-- Eventual bounded-domain lower bounds pass to the positive slab-exit probability. -/
theorem gmp_positive_slab_exit_le_of_ball_bounds
    (d : ℕ) (hd : 2 ≤ d) (Λ r l : ℝ) (hl : 1 ≤ l)
    (Q : EnvironmentLaw d Λ r) (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (ω : FieldPair d) (hω : IsRegular (sourceReducedBound Λ) (zeroPotentialReducedPair ω))
    (G : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ)
      (one_le_sourceReducedBound Q.ellipticity_parameter) (zeroPotentialReducedPair ω)
      hω μ hμ.le hμ1) (x y : Vec d) (a : ℝ)
    (hbound : ∀ᶠ n : ℕ in atTop, a ≤ (G.pathLaw x).real (finiteExitEvent
      (coordinateSlab (Renewal.forceCoord hd) x (l / μ) ∩ Metric.ball y n)
      {z | z (Renewal.forceCoord hd) - x (Renewal.forceCoord hd) = l / μ})) :
    a ≤ (G.pathLaw x).real {γ | coordinateSlabExit γ (Renewal.forceCoord hd) (l / μ) ≠ ⊤ ∧
      γ (coordinateSlabExit γ (Renewal.forceCoord hd) (l / μ)).toNNReal
        (Renewal.forceCoord hd) - γ 0 (Renewal.forceCoord hd) = l / μ} := by
  let : IsMarkovKernel G.pathLaw := G.pathLaw_isMarkovKernel
  have hlim := gmp_positive_slab_exit_tendsto_ball d hd Λ r l hl Q μ hμ hμ1 ω hω G x y
  have hreal := (ENNReal.tendsto_toReal (measure_ne_top (G.pathLaw x) _)).comp hlim
  exact ge_of_tendsto hreal hbound

end EinsteinFull.Regeneration
