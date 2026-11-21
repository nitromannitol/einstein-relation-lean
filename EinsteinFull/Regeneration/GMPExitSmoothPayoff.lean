import EinsteinFull.Regeneration.GMPExitExhaustion
import EinsteinFull.Regeneration.SlabSmoothPayoff

/-!
# Smooth payoff approximation of the positive slab exit

Bounded-domain exit expectations of the smooth force-face payoff converge
to the positive slab-exit probability for the supplied reduced diffusion.
-/

open Filter MeasureTheory ProbabilityTheory EinsteinRelation
open EinsteinRelation.Regeneration EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal Topology

namespace EinsteinFull.Regeneration

/-- The smooth slab payoff recovers the positive-exit probability in the limit. -/
theorem gmp_positive_slab_exit_tendsto_smooth_payoff
    (d : ℕ) (hd : 2 ≤ d) (Λ r l : ℝ) (hl : 1 ≤ l)
    (Q : EnvironmentLaw d Λ r) (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (ω : FieldPair d) (hω : IsRegular (sourceReducedBound Λ) (zeroPotentialReducedPair ω))
    (G : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ)
      (one_le_sourceReducedBound Q.ellipticity_parameter) (zeroPotentialReducedPair ω)
      hω μ hμ.le hμ1) (x y : Vec d) :
    let i := Renewal.forceCoord hd
    let f := slabSmoothPayoff i x (l / μ)
    Tendsto (fun n : ℕ => ∫ γ, f (γ ((MarkovProcess.ContinuousPath.exitTimeTop
      (coordinateSlab i x (l / μ) ∩ Metric.ball y n) γ).untopD 0)) ∂G.pathLaw x) atTop
      (𝓝 ((G.pathLaw x).real {γ | coordinateSlabExit γ i (l / μ) ≠ ⊤ ∧
        γ (coordinateSlabExit γ i (l / μ)).toNNReal i - γ 0 i = l / μ})) := by
  dsimp only
  let i := Renewal.forceCoord hd
  let R := l / μ
  have hR : 0 < R := div_pos (lt_of_lt_of_le zero_lt_one hl) hμ
  apply gmp_positive_slab_exit_tendsto_payoff d hd Λ r l hl Q μ hμ hμ1 ω hω G x y
    (slabSmoothPayoff i x R) (slabSmoothPayoff_smooth i x R).continuous.measurable 1
  · intro z
    have hz := slabSmoothPayoff_mem_Icc i x R z
    rw [Real.norm_eq_abs, abs_of_nonneg hz.1]
    exact hz.2
  · exact slabSmoothPayoff_lower i x R
  · exact slabSmoothPayoff_upper i x R hR

end EinsteinFull.Regeneration
