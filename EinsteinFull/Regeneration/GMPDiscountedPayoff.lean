import EinsteinFull.Regeneration.GMPBoundedSlabPayoff
import EinsteinFull.Regeneration.ExitPayoffDiscount

/-!
# Zero-discount limit for GMP slab payoffs

Finite exit from the source slab implies finite exit from each bounded
subdomain. The discounted smooth payoff therefore converges to the actual
bounded-slab payoff without an exit-time moment assumption.
-/

open Filter MeasureTheory ProbabilityTheory Set EinsteinRelation
open EinsteinRelation.Regeneration EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal Topology

namespace EinsteinFull.Regeneration

/-- The discounted bounded-slab payoff converges to the actual payoff. -/
theorem gmp_discounted_slab_payoff_tendsto
    (d : ℕ) (hd : 2 ≤ d) (Λ r l : ℝ) (hl : 1 ≤ l)
    (Q : EnvironmentLaw d Λ r) (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (ω : FieldPair d) (hω : IsRegular (sourceReducedBound Λ) (zeroPotentialReducedPair ω))
    (G : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ)
      (one_le_sourceReducedBound Q.ellipticity_parameter) (zeroPotentialReducedPair ω)
      hω μ hμ.le hμ1) (c y z : Vec d) (N : ℝ)
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (ha0 : Tendsto a atTop (𝓝 0)) :
    let i := Renewal.forceCoord hd
    let U := coordinateSlab i c (l / μ) ∩ Metric.ball y N
    let f := slabSmoothPayoff i c (l / μ)
    Tendsto (fun n : ℕ => ∫ γ,
      {γ | MarkovProcess.ContinuousPath.exitTime U γ < ⊤}.indicator
        (fun γ => Real.exp (-(a n * (MarkovProcess.ContinuousPath.exitTime U γ).toReal)) *
          f (γ ((MarkovProcess.ContinuousPath.exitTimeTop U γ).untopD 0))) γ ∂G.pathLaw z) atTop
      (𝓝 (gmpBoundedSlabPayoff G i c (l / μ) y N z)) := by
  dsimp only
  let : IsMarkovKernel G.pathLaw := G.pathLaw_isMarkovKernel
  let i := Renewal.forceCoord hd
  let U := coordinateSlab i c (l / μ) ∩ Metric.ball y N
  let f := slabSmoothPayoff i c (l / μ)
  have hfin : ∀ᵐ γ ∂G.pathLaw z, MarkovProcess.ContinuousPath.exitTime U γ < ⊤ := by
    filter_upwards [gmp_ae_source_slab_exit_ne_top d hd Λ r l hl Q μ hμ hμ1 ω hω G c z] with γ hγ
    exact lt_top_iff_ne_top.mpr (ne_top_of_le_ne_top hγ
      (MarkovProcess.ContinuousPath.exitTime_mono inter_subset_left γ))
  have h := tendsto_discounted_exitPayoff (G.pathLaw z) U
    ((isOpen_coordinateSlab i c (l / μ)).inter Metric.isOpen_ball) f
    (slabSmoothPayoff_smooth i c (l / μ)).continuous.measurable
    (fun x => (slabSmoothPayoff_mem_Icc i c (l / μ) x).1)
    (fun x => (slabSmoothPayoff_mem_Icc i c (l / μ) x).2) a ha ha0
  have heq : (∫ γ, {γ | MarkovProcess.ContinuousPath.exitTime U γ < ⊤}.indicator
        (fun γ => f (γ ((MarkovProcess.ContinuousPath.exitTimeTop U γ).untopD 0))) γ ∂G.pathLaw z) =
      gmpBoundedSlabPayoff G i c (l / μ) y N z := by
    apply integral_congr_ae
    filter_upwards [hfin] with γ hγ
    have hm : γ ∈ {γ | MarkovProcess.ContinuousPath.exitTime U γ < ⊤} := hγ
    rw [Set.indicator_of_mem hm]
  rwa [heq] at h

end EinsteinFull.Regeneration
