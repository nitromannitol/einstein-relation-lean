import EinsteinFull.Regeneration.GeometricTailMoment
import EinsteinFull.Regeneration.GMPScaledSlabExit
import EinsteinFull.Regeneration.GMPExitExhaustion

/-!
# Uniform scaled slab-exit moments

The source-scale slab escape bound gives almost-sure finite exit and a
uniform exponential moment for the force-squared scaled exit time.
-/

open MeasureTheory ProbabilityTheory Set EinsteinRelation
open EinsteinRelation.Regeneration EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- Every open subdomain of a source slab has a uniform scaled exponential exit moment. -/
theorem uniform_regular_gmp_slab_exit_exponential_moment
    (d : ℕ) (hd : 2 ≤ d) (Λ r l : ℝ) (hl : 1 ≤ l) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ (Q : EnvironmentLaw d Λ r) (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
        (ω : FieldPair d)
        (hω : IsRegular (sourceReducedBound Λ) (zeroPotentialReducedPair ω))
        (G : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ)
          (one_le_sourceReducedBound Q.ellipticity_parameter) (zeroPotentialReducedPair ω)
          hω μ hμ.le hμ1) (c x : Vec d) (U : Set (Vec d)),
        IsOpen U → U ⊆ coordinateSlab (Renewal.forceCoord hd) c (l / μ) →
        (∀ᵐ γ ∂G.pathLaw x, MarkovProcess.ContinuousPath.exitTime U γ ≠ ⊤) ∧
        Integrable (fun γ => Real.exp ((δ / 4) * (μ ^ 2 *
          (MarkovProcess.ContinuousPath.exitTime U γ).toReal))) (G.pathLaw x) ∧
        (∫ γ, Real.exp ((δ / 4) * (μ ^ 2 *
          (MarkovProcess.ContinuousPath.exitTime U γ).toReal)) ∂G.pathLaw x) ≤
            Real.exp δ * Real.exp (δ / 4) / (1 - Real.exp (δ / 4 - δ / 2)) := by
  obtain ⟨δ, hδ, hδ1, hgeo⟩ := uniform_regular_gmp_scaled_slab_exit_geometric d hd Λ r l hl
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro Q μ hμ hμ1 ω hω G c x U hU hsub
  let : IsMarkovKernel G.pathLaw := G.pathLaw_isMarkovKernel
  have hfin : ∀ᵐ γ ∂G.pathLaw x, MarkovProcess.ContinuousPath.exitTime U γ ≠ ⊤ := by
    filter_upwards [gmp_ae_source_slab_exit_ne_top d hd Λ r l hl Q μ hμ hμ1 ω hω G c x] with γ hγ
    exact ne_top_of_le_ne_top hγ (MarkovProcess.ContinuousPath.exitTime_mono hsub γ)
  refine ⟨hfin, ?_⟩
  apply exponential_moment_le_of_geometric_tail (G.pathLaw x)
    (fun γ => μ ^ 2 * (MarkovProcess.ContinuousPath.exitTime U γ).toReal)
  · exact measurable_const.mul ((MarkovProcess.ContinuousPath.measurable_exitTime U hU).ennreal_toReal)
  · intro γ
    exact mul_nonneg (sq_nonneg μ) ENNReal.toReal_nonneg
  · exact hδ
  · exact hδ1
  · exact hgeo Q μ hμ hμ1 ω hω G c x U hsub

end EinsteinFull.Regeneration
