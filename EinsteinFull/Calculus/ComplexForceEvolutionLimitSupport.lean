import EinsteinFull.Calculus.ComplexForceYosidaComparisonSupport
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Strong limits of the actual shifted forced Yosida evolutions

The Cauchy evolutions define bounded complex linear maps on the whole actual
L2 space. Contractivity permits passage to compositions with varying data.
The resulting nonnegative-time family satisfies the semigroup laws.
-/

open MeasureTheory Filter
open scoped Topology NNReal

noncomputable section
namespace EinsteinFull
open EinsteinRelation

private def evolutionLimitValue {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (t : ℝ≥0)
    (f : Lp ℂ 2 (reducedLaw Q)) : Lp ℂ 2 (reducedLaw Q) :=
  limUnder atTop (fun n => forcedComplexYosidaEvolution Q i ζ n t f)

private theorem tendsto_evolutionLimitValue {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (t : ℝ≥0)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    Tendsto (fun n => forcedComplexYosidaEvolution Q i ζ n t f) atTop
      (𝓝 (evolutionLimitValue Q i ζ t f)) :=
  (cauchySeq_forcedComplexYosidaEvolution Q i ζ f t t.property).tendsto_limUnder

private theorem norm_evolutionLimitValue_le {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (t : ℝ≥0)
    (f : Lp ℂ 2 (reducedLaw Q)) : ‖evolutionLimitValue Q i ζ t f‖ ≤ ‖f‖ :=
  le_of_tendsto (tendsto_evolutionLimitValue Q i ζ t f).norm
    (Eventually.of_forall fun n => norm_forcedComplexYosidaEvolution_apply_le Q i ζ n f t t.property)

/-- The strong limit of the actual shifted forced Yosida evolutions, bundled on all complex L2. -/
def shiftedForcedComplexEvolution {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (t : ℝ≥0) :
    Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q) :=
  (linearMapOfTendsto (evolutionLimitValue Q i ζ t)
    (fun n => (forcedComplexYosidaEvolution Q i ζ n t).toLinearMap)
    (tendsto_pi_nhds.mpr (fun f => tendsto_evolutionLimitValue Q i ζ t f))).mkContinuous 1
    (fun f => by simpa only [one_mul] using! norm_evolutionLimitValue_le Q i ζ t f)

/-- The bounded Yosida evolutions converge strongly to the actual limit family. -/
theorem tendsto_forcedComplexYosidaEvolution {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    Tendsto (fun n => forcedComplexYosidaEvolution Q i ζ n t f) atTop
      (𝓝 (shiftedForcedComplexEvolution Q i ζ t f)) :=
  tendsto_evolutionLimitValue Q i ζ t f

/-- Each limit evolution is a contraction on the actual complex L2 space. -/
theorem norm_shiftedForcedComplexEvolution_apply_le {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    ‖shiftedForcedComplexEvolution Q i ζ t f‖ ≤ ‖f‖ :=
  norm_evolutionLimitValue_le Q i ζ t f

/-- The limit evolution has operator norm at most one. -/
theorem norm_shiftedForcedComplexEvolution_le {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (t : ℝ≥0) :
    ‖shiftedForcedComplexEvolution Q i ζ t‖ ≤ 1 := by
  apply (shiftedForcedComplexEvolution Q i ζ t).opNorm_le_bound zero_le_one
  intro f
  simpa only [one_mul] using norm_shiftedForcedComplexEvolution_apply_le Q i ζ t f

/-- Strong evolution convergence persists when the initial data converge strongly. -/
theorem tendsto_forcedComplexYosidaEvolution_apply {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (t : ℝ≥0)
    {u : ℕ → Lp ℂ 2 (reducedLaw Q)} {f : Lp ℂ 2 (reducedLaw Q)}
    (hu : Tendsto u atTop (𝓝 f)) :
    Tendsto (fun n => forcedComplexYosidaEvolution Q i ζ n t (u n)) atTop
      (𝓝 (shiftedForcedComplexEvolution Q i ζ t f)) := by
  have hz : Tendsto (fun n => forcedComplexYosidaEvolution Q i ζ n t (u n) -
      forcedComplexYosidaEvolution Q i ζ n t f) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero (fun n => norm_nonneg _)
      (fun n => ?_) (tendsto_iff_norm_sub_tendsto_zero.mp hu)
    rw [← map_sub]
    exact norm_forcedComplexYosidaEvolution_apply_le Q i ζ n (u n-f) t t.property
  simpa only [sub_add_cancel, zero_add] using
    hz.add (tendsto_forcedComplexYosidaEvolution Q i ζ t f)

/-- The actual strong limit starts at the identity. -/
theorem shiftedForcedComplexEvolution_zero {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) :
    shiftedForcedComplexEvolution Q i ζ 0 = ContinuousLinearMap.id ℂ _ := by
  apply ContinuousLinearMap.ext
  intro f
  have h := tendsto_forcedComplexYosidaEvolution Q i ζ 0 f
  simp only [NNReal.coe_zero, forcedComplexYosidaEvolution_zero,
    ContinuousLinearMap.id_apply] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

/-- The actual strong limit satisfies the semigroup law. -/
theorem shiftedForcedComplexEvolution_add {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (s t : ℝ≥0) :
    shiftedForcedComplexEvolution Q i ζ (s+t) =
      (shiftedForcedComplexEvolution Q i ζ s).comp (shiftedForcedComplexEvolution Q i ζ t) := by
  apply ContinuousLinearMap.ext
  intro f
  have h := tendsto_forcedComplexYosidaEvolution_apply Q i ζ s
    (tendsto_forcedComplexYosidaEvolution Q i ζ t f)
  simp only [← ContinuousLinearMap.comp_apply, ← forcedComplexYosidaEvolution_add] at h
  exact tendsto_nhds_unique (tendsto_forcedComplexYosidaEvolution Q i ζ (s+t) f) h

/-- On the full actual generator domain the limit inherits the uniform increment bound. -/
theorem IsComplexGeneratorPair.shifted_forced_evolution_sub_le {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ} {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexGeneratorPair Q i ζ f g) (t : ℝ≥0) :
    ‖shiftedForcedComplexEvolution Q i ζ t f - f‖ ≤ (t : ℝ) * ‖g - (complexForceShift d Λ₀ ζ : ℂ) • f‖ :=
  le_of_tendsto ((tendsto_forcedComplexYosidaEvolution Q i ζ t f).sub_const f).norm
    (Eventually.of_forall fun n => hfg.forced_yosida_evolution_sub_le n t t.property)

private theorem evolution_sub_evolution_le_of_le {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ} {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexGeneratorPair Q i ζ f g) (s t : ℝ≥0) (hst : s ≤ t) :
    ‖shiftedForcedComplexEvolution Q i ζ t f - shiftedForcedComplexEvolution Q i ζ s f‖ ≤
      ((t : ℝ)-(s : ℝ)) * ‖g - (complexForceShift d Λ₀ ζ : ℂ) • f‖ := by
  have he : shiftedForcedComplexEvolution Q i ζ t f - shiftedForcedComplexEvolution Q i ζ s f =
      shiftedForcedComplexEvolution Q i ζ s (shiftedForcedComplexEvolution Q i ζ (t-s) f-f) := by
    rw [map_sub, ← ContinuousLinearMap.comp_apply, ← shiftedForcedComplexEvolution_add,
      add_tsub_cancel_of_le hst]
  rw [he]
  have h := (norm_shiftedForcedComplexEvolution_apply_le Q i ζ s _).trans
    (hfg.shifted_forced_evolution_sub_le (t-s))
  simpa only [NNReal.coe_sub hst] using h

/-- On the full generator domain the limiting orbit is Lipschitz with its actual shifted output norm. -/
theorem IsComplexGeneratorPair.lipschitzWith_shiftedForcedComplexEvolution
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g) :
    LipschitzWith ⟨‖g - (complexForceShift d Λ₀ ζ : ℂ) • f‖,
      norm_nonneg _⟩ (fun t => shiftedForcedComplexEvolution Q i ζ t f) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [dist_eq_norm]
  change ‖shiftedForcedComplexEvolution Q i ζ s f - shiftedForcedComplexEvolution Q i ζ t f‖ ≤
    ‖g - (complexForceShift d Λ₀ ζ : ℂ) • f‖ * |(s : ℝ)-(t : ℝ)|
  rcases le_total s t with hst | hts
  · rw [norm_sub_rev, abs_of_nonpos (sub_nonpos.mpr (show (s : ℝ) ≤ (t : ℝ) from hst)), neg_sub, mul_comm]
    exact evolution_sub_evolution_le_of_le hfg s t hst
  · rw [abs_of_nonneg (sub_nonneg.mpr (show (t : ℝ) ≤ (s : ℝ) from hts)), mul_comm]
    exact evolution_sub_evolution_le_of_le hfg t s hts

/-- The actual limiting contraction family is strongly continuous for every complex L2 datum. -/
theorem continuous_shiftedForcedComplexEvolution_apply {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (f : Lp ℂ 2 (reducedLaw Q)) :
    Continuous (fun t => shiftedForcedComplexEvolution Q i ζ t f) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨u, ⟨g, hug⟩, hfu⟩ :=
    (dense_complexGenerator_domain Q i ζ).exists_dist_lt f (by positivity : 0 < ε/3)
  obtain ⟨δ, hδ, huδ⟩ := Metric.continuousAt_iff.mp
    hug.lipschitzWith_shiftedForcedComplexEvolution.continuous.continuousAt
      (ε/3) (by positivity)
  refine ⟨δ, hδ, fun s hs => ?_⟩
  have hb (r : ℝ≥0) : dist (shiftedForcedComplexEvolution Q i ζ r f)
      (shiftedForcedComplexEvolution Q i ζ r u) ≤ dist f u := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact norm_shiftedForcedComplexEvolution_apply_le Q i ζ r (f-u)
  calc
    _ ≤ dist (shiftedForcedComplexEvolution Q i ζ s f) (shiftedForcedComplexEvolution Q i ζ s u) +
        (dist (shiftedForcedComplexEvolution Q i ζ s u) (shiftedForcedComplexEvolution Q i ζ t u) +
          dist (shiftedForcedComplexEvolution Q i ζ t u) (shiftedForcedComplexEvolution Q i ζ t f)) := by
      rw [← add_assoc]
      exact dist_triangle4 _ _ _ _
    _ ≤ dist f u +
        (dist (shiftedForcedComplexEvolution Q i ζ s u) (shiftedForcedComplexEvolution Q i ζ t u) +
          dist f u) := add_le_add (hb s) (add_le_add le_rfl (by
            simpa only [dist_comm] using hb t))
    _ < ε := by linarith only [hfu, huδ hs]

end EinsteinFull
