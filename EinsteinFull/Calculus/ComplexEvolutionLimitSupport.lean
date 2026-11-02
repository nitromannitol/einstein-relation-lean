import EinsteinFull.Calculus.ComplexYosidaComparisonSupport
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Strong limits of the actual unforced Yosida evolutions

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
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (t : ℝ≥0)
    (f : Lp ℂ 2 (reducedLaw Q)) : Lp ℂ 2 (reducedLaw Q) :=
  limUnder atTop (fun n => unforcedComplexYosidaEvolution Q i n t f)

private theorem tendsto_evolutionLimitValue {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (t : ℝ≥0)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    Tendsto (fun n => unforcedComplexYosidaEvolution Q i n t f) atTop
      (𝓝 (evolutionLimitValue Q i t f)) :=
  (cauchySeq_unforcedComplexYosidaEvolution Q i f t t.property).tendsto_limUnder

private theorem norm_evolutionLimitValue_le {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (t : ℝ≥0)
    (f : Lp ℂ 2 (reducedLaw Q)) : ‖evolutionLimitValue Q i t f‖ ≤ ‖f‖ :=
  le_of_tendsto (tendsto_evolutionLimitValue Q i t f).norm
    (Eventually.of_forall fun n => norm_unforcedComplexYosidaEvolution_apply_le Q i n f t t.property)

/-- The strong limit of the actual unforced Yosida evolutions, bundled on all complex L2. -/
def unforcedComplexEvolution {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (t : ℝ≥0) :
    Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q) :=
  (linearMapOfTendsto (evolutionLimitValue Q i t)
    (fun n => (unforcedComplexYosidaEvolution Q i n t).toLinearMap)
    (tendsto_pi_nhds.mpr (fun f => tendsto_evolutionLimitValue Q i t f))).mkContinuous 1
    (fun f => by simpa only [one_mul] using! norm_evolutionLimitValue_le Q i t f)

/-- The bounded Yosida evolutions converge strongly to the actual limit family. -/
theorem tendsto_unforcedComplexYosidaEvolution {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    Tendsto (fun n => unforcedComplexYosidaEvolution Q i n t f) atTop
      (𝓝 (unforcedComplexEvolution Q i t f)) :=
  tendsto_evolutionLimitValue Q i t f

/-- Each limit evolution is a contraction on the actual complex L2 space. -/
theorem norm_unforcedComplexEvolution_apply_le {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    ‖unforcedComplexEvolution Q i t f‖ ≤ ‖f‖ :=
  norm_evolutionLimitValue_le Q i t f

/-- The limit evolution has operator norm at most one. -/
theorem norm_unforcedComplexEvolution_le {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (t : ℝ≥0) :
    ‖unforcedComplexEvolution Q i t‖ ≤ 1 := by
  apply (unforcedComplexEvolution Q i t).opNorm_le_bound zero_le_one
  intro f
  simpa only [one_mul] using norm_unforcedComplexEvolution_apply_le Q i t f

/-- Strong evolution convergence persists when the initial data converge strongly. -/
theorem tendsto_unforcedComplexYosidaEvolution_apply {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (t : ℝ≥0)
    {u : ℕ → Lp ℂ 2 (reducedLaw Q)} {f : Lp ℂ 2 (reducedLaw Q)}
    (hu : Tendsto u atTop (𝓝 f)) :
    Tendsto (fun n => unforcedComplexYosidaEvolution Q i n t (u n)) atTop
      (𝓝 (unforcedComplexEvolution Q i t f)) := by
  have hz : Tendsto (fun n => unforcedComplexYosidaEvolution Q i n t (u n) -
      unforcedComplexYosidaEvolution Q i n t f) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero (fun n => norm_nonneg _)
      (fun n => ?_) (tendsto_iff_norm_sub_tendsto_zero.mp hu)
    rw [← map_sub]
    exact norm_unforcedComplexYosidaEvolution_apply_le Q i n (u n-f) t t.property
  simpa only [sub_add_cancel, zero_add] using
    hz.add (tendsto_unforcedComplexYosidaEvolution Q i t f)

/-- The actual strong limit starts at the identity. -/
theorem unforcedComplexEvolution_zero {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) :
    unforcedComplexEvolution Q i 0 = ContinuousLinearMap.id ℂ _ := by
  apply ContinuousLinearMap.ext
  intro f
  have h := tendsto_unforcedComplexYosidaEvolution Q i 0 f
  simp only [NNReal.coe_zero, unforcedComplexYosidaEvolution_zero,
    ContinuousLinearMap.id_apply] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

/-- The actual strong limit satisfies the semigroup law. -/
theorem unforcedComplexEvolution_add {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s t : ℝ≥0) :
    unforcedComplexEvolution Q i (s+t) =
      (unforcedComplexEvolution Q i s).comp (unforcedComplexEvolution Q i t) := by
  apply ContinuousLinearMap.ext
  intro f
  have h := tendsto_unforcedComplexYosidaEvolution_apply Q i s
    (tendsto_unforcedComplexYosidaEvolution Q i t f)
  simp only [← ContinuousLinearMap.comp_apply, ← unforcedComplexYosidaEvolution_add] at h
  exact tendsto_nhds_unique (tendsto_unforcedComplexYosidaEvolution Q i (s+t) f) h

/-- On the full actual generator domain the limit inherits the uniform increment bound. -/
theorem IsComplexGeneratorPair.unforced_evolution_sub_le {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexGeneratorPair Q i 0 f g) (t : ℝ≥0) :
    ‖unforcedComplexEvolution Q i t f - f‖ ≤ (t : ℝ) * ‖g‖ :=
  le_of_tendsto ((tendsto_unforcedComplexYosidaEvolution Q i t f).sub_const f).norm
    (Eventually.of_forall fun n => hfg.unforced_yosida_evolution_sub_le n t t.property)

private theorem evolution_sub_evolution_le_of_le {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexGeneratorPair Q i 0 f g) (s t : ℝ≥0) (hst : s ≤ t) :
    ‖unforcedComplexEvolution Q i t f - unforcedComplexEvolution Q i s f‖ ≤
      ((t : ℝ)-(s : ℝ)) * ‖g‖ := by
  have he : unforcedComplexEvolution Q i t f - unforcedComplexEvolution Q i s f =
      unforcedComplexEvolution Q i s (unforcedComplexEvolution Q i (t-s) f-f) := by
    rw [map_sub, ← ContinuousLinearMap.comp_apply, ← unforcedComplexEvolution_add,
      add_tsub_cancel_of_le hst]
  rw [he]
  have h := (norm_unforcedComplexEvolution_apply_le Q i s _).trans
    (hfg.unforced_evolution_sub_le (t-s))
  simpa only [NNReal.coe_sub hst] using h

/-- On the full generator domain the limiting orbit is Lipschitz with its actual output norm. -/
theorem IsComplexGeneratorPair.lipschitzWith_unforcedComplexEvolution
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i 0 f g) :
    LipschitzWith ⟨‖g‖, norm_nonneg g⟩ (fun t => unforcedComplexEvolution Q i t f) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [dist_eq_norm]
  change ‖unforcedComplexEvolution Q i s f - unforcedComplexEvolution Q i t f‖ ≤
    ‖g‖ * |(s : ℝ)-(t : ℝ)|
  rcases le_total s t with hst | hts
  · rw [norm_sub_rev, abs_of_nonpos (sub_nonpos.mpr (show (s : ℝ) ≤ (t : ℝ) from hst)), neg_sub, mul_comm]
    exact evolution_sub_evolution_le_of_le hfg s t hst
  · rw [abs_of_nonneg (sub_nonneg.mpr (show (t : ℝ) ≤ (s : ℝ) from hts)), mul_comm]
    exact evolution_sub_evolution_le_of_le hfg t s hts

/-- The actual limiting contraction family is strongly continuous for every complex L2 datum. -/
theorem continuous_unforcedComplexEvolution_apply {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (f : Lp ℂ 2 (reducedLaw Q)) :
    Continuous (fun t => unforcedComplexEvolution Q i t f) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨u, ⟨g, hug⟩, hfu⟩ :=
    (dense_unforced_complexGenerator_domain Q i).exists_dist_lt f (by positivity : 0 < ε/3)
  obtain ⟨δ, hδ, huδ⟩ := Metric.continuousAt_iff.mp
    hug.lipschitzWith_unforcedComplexEvolution.continuous.continuousAt
      (ε/3) (by positivity)
  refine ⟨δ, hδ, fun s hs => ?_⟩
  have hb (r : ℝ≥0) : dist (unforcedComplexEvolution Q i r f)
      (unforcedComplexEvolution Q i r u) ≤ dist f u := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact norm_unforcedComplexEvolution_apply_le Q i r (f-u)
  calc
    _ ≤ dist (unforcedComplexEvolution Q i s f) (unforcedComplexEvolution Q i s u) +
        (dist (unforcedComplexEvolution Q i s u) (unforcedComplexEvolution Q i t u) +
          dist (unforcedComplexEvolution Q i t u) (unforcedComplexEvolution Q i t f)) := by
      rw [← add_assoc]
      exact dist_triangle4 _ _ _ _
    _ ≤ dist f u +
        (dist (unforcedComplexEvolution Q i s u) (unforcedComplexEvolution Q i t u) +
          dist f u) := add_le_add (hb s) (add_le_add le_rfl (by
            simpa only [dist_comm] using hb t))
    _ < ε := by linarith only [hfu, huδ hs]

end EinsteinFull
