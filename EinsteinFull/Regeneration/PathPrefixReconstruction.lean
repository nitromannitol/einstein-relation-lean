import EinsteinFull.Work.W1.GMPFullPastRestartSupport
import EinsteinRelation.Diffusion.TimeChangeCovariance

/-!
# Reconstructing continuous path laws from their grid prefixes

Clamped increments join two actual continuous paths without imposing a
compatibility premise. For a path and its shifted future this recovers the
longer stopped path exactly. Equality of all grid-prefix laws determines the
whole continuous-path law. The final joint-law identity is proved for the
actual GMP realization from its already proved complete-past restart law.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinFull.Regeneration
open EinsteinRelation EinsteinRelation.External.GantertSection7Support

/-- Append one clamped path increment to a complete stopped prefix. -/
def extendPathPrefix {d : ℕ} (s Δ : ℝ≥0) (q : Path d × Path d) : Path d :=
  ⟨fun t => q.1 (min t s) + (q.2 (min Δ (t - s)) - q.2 0),
    (q.1.continuous.comp (continuous_id.min continuous_const)).add
      ((q.2.continuous.comp (continuous_const.min
        (continuous_id.sub continuous_const))).sub continuous_const)⟩

/-- The actual clamped-increment extension is jointly measurable in both paths. -/
theorem measurable_extendPathPrefix {d : ℕ} (s Δ : ℝ≥0) :
    Measurable (extendPathPrefix (d := d) s Δ) := by
  apply TimeChangeCovariance.measurable_path_of_forall_eval
  intro t
  exact ((measurable_pathPosition (min t s)).comp measurable_fst).add
    (((measurable_pathPosition (min Δ (t - s))).comp measurable_snd).sub
      ((measurable_pathPosition 0).comp measurable_snd))

/-- A path's true prefix and true shifted future recover its longer prefix. -/
theorem extendPathPrefix_prefix_shift {d : ℕ} (s Δ : ℝ≥0) (γ : Path d) :
    extendPathPrefix s Δ (gmpPrefixPath s γ, gmpShiftPath s γ) =
      gmpPrefixPath (s + Δ) γ := by
  apply ContinuousMap.ext
  intro t
  change γ (min (min t s) s) + (γ (s + min Δ (t - s)) - γ (s + 0)) =
    γ (min t (s + Δ))
  rw [min_assoc, min_self, add_zero]
  by_cases ht : t ≤ s
  · rw [min_eq_left ht, tsub_eq_zero_of_le ht, min_eq_right (zero_le (a := Δ)),
      add_zero, min_eq_left (ht.trans (le_add_of_nonneg_right Δ.2)), sub_self, add_zero]
  · have hst : s ≤ t := le_of_not_ge ht
    rw [min_eq_right hst]
    have he : s + min Δ (t - s) = min t (s + Δ) := by
      rw [add_min, add_tsub_cancel_of_le hst, min_comm]
    rw [he]
    abel

/-- Finite continuous-path measures are determined by their complete prefixes
at all positive integer multiples of one fixed positive grid spacing. -/
theorem pathMeasure_eq_of_grid_prefix {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (μ ν : Measure (Path d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ n : ℕ, μ.map (gmpPrefixPath ((n + 1 : ℕ) * Δ)) =
      ν.map (gmpPrefixPath ((n + 1 : ℕ) * Δ))) : μ = ν := by
  apply pathMeasure_eq_of_ordered_cylinder_integrals
  intro inc F hF _
  let ts := cumulativeTimes inc
  let n : ℕ := ⌈ts.sum / Δ⌉₊
  have hbound : ts.sum ≤ (n + 1 : ℕ) * Δ := by
    have hn : ts.sum ≤ n * Δ := (div_le_iff₀ hΔ).mp (Nat.le_ceil (ts.sum / Δ))
    exact hn.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.le_succ n)) Δ.2)
  have he (γ : Path d) :
      pathPositionsAtTimes ts (gmpPrefixPath ((n + 1 : ℕ) * Δ) γ) =
        pathPositionsAtTimes ts γ := by
    apply List.map_congr_left
    intro t ht
    exact congrArg γ (min_eq_left ((List.single_le_sum (fun _ _ => zero_le) t ht).trans hbound))
  have hi := congrArg (fun m : Measure (Path d) =>
    ∫ γ, F (pathPositionsAtTimes ts γ) ∂m) (h n)
  have hm : Measurable (fun γ : Path d => F (pathPositionsAtTimes ts γ)) :=
    hF.comp (measurable_pathPositionsAtTimes ts)
  rw [integral_map (measurable_gmpPrefixPath _).aemeasurable hm.aestronglyMeasurable,
    integral_map (measurable_gmpPrefixPath _).aemeasurable hm.aestronglyMeasurable] at hi
  simpa only [he] using hi

/-- The true future process starts from the endpoint of the displayed prefix. -/
def pathPrefixContinuation {d : ℕ} (P : Kernel (Vec d) (Path d)) (s : ℝ≥0) :
    Kernel (Path d) (Path d) :=
  P.comap (pathPosition s) (measurable_pathPosition s)

instance isMarkovKernel_pathPrefixContinuation {d : ℕ}
    (P : Kernel (Vec d) (Path d)) [IsMarkovKernel P] (s : ℝ≥0) :
    IsMarkovKernel (pathPrefixContinuation P s) := by
  unfold pathPrefixContinuation
  infer_instance

/-- The actual GMP prefix and complete future have their endpoint-conditioned
joint law, at every deterministic time and every spatial starting point. -/
theorem gmpPathLaw_prefix_future_joint {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω} {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1}
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)
    (s : ℝ≥0) (x : Vec d) :
    (G.pathLaw x).map (fun γ => (gmpPrefixPath s γ, gmpShiftPath s γ)) =
      ((G.pathLaw x).map (gmpPrefixPath s)).compProd
        (pathPrefixContinuation G.pathLaw s) := by
  letI := G.pathLaw_isMarkovKernel
  apply Measure.ext_prod
  intro A B hA hB
  have h := congrArg (fun μ : Measure (Path d) => μ A)
    (gmpPathLaw_prefix_future G s B hB x)
  rw [Measure.map_apply (measurable_gmpPrefixPath _) hA,
    Measure.map_apply (measurable_gmpPrefixPath _) hA,
    Measure.restrict_apply (hA.preimage (measurable_gmpPrefixPath _)),
    withDensity_apply _ (hA.preimage (measurable_gmpPrefixPath _))] at h
  rw [Measure.map_apply ((measurable_gmpPrefixPath _).prodMk (measurable_gmpShiftPath _))
      (hA.prod hB), Measure.compProd_apply_prod hA hB]
  change _ = ∫⁻ γ in A, G.pathLaw (γ s) B ∂(G.pathLaw x).map (gmpPrefixPath s)
  have hm : Measurable (fun γ : Path d => G.pathLaw (γ s) B) :=
    (G.pathLaw.measurable_coe hB).comp (measurable_pathPosition s)
  rw [setLIntegral_map hA hm (measurable_gmpPrefixPath s)]
  change (G.pathLaw x) ((gmpPrefixPath s) ⁻¹' A ∩ (gmpShiftPath s) ⁻¹' B) =
    ∫⁻ γ in (gmpPrefixPath s) ⁻¹' A, G.pathLaw ((gmpPrefixPath s γ) s) B ∂G.pathLaw x
  simpa only [gmpPrefixPath, ContinuousMap.coe_mk, min_self] using h

end EinsteinFull.Regeneration
