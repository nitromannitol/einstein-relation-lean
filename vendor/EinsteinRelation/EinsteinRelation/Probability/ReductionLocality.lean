import EinsteinRelation.Environment.Reduction
import EinsteinRelation.Probability.LocalSigma

/-! # Locality of the physical-to-reduced environment map

The concrete map is `reduce (a₀,V) = (exp(-2V) a₀, exp(-2V))` from
`paper/main.tex:199–208`. `EnvironmentLaw` denotes the physical law throughout.
A reduced local observable is pulled back through this map; its first component
must not be identified with the physical coefficient without this transport.
-/

namespace EinsteinRelation.Probability

/-- The physical-to-reduced map is continuous for locally uniform convergence. -/
theorem continuous_reduce {d : ℕ} : Continuous (reduce (d := d)) := by
  apply Continuous.prodMk
  · apply ContinuousMap.continuous_of_continuous_uncurry
    exact (Real.continuous_exp.comp
      (continuous_const.mul (continuous_fst.snd.eval continuous_snd))).smul
        (continuous_fst.fst.eval continuous_snd)
  · apply ContinuousMap.continuous_of_continuous_uncurry
    exact Real.continuous_exp.comp
      (continuous_const.mul (continuous_fst.snd.eval continuous_snd))

/-- The concrete reduced pair defines a measurable pushforward law. -/
theorem measurable_reduce {d : ℕ} : Measurable (reduce (d := d)) :=
  continuous_reduce.measurable

/-- A reduced joint observation on U is measurable from the physical pair on U. -/
theorem localSigma_reduce_comap_le {d : ℕ} (U : Set (Vec d)) :
    (localSigma U).comap (reduce (d := d)) ≤ localSigma U := by
  unfold localSigma
  rw [MeasurableSpace.comap_iSup]
  apply iSup_le
  intro x
  rw [MeasurableSpace.comap_comp]
  apply le_trans _ (le_iSup _ x)
  let F : Mat d × ℝ → Mat d × ℝ := fun p =>
    (Real.exp (-2 * p.2) • p.1, Real.exp (-2 * p.2))
  have hF : Measurable F := by
    exact ((Real.continuous_exp.comp (continuous_const.mul continuous_snd)).smul
      continuous_fst |>.prodMk
        (Real.continuous_exp.comp (continuous_const.mul continuous_snd))).measurable
  have h := MeasurableSpace.comap_mono
    (g := fun ω : FieldPair d => (ω.1 x, ω.2 x)) hF.comap_le
  rw [MeasurableSpace.comap_comp] at h
  exact h

/-- The restriction-locality consumer of the joint sigma transport inequality. -/
theorem measurable_reduce_local {d : ℕ} (U : Set (Vec d)) :
    @Measurable (FieldPair d) (FieldPair d) (localSigma U) (localSigma U)
      (reduce (d := d)) :=
  Measurable.of_comap_le (localSigma_reduce_comap_le U)

/-- Stationarity is preserved by the actual pointwise environment reduction. -/
theorem isStationary_map_reduce {d : ℕ} (Q : MeasureTheory.Measure (FieldPair d))
    (hQ : IsStationary Q) : IsStationary (MeasureTheory.Measure.map reduce Q) := by
  intro x
  rw [MeasureTheory.Measure.map_map (measurable_translate x) measurable_reduce]
  change MeasureTheory.Measure.map (reduce ∘ translate x) Q =
    MeasureTheory.Measure.map reduce Q
  rw [← MeasureTheory.Measure.map_map measurable_reduce (measurable_translate x), hQ x]

end EinsteinRelation.Probability
