import EinsteinFull.External.DFGW.ContinuousPathTests
import MarkovProcess.Trajectory.WeakContinuity

/-! # Weak convergence on continuous path space

Finite-dimensional weak convergence and eventual tightness imply weak convergence of laws on
continuous path space. Cylinder functionals are dense uniformly on compact sets.
-/

open MeasureTheory ProbabilityTheory Filter EinsteinRelation MarkovProcess
open scoped NNReal Topology ENNReal

namespace EinsteinFull.External.DFGW

/-- Eventual tightness and convergence of finite-dimensional laws imply convergence of bounded
continuous functionals on continuous path space. -/
theorem tendsto_path_integral_of_tight_of_finiteDimensional
    {d : ℕ} {ι : Type*} {l : Filter ι}
    (Q : ι → ProbabilityMeasure (Path d)) (W : ProbabilityMeasure (Path d))
    (htight : ∀ δ : ℝ, 0 < δ → ∃ K : Set (Path d), IsCompact K ∧
      (W : Measure (Path d)) Kᶜ ≤ ENNReal.ofReal δ ∧
      ∀ᶠ i in l, (Q i : Measure (Path d)) Kᶜ ≤ ENNReal.ofReal δ)
    (hfd : ∀ (I : Finset ℝ≥0) (g : BoundedContinuousFunction (I → Vec d) ℝ),
      Tendsto (fun i => ∫ γ, g (ContinuousPath.finsetEvaluation I γ) ∂(Q i : Measure (Path d))) l
        (𝓝 (∫ γ, g (ContinuousPath.finsetEvaluation I γ) ∂(W : Measure (Path d)))))
    (F : BoundedContinuousFunction (Path d) ℝ) :
    Tendsto (fun i => ∫ γ, F γ ∂(Q i : Measure (Path d))) l
      (𝓝 (∫ γ, F γ ∂(W : Measure (Path d)))) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let ε5 : ℝ := ε / 5
  have hε5 : 0 < ε5 := by dsimp [ε5]; positivity
  let C : ℝ := ‖F‖ + (‖F‖ + ε5)
  have hC : 0 < C := by dsimp [C]; have := norm_nonneg F; linarith
  let δ : ℝ := ε5 / C
  have hδ : 0 < δ := div_pos hε5 hC
  obtain ⟨K, hK, hWK, hQK⟩ := htight δ hδ
  obtain ⟨G, hGcyl, hGnorm, hGapprox⟩ :=
    ContinuousPath.exists_boundedCylinder_approx F hK hε5
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  have herror (ρ : ProbabilityMeasure (Path d)) (hρ : (ρ : Measure (Path d)) Kᶜ ≤ ENNReal.ofReal δ) :
      |(∫ γ, F γ ∂(ρ : Measure (Path d))) - ∫ γ, G γ ∂(ρ : Measure (Path d))| ≤ 2 * ε5 := by
    have hmass : (ρ : Measure (Path d)).real Kᶜ ≤ δ := by
      rw [measureReal_def]
      exact ENNReal.toReal_le_of_le_ofReal hδ.le hρ
    have hbase := abs_integral_sub_le_of_approx_on (ρ : Measure (Path d)) F G hKmeas hε5.le hGapprox
    have hFG : ‖F‖ + ‖G‖ ≤ C := by dsimp [C]; linarith [hGnorm]
    have hprod : (‖F‖ + ‖G‖) * (ρ : Measure (Path d)).real Kᶜ ≤ ε5 := by
      calc
        _ ≤ C * δ := mul_le_mul hFG hmass measureReal_nonneg hC.le
        _ = ε5 := by dsimp [δ]; field_simp
    linarith
  obtain ⟨I, g, hg⟩ := hGcyl
  have hcyl : Tendsto (fun i => ∫ γ, G γ ∂(Q i : Measure (Path d))) l
      (𝓝 (∫ γ, G γ ∂(W : Measure (Path d)))) := by
    simp_rw [hg]
    exact hfd I g
  have hnear : ∀ᶠ i in l, |(∫ γ, G γ ∂(Q i : Measure (Path d))) -
      ∫ γ, G γ ∂(W : Measure (Path d))| < ε5 := by
    have h := Metric.tendsto_nhds.mp hcyl ε5 hε5
    simpa only [Real.dist_eq] using h
  filter_upwards [hQK, hnear] with i hiK hinear
  rw [Real.dist_eq]
  have h1 := herror (Q i) hiK
  have h2 := herror W hWK
  have h2' : |(∫ γ, G γ ∂(W : Measure (Path d))) -
      ∫ γ, F γ ∂(W : Measure (Path d))| ≤ 2 * ε5 := by
    rw [abs_sub_comm]
    exact h2
  have htri1 := abs_sub_le (∫ γ, F γ ∂(Q i : Measure (Path d)))
    (∫ γ, G γ ∂(Q i : Measure (Path d))) (∫ γ, F γ ∂(W : Measure (Path d)))
  have htri2 := abs_sub_le (∫ γ, G γ ∂(Q i : Measure (Path d)))
    (∫ γ, G γ ∂(W : Measure (Path d))) (∫ γ, F γ ∂(W : Measure (Path d)))
  dsimp only [ε5] at h1 h2' hinear
  linarith only [htri1, htri2, h1, h2', hinear]

end EinsteinFull.External.DFGW
