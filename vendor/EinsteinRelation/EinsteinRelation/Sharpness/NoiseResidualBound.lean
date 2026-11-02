import EinsteinRelation.Sharpness.CompactLocalBound
import EinsteinRelation.Sharpness.NoiseContinuity
import Mathlib.MeasureTheory.Measure.Trim

/-! # Actual residual compact bound under the probability measure

Source: `paper/main.tex:1212–1216`, the first convolution `h ≔ ζ * tanh(K * W)` of the sharpness
example. For a fixed smooth compactly supported kernel `K`, a test function `f`, a point `x`, and a
real coefficient `a`, the residual sample

  `R ω y ≔ W ω (kernelTest K (x - y) - a • f)`

is the actual distribution `W ω` evaluated on the actual compact test function
`kernelTest K (x - y) - a • f`. By the true linearity of the continuous linear map `W ω`, it equals
`mollifiedNoise (W ω) K (x - y) - a * W ω f`, so it is continuous in `y` for every sample by
`continuous_mollifiedNoise`. No `L²` continuity is used.

The `C`-indexed residual evaluations generate the coarse sigma-algebra `⨆ y : C, ...`, which lies
below the ambient sigma-algebra because each evaluation is measurable by `hmeas`. The local
compact-bound lemma `exists_positive_probability_compact_bound_of_local` is applied to the trimmed
probability measure `P.trim hle` on that coarse sigma-algebra. Its positive mass is transferred back
to `P` on coarse-measurable events by `trim_measurableSet_eq`.

Nothing is assumed about measurability of an uncountable supremum, independence, Gaussian laws,
covariance constancy, or boundedness of the residual event.
-/

open MeasureTheory

namespace EinsteinRelation.Sharpness

/-- Transfer of the local compact bound to a coarser sigma-algebra `m ≤ m0`. The lemma is applied
to the trimmed probability measure `P.trim hle`, which has the same mass as `P` on `m`-measurable
events, so positivity of the trimmed mass gives positivity of `P` at the same bound `M`. -/
private theorem exists_positive_probability_on_trim {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : @Measure Ω m0) [IsProbabilityMeasure P] {m : MeasurableSpace Ω} (hle : m ≤ m0)
    {d : ℕ} (H : Ω → Vec d → ℝ) (C : Set (Vec d)) (hC : IsCompact C)
    (hcont : ∀ ω, ContinuousOn (H ω) C)
    (hmeas : ∀ y ∈ C, Measurable[m] (fun ω => H ω y)) :
    ∃ M : ℕ, MeasurableSet[m] {ω | ∀ y ∈ C, |H ω y| ≤ (M : ℝ)} ∧
      0 < P {ω | ∀ y ∈ C, |H ω y| ≤ (M : ℝ)} := by
  have huniv : (P.trim hle) Set.univ = 1 := by
    rw [trim_measurableSet_eq hle (@MeasurableSet.univ Ω m)]
    exact measure_univ
  have hprob : @IsProbabilityMeasure Ω m (P.trim hle) := ⟨huniv⟩
  obtain ⟨hmeasS, M, hM⟩ :=
    @exists_positive_probability_compact_bound_of_local Ω m (P.trim hle) hprob d H C hC hcont hmeas
  have hPS : (P.trim hle) {ω | ∀ y ∈ C, |H ω y| ≤ (M : ℝ)} =
      P {ω | ∀ y ∈ C, |H ω y| ≤ (M : ℝ)} :=
    trim_measurableSet_eq hle (hmeasS M)
  exact ⟨M, hmeasS M, hM.trans_eq hPS⟩

/-- The actual residual compact bound under the probability measure `P`. The residual sample
`R ω y = W ω (kernelTest K (x - y) - a • f)` is continuous in `y` by `continuous_mollifiedNoise`,
and each of its evaluations is measurable by `hmeas`. The coarse sigma-algebra `⨆ y : C, ...` is the
supremum of these `C`-indexed evaluations. The bound event is measurable for it and has positive
probability under `P`. -/
theorem exists_positive_probability_noise_residual_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} (W : Ω → NoiseSample d)
    (hmeas : ∀ f : NoiseTest d, Measurable (fun ω => W ω f))
    (K f : NoiseTest d) (x : Vec d) (a : ℝ) (C : Set (Vec d)) (hC : IsCompact C) :
  ∃ M : ℕ,
    MeasurableSet[⨆ y : C, (borel ℝ).comap
      (fun ω => W ω (kernelTest K (x-y.1) - a • f))]
      {ω | ∀ y ∈ C, |W ω (kernelTest K (x-y) - a • f)| ≤ (M : ℝ)} ∧
    0 < P {ω | ∀ y ∈ C, |W ω (kernelTest K (x-y) - a • f)| ≤ (M : ℝ)} := by
  -- The actual continuous linear map `W ω` splits the difference and the scalar multiple.
  have hres : ∀ (ω : Ω) (y : Vec d),
      W ω (kernelTest K (x - y) - a • f) = mollifiedNoise (W ω) K (x - y) - a * W ω f := by
    intro ω y
    show W ω (kernelTest K (x - y) - a • f) = W ω (kernelTest K (x - y)) - a * W ω f
    rw [map_sub, map_smul, smul_eq_mul]
  -- The residual sample is continuous in `y` globally, hence on `C`.
  have hcont : ∀ ω, ContinuousOn (fun y : Vec d => W ω (kernelTest K (x - y) - a • f)) C := by
    intro ω
    have hcomp : Continuous fun y : Vec d => mollifiedNoise (W ω) K (x - y) :=
      (continuous_mollifiedNoise (W ω) K).comp (continuous_sub_left x)
    have hg : Continuous fun y : Vec d => W ω (kernelTest K (x - y) - a • f) :=
      (hcomp.sub (continuous_const : Continuous fun _ : Vec d => a * W ω f)).congr
        fun y => (hres ω y).symm
    exact hg.continuousOn
  -- The coarse sigma-algebra is the supremum of the `C`-indexed residual evaluations. It lies
  -- below the ambient sigma-algebra because each evaluation is measurable.
  have hle : (⨆ y : C, (borel ℝ).comap
      (fun ω => W ω (kernelTest K (x - y.1) - a • f))) ≤ ‹MeasurableSpace Ω› := by
    refine iSup_le fun y => ?_
    exact measurable_iff_comap_le.mp (hmeas (kernelTest K (x - y.1) - a • f))
  -- Each `C`-indexed residual evaluation is measurable for the coarse sigma-algebra.
  have hmeasC : ∀ y ∈ C, Measurable[(⨆ y' : C, (borel ℝ).comap
      (fun ω => W ω (kernelTest K (x - y'.1) - a • f)))]
      (fun ω => W ω (kernelTest K (x - y) - a • f)) := by
    intro y hy
    have hy_le : (borel ℝ).comap (fun ω => W ω (kernelTest K (x - y) - a • f)) ≤
        ⨆ y' : C, (borel ℝ).comap (fun ω => W ω (kernelTest K (x - y'.1) - a • f)) :=
      le_iSup (fun y' : C => (borel ℝ).comap
        (fun ω => W ω (kernelTest K (x - y'.1) - a • f))) ⟨y, hy⟩
    exact Measurable.mono (comap_measurable _) hy_le le_rfl
  exact exists_positive_probability_on_trim P hle (H := fun ω y => W ω (kernelTest K (x - y) - a • f))
    C hC hcont hmeasC

end EinsteinRelation.Sharpness
