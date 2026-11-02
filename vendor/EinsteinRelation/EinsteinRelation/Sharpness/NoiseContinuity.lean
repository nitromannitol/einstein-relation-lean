import EinsteinRelation.Sharpness.NoiseKernel
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.UniformSpace.HeineCantor

/-! # Continuity of the first convolution `K * W` in the LF test-function topology

Source: `paper/main.tex:1212–1216`, the internal construction of the first convolution
`K * W`. For a fixed smooth compactly supported kernel `K`, the translates
`y ↦ K(x - y)` depend continuously on `x` in the canonical LF topology of the test
functions. Composing a distribution `W` with them gives continuity in `x`, and joint
measurability in `(ω, x)` follows from measurable evaluations.

Only topology is used here. All norms are topology witnesses on `Vec d`, whose source
instance is unchanged. No probability existence, stationarity, or samplewise `L²`
continuity is assumed. -/

namespace EinsteinRelation.Sharpness

/-- The set `{x - y | x ∈ closedBall x0 1, y ∈ tsupport K}` is compact. -/
private theorem isCompact_kernelSupport {d : ℕ} (K : NoiseTest d) (x0 : Vec d) :
    IsCompact ((fun p : Vec d × Vec d => p.1 - p.2) ''
      (Metric.closedBall x0 1 ×ˢ tsupport (⇑K))) :=
  ((isCompact_closedBall x0 1).prod K.hasCompactSupport.isCompact).image
    (continuous_fst.sub continuous_snd)

/-- The kernel translate `y ↦ K(x - y)`, bundled as a smooth test function whose support
lies in the compact set `Kc`, provided it vanishes outside `Kc`. -/
private noncomputable def kernelSupportedIn {d : ℕ} (K : NoiseTest d)
    (Kc : TopologicalSpace.Compacts (Vec d)) (x : Vec d)
    (hx : ∀ y : Vec d, y ∉ (Kc : Set (Vec d)) → K (x - y) = 0) :
    ContDiffMapSupportedIn (Vec d) ℝ ⊤ Kc where
  toFun := fun y => K (x - y)
  contDiff' := K.contDiff.comp (contDiff_const.sub contDiff_id)
  zero_on_compl' := fun y hy => hx y hy

/-- A continuous compactly supported `G` has a family of translates `T x = G(· - x)` in the
bounded continuous functions with the sup norm. -/
private theorem exists_translate_bcf {d : ℕ} {E' : Type*} [NormedAddCommGroup E']
    {G : Vec d → E'} (hG : Continuous G) (hGc : HasCompactSupport G) :
    ∃ T : Vec d → BoundedContinuousFunction (Vec d) E', ∀ x z : Vec d, T x z = G (z - x) := by
  obtain ⟨C, hC⟩ := hG.bounded_above_of_compact_support hGc
  exact ⟨fun x => BoundedContinuousFunction.ofNormedAddCommGroup (fun z => G (z - x))
    (hG.comp (continuous_id.sub continuous_const)) C (fun z => hC (z - x)), fun x z => rfl⟩

/-- Translates of a uniformly continuous compactly supported `G`, as a family of bounded
continuous functions, depend continuously on the translation parameter in the sup norm. -/
private theorem continuous_of_translate {d : ℕ} {E' : Type*} [NormedAddCommGroup E']
    {G : Vec d → E'} (hG : Continuous G) (hGc : HasCompactSupport G)
    {T : Vec d → BoundedContinuousFunction (Vec d) E'}
    (hT : ∀ x z : Vec d, T x z = G (z - x)) :
    Continuous T := by
  rw [Metric.continuous_iff]
  intro x0 ε hε
  obtain ⟨δ, hδ, hGδ⟩ := Metric.uniformContinuous_iff.mp
    (hGc.uniformContinuous_of_continuous hG) (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, fun x hx => ?_⟩
  have hle : dist (T x) (T x0) ≤ ε / 2 := by
    rw [BoundedContinuousFunction.dist_le (half_pos hε).le]
    intro z
    have hzx : dist (z - x) (z - x0) < δ := by
      have h : dist (z - x) (z - x0) = dist x x0 := by
        rw [dist_eq_norm, dist_eq_norm, show z - x - (z - x0) = -(x - x0) by abel, norm_neg]
      rw [h]
      exact hx
    simp only [hT]
    exact (hGδ hzx).le
  linarith

/-- On a closed ball, the kernel translates form a continuous map into the LF
test-function space. -/
private theorem continuousOn_kernelTest_closedBall {d : ℕ} (K : NoiseTest d) (x0 : Vec d) :
    ContinuousOn (kernelTest K) (Metric.closedBall x0 1) := by
  obtain ⟨Kc, hKc⟩ : ∃ Kc : TopologicalSpace.Compacts (Vec d),
      (Kc : Set (Vec d)) = (fun p : Vec d × Vec d => p.1 - p.2) ''
        (Metric.closedBall x0 1 ×ˢ tsupport (⇑K)) :=
    ⟨⟨_, isCompact_kernelSupport K x0⟩, rfl⟩
  have hzero : ∀ x ∈ Metric.closedBall x0 1, ∀ y : Vec d,
      y ∉ (Kc : Set (Vec d)) → K (x - y) = 0 := by
    intro x hx y hy
    refine image_eq_zero_of_notMem_tsupport (fun hmem => hy ?_)
    rw [hKc]
    exact ⟨(x, x - y), ⟨hx, hmem⟩, sub_sub_cancel x y⟩
  obtain ⟨F, hF⟩ : ∃ F : NoiseTest d, ∀ y : Vec d, F y = K (0 - y) :=
    ⟨kernelTest K 0, fun y => rfl⟩
  have hcoe : ∀ (x : Vec d) (hx : ∀ y : Vec d, y ∉ (Kc : Set (Vec d)) → K (x - y) = 0),
      ⇑(kernelSupportedIn K Kc x hx) = fun y => F (y - x) := by
    intro x hx
    funext y
    rw [hF]
    show K (x - y) = K (0 - (y - x))
    congr 1
    abel
  have hsub : (Kc : Set (Vec d)) ⊆ ((⊤ : TopologicalSpace.Opens (Vec d)) : Set (Vec d)) :=
    Set.subset_univ _
  have hΦ : Continuous fun x : Metric.closedBall x0 1 =>
      kernelSupportedIn K Kc (x : Vec d) (hzero (x : Vec d) x.2) := by
    rw [ContDiffMapSupportedIn.continuous_iff_comp]
    intro i
    have hi : (i : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := mod_cast le_top
    have hG : Continuous (iteratedFDeriv ℝ i ⇑F) :=
      F.contDiff.continuous_iteratedFDeriv hi
    have hGc : HasCompactSupport (iteratedFDeriv ℝ i ⇑F) :=
      F.hasCompactSupport.iteratedFDeriv i
    obtain ⟨T, hT⟩ := exists_translate_bcf hG hGc
    have hTc : Continuous T := continuous_of_translate hG hGc hT
    have hfun : ∀ (x : Metric.closedBall x0 1) (z : Vec d),
        (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i
          (kernelSupportedIn K Kc (x : Vec d) (hzero (x : Vec d) x.2))) z =
          iteratedFDeriv ℝ i ⇑F (z - (x : Vec d)) := by
      intro x z
      rw [ContDiffMapSupportedIn.structureMapCLM_top_apply, hcoe, iteratedFDeriv_comp_sub]
    refine (hTc.comp continuous_subtype_val).congr fun x =>
      BoundedContinuousFunction.ext fun z => ?_
    exact (hT (x : Vec d) z).trans (hfun x z).symm
  have hcont : Continuous fun x : Metric.closedBall x0 1 => kernelTest K (x : Vec d) :=
    ((TestFunction.continuous_ofSupportedIn hsub).comp hΦ).congr fun x =>
      TestFunction.ext fun _ => rfl
  rw [continuousOn_iff_continuous_restrict]
  exact hcont

/-- The kernel translates `x ↦ (y ↦ K(x - y))` are continuous into the LF test-function
space `𝓓(ℝ^d)`. This is the continuity of the first convolution's test-function argument
(`paper/main.tex:1212–1216`). -/
theorem continuous_kernelTest {d : ℕ} (K : NoiseTest d) : Continuous (kernelTest K) := by
  rw [continuous_iff_continuousAt]
  intro x0
  exact (continuousOn_kernelTest_closedBall K x0).continuousAt
    (Metric.closedBall_mem_nhds x0 one_pos)

/-- For each sample `W`, the first convolution `x ↦ (K * W)(x)` is continuous. -/
theorem continuous_mollifiedNoise {d : ℕ} (W : NoiseSample d) (K : NoiseTest d) :
    Continuous (mollifiedNoise W K) :=
  (map_continuous W).comp (continuous_kernelTest K)

/-- Joint measurability of `(ω, x) ↦ (K * W(ω))(x)`, from measurable evaluations in `ω` and
continuity in `x`. -/
theorem measurable_mollifiedNoise_uncurry {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (W : Ω → NoiseSample d)
    (hmeas : ∀ f : NoiseTest d, Measurable (fun ω => W ω f)) (K : NoiseTest d) :
    Measurable (fun p : Ω × Vec d => mollifiedNoise (W p.1) K p.2) := by
  have h := MeasureTheory.measurable_uncurry_of_continuous_of_measurable
    (u := fun (x : Vec d) (ω : Ω) => mollifiedNoise (W ω) K x)
    (fun ω => continuous_mollifiedNoise (W ω) K)
    (fun x => measurable_mollifiedNoise W hmeas K x)
  exact h.comp measurable_swap

end EinsteinRelation.Sharpness
