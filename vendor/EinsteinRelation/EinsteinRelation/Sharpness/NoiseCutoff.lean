import EinsteinRelation.Sharpness.NoiseKernel
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Topology.MetricSpace.Bounded

/-! # Compact smooth cutoff for the noise nondegeneracy route

Source: `paper/main.tex:1212–1216`, the internal construction `h ≔ ζ * tanh(K * W)` in
`sharp.example`. This file supplies only an auxiliary smooth compactly supported test
`f : NoiseTest d` with values in `[0, 1]` that equals `1` on a given compact set of coordinates.
It is a test for `integral_noiseTest_mul_of_eq_one`; it is neither the paper's chosen cutoff `ζ`
nor a normalized mollifier.

The coordinate norm of `Vec d` is used only to find a compact closed ball containing the set.
No Euclidean geometric conclusion, source regularity estimate, or nondegeneracy of `h` is proved
or assumed here.
-/

namespace EinsteinRelation.Sharpness

/-- A coordinate smooth bump, packaged as an actual compact smooth test on `Vec d`. -/
private noncomputable def bumpNoiseTest {d : ℕ} (b : ContDiffBump (0 : Vec d)) : NoiseTest d where
  toFun := ⇑b
  contDiff' := (b.contDiff : ContDiff ℝ (⊤ : ℕ∞) ⇑b)
  hasCompactSupport' := b.hasCompactSupport
  tsupport_subset' := Set.subset_univ _

/-- The values of the packaged test are the values of the bump. -/
private theorem bumpNoiseTest_apply {d : ℕ} (b : ContDiffBump (0 : Vec d)) (x : Vec d) :
    bumpNoiseTest b x = b x :=
  rfl

/-- For every compact set `C` of coordinates there is a smooth compactly supported test with
values in `[0, 1]` that equals `1` on `C`. The test is auxiliary: it fixes no choice of `ζ`
and no normalized mollifier. -/
theorem exists_noiseTest_eq_one_on_compact {d : ℕ} (C : Set (Vec d)) (hC : IsCompact C) :
    ∃ f : NoiseTest d, (∀ x : Vec d, 0 ≤ f x ∧ f x ≤ 1) ∧ (∀ x ∈ C, f x = 1) := by
  obtain ⟨R, hR1, hCR⟩ := hC.isBounded.subset_closedBall_lt 1 (0 : Vec d)
  let b : ContDiffBump (0 : Vec d) :=
    { rIn := R
      rOut := R + 1
      rIn_pos := by linarith
      rIn_lt_rOut := by linarith }
  refine ⟨bumpNoiseTest b, fun x => ?_, fun x hx => ?_⟩
  · rw [bumpNoiseTest_apply]
    exact ⟨b.nonneg' x, b.le_one⟩
  · rw [bumpNoiseTest_apply]
    exact b.one_of_mem_closedBall (hCR hx)

end EinsteinRelation.Sharpness
