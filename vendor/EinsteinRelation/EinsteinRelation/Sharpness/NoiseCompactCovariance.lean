import EinsteinRelation.Sharpness.NoiseCutoff
import EinsteinRelation.Sharpness.NoiseProjection
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Tactic.FunProp
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Compactness.Compact

/-! # Constant compact-support covariance for the noise nondegeneracy route

Source: `paper/main.tex:1212–1216`, the internal construction `h ≔ ζ * tanh(K * W)` in
`sharp.example`. For a fixed point `x`, this file produces an auxiliary nonzero compact smooth test
`f` whose integral against the reflected translate `u ↦ K (x - y - u)` equals `∫ K` for every `y`
in the topological support `tsupport ζ`. This strengthens the local statement in
`NoiseCovarianceCutoff`, which only covers the points with `ζ y ≠ 0`.

The test `f` comes from `exists_noiseTest_eq_one_on_compact` applied to the compact set
`{0} ∪ {x - y - z | y ∈ tsupport ζ, z ∈ tsupport K}`. The point `0` makes `f ≠ 0` independent of
whether `ζ` or `K` vanishes. The test is not the paper's choice of `ζ` or `K`; the canonical
choice of the test is an internal obligation of the general. No nondegeneracy of `h` is proved or
assumed here.
-/

open MeasureTheory

namespace EinsteinRelation.Sharpness

/-- For a fixed point `x` and smooth compactly supported tests `ζ` and `K`, there is a nonzero
compact smooth test `f` such that, for every `y` in the topological support of `ζ`, the integral
of `f` against the reflected translate `kernelTest K (x - y)` equals the total integral of `K`. -/
theorem exists_noiseTest_constant_compact_covariance {d : ℕ}
    (ζ K : NoiseTest d) (x : Vec d) :
  ∃ f : NoiseTest d, f ≠ 0 ∧ ∀ y ∈ tsupport (ζ : Vec d → ℝ),
    (∫ u : Vec d, f u * kernelTest K (x-y) u) = ∫ u : Vec d, K u := by
  have hζ : IsCompact (tsupport (ζ : Vec d → ℝ)) := ζ.hasCompactSupport
  have hK : IsCompact (tsupport (K : Vec d → ℝ)) := K.hasCompactSupport
  have hpair : IsCompact (tsupport (ζ : Vec d → ℝ) ×ˢ tsupport (K : Vec d → ℝ)) :=
    hζ.prod hK
  have hcont : Continuous (fun p : Vec d × Vec d => (x - p.1) - p.2) := by
    fun_prop
  have hC : IsCompact (({0} : Set (Vec d)) ∪
      ((fun p : Vec d × Vec d => (x - p.1) - p.2) ''
        (tsupport (ζ : Vec d → ℝ) ×ˢ tsupport (K : Vec d → ℝ)))) :=
    isCompact_singleton.union (hpair.image hcont)
  obtain ⟨f, -, hone⟩ := exists_noiseTest_eq_one_on_compact _ hC
  refine ⟨f, ?_, fun y hy => ?_⟩
  · intro h0
    have h1 : f 0 = 1 := hone 0 (Set.mem_union_left _ (Set.mem_singleton _))
    have h2 : f 0 = 0 := congrArg (fun g : NoiseTest d => g 0) h0
    exact zero_ne_one (h2.symm.trans h1)
  · have hone' : ∀ u : Vec d, kernelTest K (x - y) u ≠ 0 → f u = 1 := by
      intro u hu
      have hKu : K ((x - y) - u) ≠ 0 := hu
      have hKmem : (x - y) - u ∈ tsupport (K : Vec d → ℝ) :=
        subset_tsupport (K : Vec d → ℝ) (Function.mem_support.mpr hKu)
      apply hone
      refine Set.mem_union_right _ ⟨(y, (x - y) - u), ⟨hy, hKmem⟩, ?_⟩
      exact sub_sub_cancel (x - y) u
    rw [integral_noiseTest_mul_of_eq_one f (kernelTest K (x - y)) hone']
    exact integral_sub_left_eq_self (fun u : Vec d => K u) volume (x - y)

end EinsteinRelation.Sharpness
