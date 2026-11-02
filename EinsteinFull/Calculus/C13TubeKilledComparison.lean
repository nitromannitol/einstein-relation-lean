import EinsteinFull.Blueprint.Foundation.Proofs.SbxS3TubeProbability
import EinsteinFull.Calculus.C13TubeBlockMeasurability

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace EinsteinFull
open EinsteinRelation
open EinsteinRelation.External.GantertSection7Support

/-- The rescaled actual killed endpoint law is dominated by the corresponding
literal tube piece. -/
theorem c13_endpoint_ball_killed_le_piece {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω} {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1}
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)
    (eps : ℝ) (heps : 0 < eps) (c cnext y : Vec d)
    (hstep : euclideanNorm (cnext - c) ≤ eps / 16)
    (hy : euclideanNorm (y - cnext) < eps / 16)
    (hlam : 0 < lam) (h : ℝ) (hh : 0 ≤ h) (x : Vec d)
    (A : Set (Vec d)) (hA : MeasurableSet A) :
    let U : Set (Vec d) := {z | euclideanNorm (z - y) < eps / 4}
    ∀ hU : IsOpen U,
    ((gmpKilledEndpointKernel G ((fun z : Vec d => lam • z) ⁻¹' U)
      (hU.preimage (continuous_id.const_smul lam)) (h / lam ^ 2).toNNReal x).map
      (fun z => lam • z)) A ≤
    G.pathLaw x {Y | (∀ u : ℝ≥0, (u : ℝ) ≤ h →
      euclideanNorm (lam • Y ((u : ℝ) / lam ^ 2).toNNReal - c) < eps / 2) ∧
      lam • Y (h / lam ^ 2).toNNReal ∈ A} := by
  intro U hU
  rw [Blueprint.TubeProbability.rescaled_killedEndpoint_apply_set G U hU hlam h hh x A hA]
  apply measure_mono
  intro Y hY
  refine ⟨?_, hY.2⟩
  intro u hu
  exact Blueprint.TubeProbability.endpoint_ball_subset_piece_ball eps heps c cnext y hstep hy
    (hY.1 u hu)

/-- A supplied local killed endpoint density bound yields the corresponding
literal tube-piece domination. -/
theorem c13_piece_density_of_endpoint_killed_density {d : ℕ} {hd : 2 ≤ d}
    {L : ℝ} {hL : 1 ≤ L} {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1}
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)
    (eps : ℝ) (heps : 0 < eps) (c cnext : Vec d)
    (hstep : euclideanNorm (cnext - c) ≤ eps / 16)
    (hlam : 0 < lam) (h : ℝ) (hh : 0 ≤ h) (x : Vec d) (cstar : ℝ)
    (U : Set (Vec d)) (hU : IsOpen U)
    (hUeq : U = {z | euclideanNorm (z - cnext) < eps / 4})
    (hdom : ∀ A : Set (Vec d), MeasurableSet A →
      A ⊆ {z | euclideanNorm (z - cnext) < eps / 16} →
      ENNReal.ofReal cstar * volume A ≤
        ((gmpKilledEndpointKernel G ((fun z : Vec d => lam • z) ⁻¹' U)
          (hU.preimage (continuous_id.const_smul lam)) (h / lam ^ 2).toNNReal x).map
          (fun z => lam • z)) A) :
    ∀ A : Set (Vec d), MeasurableSet A →
      A ⊆ {z | euclideanNorm (z - cnext) < eps / 16} →
      ENNReal.ofReal cstar * volume A ≤
      G.pathLaw x {Y | (∀ u : ℝ≥0, (u : ℝ) ≤ h →
        euclideanNorm (lam • Y ((u : ℝ) / lam ^ 2).toNNReal - c) < eps / 2) ∧
        lam • Y (h / lam ^ 2).toNNReal ∈ A} := by
  intro A hA hA_sub
  have hy : euclideanNorm (cnext - cnext) < eps / 16 := by
    have hzero : euclideanNorm (0 : Vec d) = 0 := by
      simp [euclideanNorm, euclideanSq, dot]
    simpa only [sub_self, hzero] using (div_pos heps (by norm_num : (0 : ℝ) < 16))
  subst U
  exact (hdom A hA hA_sub).trans
    (c13_endpoint_ball_killed_le_piece G eps heps c cnext cnext hstep hy hlam h hh x A hA hU)

end EinsteinFull
