import EinsteinFull.Calculus.S2ForwardMartingale
import EinsteinFull.Frozen.SignedPhysicalFamily

/-!
# From a signed physical family to a reduced family

Given a family `X` with `IsSignedPhysicalFamily i Q X` (every real force, almost every
environment, origin laws solving the physical martingale problem) and almost-sure smoothness of
the environment, the forward time change produces a family `Y` of quenched path-law kernels whose
origin laws solve the reduced martingale problem for every real force, and `X` is recovered from
`Y` by `inverseClockPath`.
-/

open MeasureTheory
open scoped NNReal

namespace EinsteinFull
open EinsteinRelation EinsteinRelation.Clock EinsteinRelation.Clock.InverseMeaningV3

theorem exists_reducedFamily_of_signedPhysical {d : ℕ} {Λ₀ r₀ : ℝ} (i : Fin d)
    (Q : EnvironmentLaw d Λ₀ r₀) (hsmooth : ∀ᵐ ω ∂Q.measure, IsSmoothFieldPair ω)
    (X : DiffusionFamily d) (hX : IsSignedPhysicalFamily i Q X) :
    ∃ Y : DiffusionFamily d,
      (∀ lam : ℝ, ∀ᵐ ω ∂Q.measure,
        SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (Y lam (0, ω))) ∧
      ∀ lam : ℝ, ∀ᵐ ω ∂Q.measure, ∃ hω : IsRegular Λ₀ ω,
        X lam (0, ω) = (Y lam (0, ω)).map (fun γ : Path d => inverseClockPath ω γ Λ₀ hω) := by
  have hL : 0 < Λ₀ := lt_of_lt_of_le one_pos Q.ellipticity_parameter
  choose Y hY using fun lam : ℝ => exists_forwardKernel (d := d) Λ₀ (X lam)
  refine ⟨Y, fun lam => ?_, fun lam => ?_⟩
  · filter_upwards [Q.regular, hsmooth, hX lam] with ω hω hs hmp
    rw [hY lam ω hω hmp.1]
    exact forwardClock_solves hL hω hs i lam 0 hmp
  · filter_upwards [Q.regular, hX lam] with ω hω hmp
    refine ⟨hω, ?_⟩
    rw [hY lam ω hω hmp.1, Measure.map_map (measurable_inverseClockPath_fixed ω Λ₀ hω)
      (measurable_forwardClockPath hω)]
    have hid : (fun γ : Path d => inverseClockPath ω γ Λ₀ hω) ∘ forwardClockPath hω = id :=
      funext fun γ => inverseClockPath_forwardClockPath hω γ
    rw [hid, Measure.map_id]

end EinsteinFull
