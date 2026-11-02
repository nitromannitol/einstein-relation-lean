import EinsteinFull.Calculus.CLUnforcedClockL2
import EinsteinFull.Calculus.C20ClockPointwiseApplication
import EinsteinFull.Calculus.C12UnforcedInverseDiffusivity
import EinsteinFull.Blueprint.Foundation.Draft.S2SmoothScopeUnforcedClock
import EinsteinFull.Blueprint.Foundation.Draft.S2SmoothScopeUnforced
import EinsteinFull.Blueprint.Foundation.Draft.S2SmoothScopeCorrectorCovariance
import EinsteinFull.Blueprint.Foundation.Draft.S2SmoothScopePathwise

/-!
# The unforced clock

`eq.time-change-identities#unforced-clock` in the smooth scope. The unit clock shift preserves
the annealed unforced law and the normalized clock converges in L², so the pointwise ergodic
theorem gives the almost-sure clock rate `m`. The corrector covariance of the reduced process
then gives the diffusivity `m⁻¹ ahom` of the physical process.
-/

open MeasureTheory Filter
open scoped NNReal

namespace EinsteinFull.Blueprint
open EinsteinFull EinsteinRelation

/-- Smooth-scope unforced-clock identity, from the unforced process, the corrector covariance and
the pathwise time change; the structural data are rebuilt from `(Λ₀, r₀, b)`. -/
theorem node_eq_u2E_time_u2D_change_u2D_identities_u23_unforced_u2D_clock_of_deps
    (hUnforced : node_stationary_u2D_environment_u23_unforced_u2D_processStmtV2)
    (hCovariance : node_eq_u2E_time_u2D_change_u2D_identities_u23_corrector_u2D_covarianceStmtV2)
    (hPathwise : node_eq_u2E_reduced_u2D_generator_u23_pathwiseStmtV2) :
    node_eq_u2E_time_u2D_change_u2D_identities_u23_unforced_u2D_clockStmtV2 := by
  intro d hd Λ₀ r₀ b Q hΛ₀ hr₀ hb hsm X Y hX hY hmap
  let D : StructuralData d := ⟨Λ₀, r₀, b, hΛ₀, hr₀, hb⟩
  have hQ : HasSmoothBounds D Q := hsm
  have hunf : UnforcedAt hd Q := hUnforced d hd D Q hQ
  have hpath : PathwiseAt Q := fun i lam => hPathwise d hd D Q hQ i lam
  have hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw Y ω) :=
    hY.mono fun _ h => h.1
  have hrate : HasReducedClockRate Q Y (∫ ω, ω.2 0 ∂reducedLaw Q) :=
    c20_clock_rate_of_regular_clock_l2_error Q Y hprob _
      (measurePreserving_c12ClockShift_one hd D Q hQ hunf hpath Y hY hprob)
      (tendsto_unforced_clock_l2_error hd D Q hQ hunf hpath Y hY hprob)
  exact ⟨hrate, supplied_unforced_inverse_diffusivity_of_rate d hd Λ₀ r₀ Q X Y hX hY hmap
    hrate (hCovariance d hd Λ₀ r₀ b Q hΛ₀ hr₀ hb hsm Y hY)⟩

end EinsteinFull.Blueprint
