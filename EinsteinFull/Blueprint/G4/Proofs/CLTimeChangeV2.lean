import EinsteinFull.Blueprint.Foundation.Draft.S2SmoothScopeForcedClock
import EinsteinFull.Blueprint.Foundation.Draft.S2SmoothScopeUnforcedClock
import EinsteinFull.Blueprint.Foundation.Draft.S2SmoothScopeTimeChange

/-! Smooth-scope (D1) assembly of `eq.time-change-identities` from its two
ordered graph premises, as in the original reduction. -/

namespace EinsteinFull.Blueprint

/-- Assemble the signed fixed-force velocity identities and the unforced clock
and anisotropic covariance identities, retaining the structural clock bound. -/
theorem node_eq_u2E_time_u2D_change_u2D_identities_of_deps
    (hForced : node_eq_u2E_time_u2D_change_u2D_identities_u23_forced_u2D_clockStmtV2)
    (hUnforced : node_eq_u2E_time_u2D_change_u2D_identities_u23_unforced_u2D_clockStmtV2) :
    node_eq_u2E_time_u2D_change_u2D_identitiesStmtV2 := by
  intro Λ₀ hΛ₀
  obtain ⟨Λ, hΛ, hClock⟩ := hForced Λ₀ hΛ₀
  refine ⟨Λ, hΛ, ?_⟩
  intro d hd r₀ b Q hr hb hsm X Y hX hY hCoupling
  refine ⟨?_, hUnforced d hd Λ₀ r₀ b Q hΛ₀ hr hb hsm (X 0) (Y 0) (hX 0) (hY 0) (hCoupling 0)⟩
  intro lam hlam
  obtain ⟨η, vX, vY, hlo, hhi, hη, hvX, hvY, _, _, _, hvel⟩ :=
    hClock d hd r₀ b Q hr hb hsm lam hlam (X lam) (Y lam) (hX lam) (hY lam) (hCoupling lam)
  exact ⟨η, vX, vY, hlo, hhi, hη, hvX, hvY, hvel⟩

end EinsteinFull.Blueprint
