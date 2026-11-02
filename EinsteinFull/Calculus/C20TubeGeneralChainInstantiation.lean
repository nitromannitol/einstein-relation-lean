import EinsteinFull.Calculus.C20TubeNonlinearWeakPairingLimit

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open scoped Topology

namespace EinsteinFull.Calculus

/-- Instantiate the combined-limit premise of the conditional chain-rule producer. -/
theorem c20_actual_weighted_caloric_renormalization_of_producer
    (hpass : ∀ {d : ℕ}
    {κ R a b : ℝ} (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hF0 : F 0 = 0)
    (M : ℝ) (hM : 0 ≤ M)
    (hder : ∀ r, |deriv (deriv F) r| ≤ M)
    (hcombined : ∀ (ψ : ℝ × Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall 0 R →
    let uh := fun h : ℝ => fun z : ℝ × Vec d => h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)
    let Gh := fun h : ℝ => fun z : ℝ × Vec d => h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)
    Tendsto (fun h : ℝ => ∫ z in Set.Ioo a b ×ˢ sourceBall 0 R,
      -(ρ z.2 * F (uh h z)) * fderiv ℝ ψ z (1,0) +
        deriv F (uh h z) * dot ((α z.2).mulVec (Gh h z))
          (fun j => fderiv ℝ ψ z (0,unitVector j)) +
        deriv (deriv F) (uh h z) * dot ((α z.2).mulVec (Gh h z)) (Gh h z) * ψ z)
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (∫ z in Set.Ioo a b ×ˢ sourceBall 0 R,
        -(ρ z.2 * F (u z)) * fderiv ℝ ψ z (1,0) +
        deriv F (u z) * dot ((α z.2).mulVec (G z))
          (fun j => fderiv ℝ ψ z (0,unitVector j)) +
        deriv (deriv F) (u z) * dot ((α z.2).mulVec (G z)) (G z) * ψ z))),
    ∀ ψ : ℝ × Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
    tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall 0 R →
    (∫ z in Set.Ioo a b ×ˢ sourceBall 0 R,
      -(ρ z.2 * F (u z)) * fderiv ℝ ψ z (1,0) +
      deriv F (u z) * dot ((α z.2).mulVec (G z))
        (fun j => fderiv ℝ ψ z (0,unitVector j)) +
      deriv (deriv F) (u z) * dot ((α z.2).mulVec (G z)) (G z) * ψ z) = 0) :
    ∀ {d : ℕ}
    {κ R a b : ℝ} (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hF0 : F 0 = 0)
    (M : ℝ) (hM : 0 ≤ M)
    (hder : ∀ r, |deriv (deriv F) r| ≤ M),
    ∀ ψ : ℝ × Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
    tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall 0 R →
    (∫ z in Set.Ioo a b ×ˢ sourceBall 0 R,
      -(ρ z.2 * F (u z)) * fderiv ℝ ψ z (1,0) +
      deriv F (u z) * dot ((α z.2).mulVec (G z))
        (fun j => fderiv ℝ ψ z (0,unitVector j)) +
      deriv (deriv F) (u z) * dot ((α z.2).mulVec (G z)) (G z) * ψ z) = 0 := by
  intro d κ R a b hκ hR hab ρ α hell u G hcal F hF hF0 M hM hder
  apply hpass hκ hR hab ρ α hell u G hcal F hF hF0 M hM hder
  intro ψ hψ hψc hψs
  exact c20_weighted_forward_nonlinear_weak_pairing_limit_compact
    hκ hR hab ρ α hell 0 u G hcal.1 hcal.2.1 hcal.2.2.1 F hF M hM hder
    ψ hψ hψc hψs

end EinsteinFull.Calculus
