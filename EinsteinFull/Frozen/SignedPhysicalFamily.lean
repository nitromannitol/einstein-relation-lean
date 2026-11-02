import EinsteinRelation.Diffusion.Basic

open MeasureTheory

namespace EinsteinFull

open EinsteinRelation

/-- The physical diffusion of Section 1 for every real force, specified by its
conservative martingale problem at the origin. -/
def IsSignedPhysicalFamily {d : ℕ} {Λ₀ r₀ : ℝ} (i : Fin d)
    (Q : EnvironmentLaw d Λ₀ r₀) (P : DiffusionFamily d) : Prop :=
  ∀ lam : ℝ, ∀ᵐ ω ∂Q.measure,
    SolvesMartingaleProblem (physicalGenerator i ω lam) 0 (P lam (0, ω))

end EinsteinFull
