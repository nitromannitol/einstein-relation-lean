import EinsteinFull.Frozen.SharpExample

/-!
# Proposition 7.1 (paper label `sharp.example`): the solution

The statement below is the statement of `Challenge.lean`, word for word. It is elaborated here
in the environment of the library, where the definitions that it uses are the library's own; the proof
applies the library theorem `EinsteinFull.Frozen.sharp_example`.
-/

open MeasureTheory Filter
open scoped Topology

namespace EinsteinFull.Frozen

open EinsteinRelation

theorem _root_.EinsteinFullAudit.SharpExample.sharp_example (d : ℕ) (hd : 2 ≤ d) :
    ∃ (D : StructuralData d) (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q ∧ ∃ c₀ : ℝ, 0 < c₀ ∧
        ∀ P : DiffusionFamily d,
        IsSignedPhysicalFamily (⟨0, by omega⟩ : Fin d) Q P →
        ∀ covariance : Mat d,
        HasDiffusivity Q.measure (originLaw (P 0)) covariance →
        ∀ velocity : ℝ → Vec d,
        (∀ lam : ℝ, 0 < lam →
          HasQuenchedVelocity Q.measure (originLaw (P lam)) (velocity lam)) →
          Tendsto (fun lam : ℝ =>
            dot ((lam⁻¹ • velocity lam) -
              covariance.mulVec (unitVector (⟨0, by omega⟩ : Fin d)))
              (unitVector (⟨0, by omega⟩ : Fin d)) / lam)
            (𝓝[>] (0 : ℝ)) (𝓝 c₀) := by
  exact EinsteinFull.Frozen.sharp_example d hd

end EinsteinFull.Frozen
