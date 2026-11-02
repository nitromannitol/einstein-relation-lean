import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import EinsteinFullAudit.Vocabulary.EinsteinFull.External.AKMAveragedCorrector
import EinsteinFullAudit.Vocabulary.EinsteinFull.External.AKMBlockBoundary
import EinsteinFullAudit.Vocabulary.EinsteinFull.External.AKMBlockChange
import EinsteinFullAudit.Vocabulary.EinsteinFull.External.AKMBlockClt
import EinsteinFullAudit.Vocabulary.EinsteinFull.External.AKMCoarsenedCoefficientEstimates
import EinsteinFullAudit.Vocabulary.EinsteinFull.External.AKMLocalizedEnergy
import EinsteinFullAudit.Vocabulary.EinsteinFull.External.AKMNegativeSobolev
import EinsteinFullAudit.Vocabulary.EinsteinFull.External.AKMSublinearCorrectors
import EinsteinFullAudit.Vocabulary.EinsteinFull.External.AKMWhiteNoiseExistence
import EinsteinFullAudit.Vocabulary.EinsteinFull.External.BassContinuousElliptic
import EinsteinFullAudit.Vocabulary.EinsteinFull.External.DFGWInvariance
import EinsteinFullAudit.Vocabulary.EinsteinFull.External.GMPVelocity
import EinsteinFullAudit.Vocabulary.EinsteinFull.Frozen.EnvironmentLaw
import EinsteinFullAudit.Vocabulary.EinsteinFull.Frozen.GantertRegenerationTail
import EinsteinFullAudit.Vocabulary.EinsteinFull.Frozen.SignedPhysicalFamily
import EinsteinFullAudit.Vocabulary.EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFullAudit.Vocabulary.EinsteinFull.Frozen.SmoothWithBounds
import EinsteinFullAudit.Vocabulary.EinsteinFull.Frozen.StructuralData
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Calculus.Generator
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Diffusion.Basic
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Basic
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Reduction
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Smooth

/-!
# Proposition 7.1 (paper label `sharp.example`): Mathlib-only statement

Proposition 7.1 of *Quantitative Einstein relation for reversible diffusions in a random environment* (Ahmed Bou-Rabee and
Ruizhe Xu), stated with every definition that it uses. This file imports only Mathlib and the files under
`Vocabulary/`, which restate the library definitions under their library names; the final theorem has the
one intentional `sorry` of the challenge. `Solution.lean` proves the same theorem from the library, and the
comparator checks that the two statements, and every definition they depend on, are identical.

**The statement.** Let `d ≥ 2`. There are structural data `D`, an environment law `Q` satisfying Assumptions 1.1 and 1.2
with the data `D`, and `c₀ > 0` such that, for every family `P` of path laws of the physical diffusion
(`IsSignedPhysicalFamily`), every diffusivity matrix `Σ_X` of the unforced diffusion (`HasDiffusivity`) and
every choice of quenched velocities `ℓ_X(λ)`, `λ > 0` (`HasQuenchedVelocity`),

  `((λ⁻¹ ℓ_X(λ) − Σ_X e₁) · e₁) / λ → c₀` as `λ ↓ 0`.

**Axioms.** The library proves this theorem from `propext`, `Classical.choice`, `Quot.sound` and the
literature inputs below, each a named axiom with its source (see the README). The vocabulary declares
them with their restated statements, `comparator.json` permits exactly these, and the comparator
checks that their statements agree with the library's.

- `EinsteinFull.External.akm_averaged_corrector`
- `EinsteinFull.External.akm_block_boundary`
- `EinsteinFull.External.akm_block_change`
- `EinsteinFull.External.akm_block_clt`
- `EinsteinFull.External.akm_coarsened_coefficient_estimates`
- `EinsteinFull.External.akm_localized_energy`
- `EinsteinFull.External.akm_negative_sobolev`
- `EinsteinFull.External.akm_sublinear_correctors`
- `EinsteinFull.External.akm_white_noise_exists`
- `EinsteinFull.External.bass_continuous_elliptic_well_posed`
- `EinsteinFull.External.dfgw_invariance`
- `EinsteinFull.External.gantert_regeneration_tail`
- `EinsteinFull.External.gmp_velocity`
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
            (𝓝[>] (0 : ℝ)) (𝓝 c₀) := by sorry

end EinsteinFull.Frozen
