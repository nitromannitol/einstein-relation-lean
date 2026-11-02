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
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import EinsteinFullAudit.Vocabulary.EinsteinFull.External.AKMAveragedCorrector
import EinsteinFullAudit.Vocabulary.EinsteinFull.External.AKMBlockBoundary
import EinsteinFullAudit.Vocabulary.EinsteinFull.External.AKMBlockChange
import EinsteinFullAudit.Vocabulary.EinsteinFull.External.AKMBlockClt
import EinsteinFullAudit.Vocabulary.EinsteinFull.External.AKMCoarsenedCoefficientEstimates
import EinsteinFullAudit.Vocabulary.EinsteinFull.External.AKMLocalizedEnergy
import EinsteinFullAudit.Vocabulary.EinsteinFull.External.AKMNegativeSobolev
import EinsteinFullAudit.Vocabulary.EinsteinFull.External.AKMSublinearCorrectors
import EinsteinFullAudit.Vocabulary.EinsteinFull.External.BassContinuousElliptic
import EinsteinFullAudit.Vocabulary.EinsteinFull.External.DFGWInvariance
import EinsteinFullAudit.Vocabulary.EinsteinFull.External.GMPVelocity
import EinsteinFullAudit.Vocabulary.EinsteinFull.Frozen.CriticalKernelTerm
import EinsteinFullAudit.Vocabulary.EinsteinFull.Frozen.CriticalVelocityTerm
import EinsteinFullAudit.Vocabulary.EinsteinFull.Frozen.EnvironmentLaw
import EinsteinFullAudit.Vocabulary.EinsteinFull.Frozen.ExpansionModulus
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
# Theorem 1.1 (paper label `t:expansion`): Mathlib-only statement

Theorem 1.1 of *Quantitative Einstein relation for reversible diffusions in a random environment* (Ahmed Bou-Rabee and
Ruizhe Xu), stated with every definition that it uses. This file imports only Mathlib and the files under
`Vocabulary/`, which restate the library definitions under their library names; the final theorem has the
one intentional `sorry` of the challenge. `Solution.lean` proves the same theorem from the library, and the
comparator checks that the two statements, and every definition they depend on, are identical.

**The statement.** Let `d ≥ 2` and let `D` be structural data: an ellipticity constant `Λ₀ ≥ 1`, a range of dependence
`r₀ ≥ 1` and derivative bounds `Λ_k > 0` (`StructuralData`). There are `C ≥ 0` and `λ_* ∈ (0, e⁻¹]` such
that every environment law `Q` satisfying Assumption 1.1 with the constants `Λ₀, r₀` (`EnvironmentLaw`) and
Assumption 1.2 with the bounds `Λ_k` (`HasSmoothBounds`) has vectors `b₁, …, b_{d+1}, c ∈ ℝᵈ` with
`Σⱼ |bⱼ| + |c| ≤ C`, chosen before the diffusion and the force, with the following property. For every
family `P` of path laws of the physical diffusion with force `λ e₁`, for every real `λ`
(`IsSignedPhysicalFamily`), and every diffusivity matrix `Σ_X` of the unforced diffusion (`HasDiffusivity`),
`b₁ = Σ_X e₁`; and for every choice of quenched velocities `ℓ_X(λ)`, `λ ≠ 0` (`HasQuenchedVelocity`), and
every `0 < |λ| ≤ λ_*`,

  `|ℓ_X(λ) − Σ_{j=1}^{d+1} bⱼ λʲ − c S_d(λ)| ≤ C |λ|^{d+1} ω(|λ|)`,

where `S_d(λ) = λ T_d(λ)`, `T_d(λ) = λᵈ log(1/|λ|)` for even `d` and `|λ|ᵈ` for odd `d`
(`criticalVelocityTerm`), and `ω(s) = exp(−√(log(1/s)))` (`expansionModulus`).

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
- `EinsteinFull.External.bass_continuous_elliptic_well_posed`
- `EinsteinFull.External.dfgw_invariance`
- `EinsteinFull.External.gantert_regeneration_tail`
- `EinsteinFull.External.gmp_velocity`
-/

open MeasureTheory
open scoped BigOperators

namespace EinsteinFull.Frozen

open EinsteinRelation

theorem _root_.EinsteinFullAudit.UniformSmallForceExpansion.uniform_small_force_expansion (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C lamStar : ℝ, 0 ≤ C ∧ 0 < lamStar ∧
      ∃ hstar : lamStar ≤ Real.exp (-1),
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      HasSmoothBounds D Q →
      ∃ (b : Fin (d + 1) → Vec d) (c : Vec d),
        (∑ j, euclideanNorm (b j)) + euclideanNorm c ≤ C ∧
        ∀ P : DiffusionFamily d,
        IsSignedPhysicalFamily (⟨0, by omega⟩ : Fin d) Q P →
        ∀ covariance : Mat d,
        HasDiffusivity Q.measure (originLaw (P 0)) covariance →
          b ⟨0, by omega⟩ = covariance.mulVec (unitVector (⟨0, by omega⟩ : Fin d)) ∧
          ∀ velocity : ℝ → Vec d,
          (∀ lam : ℝ, lam ≠ 0 →
            HasQuenchedVelocity Q.measure (originLaw (P lam)) (velocity lam)) →
          ∀ (lam : ℝ) (hlam : 0 < |lam|) (hsmall : |lam| ≤ lamStar),
            euclideanNorm (velocity lam - (∑ j : Fin (d + 1), lam ^ (j.val + 1) • b j) -
              criticalVelocityTerm d lam (abs_pos.mp hlam) • c) ≤
              C * |lam| ^ (d + 1) *
                expansionModulus |lam| hlam (hsmall.trans hstar) := by sorry

end EinsteinFull.Frozen
