import EinsteinFull.Regeneration.PhysicalKernel
import EinsteinFull.PhysicalRegeneration.Calculus.SbxS1CouplingAssemblyR02
import EinsteinFull.PhysicalRegeneration.Regeneration.SbxS1JointSplitR01
import EinsteinFull.PhysicalRegeneration.Regeneration.GMPUniformExitMinorization
import EinsteinFull.PhysicalRegeneration.Frozen.RegenerationCoupling

/-!
# The split coupling of the physical diffusion

GMP 2012, Proposition 5.4 (p. 23), applied to the physical diffusion of Section 7: the killed
physical kernel over one interval of length `λ⁻²` dominates `δ` times the uniform law on the
endpoint ball (local heat-kernel lower bounds hold for every regular pair), so the physical
kernel carries the split coupling, with the coin probability fixed before the environment law
and the force.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open EinsteinRelation.External.GantertSection7Support EinsteinFull.External.Source.GMP
open scoped NNReal

namespace EinsteinFull.Regeneration

/-- For every scale `l ≥ 1` there is a coin probability `δ`, fixed before the environment law and
the force, such that every physical kernel agrees almost surely with a kernel that carries the
split coupling of GMP Proposition 5.4 at scale `l / λ` and grid `λ⁻²`. -/
theorem exists_physical_regeneration_coupling (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ l : ℝ)
    (hl : 1 ≤ l) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
        (P : QuenchedPathLaws d),
        IsGMPPhysicalKernel hd Q.ellipticity_parameter Q lam h₀.le h₁ P →
        ∃ (P' : QuenchedPathLaws d) (K : CoupledQuenchedLaws d),
          (∀ᵐ ω ∂Q.measure, ∀ x, P' (x, ω) = P (x, ω)) ∧
          IsRegenerationCouplingPhys hd Q lam l δ h₀.le h₁ P' K := by
  obtain ⟨δ, hδ₀, hδ₁, hmin⟩ := uniform_regular_gmp_source_minorization_phys d hd Λ₀ r₀ l hl
  refine ⟨δ, hδ₀, hδ₁, ?_⟩
  intro Q lam h₀ h₁ P hP
  have hPR := hP.reducedBound
  have hminP : ∀ᵐ ω ∂Q.measure, HasSourceMinorization (fun x => P (x, ω))
      (Renewal.regenDelta lam) δ (l / lam) (Renewal.forceCoord hd) := by
    filter_upwards [hPR] with ω hω
    obtain ⟨hω', G, hG⟩ := hω
    have hf : (fun x => P (x, ω)) = fun x => G.pathLaw x := funext hG
    rw [hf]
    exact hmin Q lam h₀ h₁ ω hω' G
  obtain ⟨P', hae, hP', hMarkov, hstart, hmin'⟩ :=
    SbxS1CouplingAssemblyR02.patch_reduced_kernel_phys hd Q lam h₀.le h₁
      (Renewal.regenDelta lam) δ (l / lam) (Renewal.forceCoord hd) P hPR hminP
  let : IsMarkovKernel P' := hMarkov
  have hΔ := EinsteinRelation.regenDelta_pos h₀
  have hR : 0 < l / lam := div_pos (lt_of_lt_of_le zero_lt_one hl) h₀
  let K := splitContinuousCouplingKernel (Renewal.regenDelta lam) hΔ δ (l / lam)
    (Renewal.forceCoord hd) hδ₀ hδ₁ hR P' hmin'
  have hK : IsRegenerationCouplingPhys hd Q lam l δ h₀.le h₁ P' K :=
    s1_canonical_all_clauses_phys (Renewal.regenDelta lam) hΔ δ (l / lam)
      (Renewal.forceCoord hd) hδ₀ hδ₁ hR P' hmin' hstart hd Q h₀.le h₁ hP'
  exact ⟨P', K, hae, hK⟩

end EinsteinFull.Regeneration
