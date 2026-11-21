import EinsteinRelation.Regeneration.CoupledEnvironmentRegularity
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.DeterministicEndpointNullSets
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinRelation.Regeneration.CoupledEnvironmentRegularity`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/


open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinRelation.Regeneration
/-- The physical-kernel version of `EinsteinRelation.Regeneration.CoupledEnvironmentRegular`. -/
def CoupledEnvironmentRegularPhys {d : ℕ} (hd : 2 ≤ d) (Λ₀ : ℝ) (hΛ₀ : 1 ≤ Λ₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d) (ω : FieldPair d) : Prop :=
  (∃ hω : IsRegular (sourceReducedBound Λ₀) ω,
    ∃ r : External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀)
      ω hω lam h0 h1,
      ∀ x, P (x, ω) = r.pathLaw x) ∧
  CoupledFibreRegular Δ δ R i P K (0, ω) ∧
  (∀ᵐ x ∂(volume : Measure (Vec d)), CoupledFibreRegular Δ δ R i P K (x, ω)) ∧
  ∀ n : ℕ, 1 ≤ n → ∀ x : Vec d,
    (P (x, ω)).map (pathPosition ((n : ℝ≥0) * Δ)) ≪ (volume : Measure (Vec d))

/-- The physical-kernel version of `EinsteinRelation.Regeneration.ae_coupledEnvironmentRegular`. -/
theorem ae_coupledEnvironmentRegular_phys {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q.measure K) (hm : HasPathMarginals Q.measure K P)
    (hP : EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd Q.ellipticity_parameter Q lam h0 h1 P)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ R : ℝ) (i : Fin d)
    (hr : HasDeterministicRestart Q.measure Δ K)
    (hone : Renewal.HasOneIntervalKernel Q.measure Δ δ R i P K) :
    ∀ᵐ ω ∂Q.measure,
      CoupledEnvironmentRegularPhys hd Λ₀ Q.ellipticity_parameter lam h0 h1 Δ δ R i P K ω := by
  have hprod : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
      CoupledFibreRegular Δ δ R i P K p := by
    filter_upwards [hK.2, hm.2, hr.2, hone.2] with p hp hm hr ho
    exact ⟨hp, hm, hr, ho⟩
  have hswap : ∀ᵐ p ∂Q.measure.prod (volume : Measure (Vec d)),
      CoupledFibreRegular Δ δ R i P K (p.2, p.1) := by
    have h := (Measure.measurePreserving_swap
      (μ := Q.measure) (ν := (volume : Measure (Vec d)))).quasiMeasurePreserving.ae hprod
    exact h
  have hdens : ∀ n : ℕ, ∀ᵐ ω ∂Q.measure, 1 ≤ n → ∀ x : Vec d,
      (P (x, ω)).map (pathPosition ((n : ℝ≥0) * Δ)) ≪ (volume : Measure (Vec d)) := by
    intro n
    by_cases hn : 1 ≤ n
    · have ht : 0 < (n : ℝ≥0) * Δ := mul_pos (by exact_mod_cast (by omega : 0 < n)) hΔ
      exact (map_pathPosition_absolutelyContinuous_of_isGMPReducedKernel_phys hd
        Q.ellipticity_parameter Q lam h0 h1 P hP _ ht).mono fun _ h _ => h
    · exact Filter.Eventually.of_forall fun _ h => (hn h).elim
  filter_upwards [hP, hK.1, hm.1, hr.1, hone.1, Measure.ae_ae_of_ae_prod hswap,
    ae_all_iff.mpr hdens] with ω hp hk hm hr ho hs hdens
  exact ⟨hp, ⟨hk, hm, hr, ho⟩, hs, hdens⟩

end EinsteinRelation.Regeneration
