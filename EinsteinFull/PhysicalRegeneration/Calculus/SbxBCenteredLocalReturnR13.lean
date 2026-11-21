import EinsteinFull.Calculus.SbxBCenteredLocalReturnR13
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_past_u2D_kernel
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_regen_u2D_tails
import EinsteinFull.PhysicalRegeneration.Calculus.SbxAGlobalReducedKernelR04
import EinsteinFull.PhysicalRegeneration.Calculus.SbxBCenteredSurvivalR12
import EinsteinFull.PhysicalRegeneration.Calculus.SbxBCenteredTubeChainR03
import EinsteinFull.PhysicalRegeneration.Calculus.SbxS3JointReducedKernelR01
import EinsteinFull.PhysicalRegeneration.Calculus.SbxS6SuppliedKernelUniquenessR01
import EinsteinFull.PhysicalRegeneration.Frozen.RegenerationCoupling
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Calculus.SbxBCenteredLocalReturnR13`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/

open MeasureTheory
open EinsteinRelation EinsteinRelation.SpatialDirichlet
open EinsteinRelation.External.GantertSection7Support
open EinsteinFull.Blueprint.TubeProbability EinsteinFull.External.Source.GMP
namespace EinsteinFull
/-- The physical-kernel version of
`EinsteinFull.b_centered_local_return_of_continuous_native_primitives`. -/
theorem b_centered_local_return_of_continuous_native_primitives_phys
    (hspectral : b_centered_continuous_spectral_existence)
    (hsurvival : b_centered_global_half_survival)
    (hcomparison : b_centered_global_native_comparison) :
    b_centered_local_return_input_phys := by
  apply b_centered_local_return_input_of_native_inputs_phys
  intro d hd L l hl
  let M := max 1 (sourceReducedBound L)
  have hLpos : 0 < sourceReducedBound L := by
    unfold sourceReducedBound
    apply mul_pos (Real.exp_pos _)
    nlinarith [sq_nonneg (L + 1/6)]
  have hLM : sourceReducedBound L ≤ M := le_max_right _ _
  let κ := bPhysicalClippedKappa M (l/2)
  have hκ : 0 < κ := b_physical_clipped_kappa_pos (le_max_left _ _)
  obtain ⟨δ₁, hδ₁, hmass⟩ := hsurvival d hd κ hκ
  obtain ⟨δ₂, H, hδ₂, hH, hcomp⟩ := hcomparison d hd κ hκ
  refine ⟨κ, min δ₁ δ₂, H, hκ, lt_min hδ₁ hδ₂, hH, ?_, ?_, ?_⟩
  · intro ω hω μ hμ hμ1
    have hωM : IsRegular M ω := by
      rcases hω with ⟨hell, hpot, hlip, hpotlip⟩
      refine ⟨?_, fun x => (hpot x).trans hLM, ?_, ?_⟩
      · intro x
        refine ⟨(hell x).1, fun v => ⟨?_, ?_⟩⟩
        · exact (mul_le_mul_of_nonneg_right (inv_anti₀ hLpos hLM)
            (euclideanSq_nonneg_coords v)).trans ((hell x).2 v).1
        · exact ((hell x).2 v).2.trans (mul_le_mul_of_nonneg_right hLM
            (euclideanSq_nonneg_coords v))
      · intro x y v
        exact (hlip x y v).trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hLM (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
      · intro x y
        exact (hpotlip x y).trans (mul_le_mul_of_nonneg_right hLM (Real.sqrt_nonneg _))
    let ρ := bPhysicalClippedRho hd ω (l/2) μ
    let α := bPhysicalClippedAlpha hd ω (l/2) μ
    have hell : IsUniformlyElliptic κ ρ α :=
      b_physical_clipped_elliptic (le_max_left _ _) (by positivity) hd ω hωM μ
    have hρ : Continuous ρ := b_physical_clipped_rho_continuous hd ω (l/2) μ
    obtain ⟨K, G, hK⟩ := hspectral d hd κ hκ ((l/2)/μ) (by positivity) ρ α hell hρ
    exact ⟨ρ, α, K, G, hell,
      fun x hx => b_physical_clipped_eq_on_ball hμ hd ω x hx, hK⟩
  · intro ω μ hμ hμ1 ρ α K G hell hcoeff hK x r u hr hball hu hut
    exact hmass ((l/2)/μ) (by positivity) ρ α hell K G hK x r u hr hball hu
      (hut.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg r)))
  · intro ω μ hμ hμ1 ρ α K G hell hcoeff hK x y r u hr hball hy hu hut hxy
    exact hcomp ((l/2)/μ) (by positivity) ρ α hell K G hK x y r u hr hball hy hu
      (hut.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg r))) hxy

end EinsteinFull
