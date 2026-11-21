import EinsteinFull.Calculus.SbxBCenteredSurvivalR12
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_past_u2D_kernel
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_regen_u2D_tails
import EinsteinFull.PhysicalRegeneration.Calculus.SbxAGlobalReducedKernelR04
import EinsteinFull.PhysicalRegeneration.Calculus.SbxBCenteredTubeChainR03
import EinsteinFull.PhysicalRegeneration.Calculus.SbxS3JointReducedKernelR01
import EinsteinFull.PhysicalRegeneration.Calculus.SbxS6SuppliedKernelUniquenessR01
import EinsteinFull.PhysicalRegeneration.Frozen.RegenerationCoupling
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Calculus.SbxBCenteredSurvivalR12`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/

open MeasureTheory
open scoped NNReal ENNReal
namespace EinsteinFull
open EinsteinRelation EinsteinRelation.Diffusion EinsteinRelation.SpatialDirichlet
open EinsteinRelation.External.GantertSection7Support
open EinsteinFull.Blueprint.TubeProbability EinsteinFull.External.Source.GMP
/-- The physical-kernel version of `EinsteinFull.b_centered_local_return_input_of_native_inputs`. -/
theorem b_centered_local_return_input_of_native_inputs_phys
    (hinputs : ∀ (d : ℕ) (hd : 2 ≤ d) (L l : ℝ), 0 < l →
      ∃ κ δ H : ℝ, 0 < κ ∧ 0 < δ ∧ 0 < H ∧
        b_native_spectral_input d hd L l κ ∧ b_native_half_mass_input d hd l κ δ ∧
        b_native_local_comparison_input d hd l κ δ H) :
    b_centered_local_return_input_phys := by
  intro d hd L r₀ l hl
  obtain ⟨κ, δ, H, hκ, hδ, hH, hkernel, hmass, hcompare⟩ := hinputs d hd L l hl
  obtain ⟨ε, hε, hbound⟩ := b_scaled_centered_return_of_native_short_time
    d hd κ δ H (l/2) 1 hκ hδ hH (by positivity) (by norm_num)
  refine ⟨1, min ε 1, by norm_num, lt_min hε (by norm_num), min_le_right _ _, ?_⟩
  intro Q lam h0 h1 P hP
  filter_upwards [hP] with ω hωP
  obtain ⟨hω, R, hrow⟩ := hωP
  intro c y hy
  let η := ω
  let hωc : IsRegular (sourceReducedBound L) (translate c η) :=
    (ActualImageLpStateTransport.isRegular_translate_iff c η).mpr hω
  let R' := Classical.choice (u5_regular_signed_fixed_environment_realization_exists
    hd (one_le_sourceReducedBound Q.ellipticity_parameter) (translate c η) hωc |lam| h0.le h1)
  obtain ⟨ρ, α, K, G, hell, hcoeff, hK⟩ := hkernel (translate c η) hωc |lam| h0 h1
  have hy' : y-c ∈ sourceBall (0 : Vec d) (((l/2)/|lam|)/2) := by
    change euclideanNorm (y-c-0) < ((l/2)/|lam|)/2
    simp only [sub_zero]
    convert hy using 1; ring
  have hb := hbound |lam| h0 h1 R' ρ α hell hcoeff K G hK
    (hmass (translate c η) |lam| h0 h1 ρ α K G hell hcoeff hK)
    (hcompare (translate c η) |lam| h0 h1 ρ α K G hell hcoeff hK) (y-c) hy'
  have ht := b_centered_return_of_translated_environment hd (sourceReducedBound L)
    (one_le_sourceReducedBound Q.ellipticity_parameter) η hω |lam| h0.le h1 c hωc R R'
    y (1/|lam|^2).toNNReal ((l/2)/|lam|)
  rw [ht] at hb
  rw [hrow y]
  apply (ENNReal.ofReal_le_ofReal (min_le_left ε 1)).trans
  have heq : (l/2)/|lam| = (l/|lam|)/2 := by ring
  have heq2 : (l/|lam|)/2/2 = (l/|lam|)/4 := by ring
  simpa [heq, heq2] using hb

end EinsteinFull
