import EinsteinFull.Calculus.SunaS7SuppliedKilledFDD
import EinsteinFull.Calculus.SunaS2RationalStoppedLaw
import EinsteinFull.Calculus.C2S3PastAssembly
import EinsteinFull.Work.W1.GMPKilledEndpointSupport

open MeasureTheory ProbabilityTheory
open EinsteinRelation EinsteinRelation.Diffusion EinsteinRelation.Regeneration
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal

namespace EinsteinFull

/-- Conditional form of the past-kernel assertion in paper/main.tex:1499.
The hypothesis is the as-yet unproved positive-time locality of killed endpoint
laws for the supplied realizations. Time zero follows from the proved kernel
identity, and the imported FDD and stopped-law adapters supply the remainder. -/
theorem c2_positive_time_past
    (hpart : ∀ {d : ℕ} (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ)
      (ω ω' : FieldPair d) (hω : IsRegular Λ ω) (hω' : IsRegular Λ ω')
      (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
      (r : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
      (r' : GantertFixedEnvironmentRealization hd Λ hΛ ω' hω' lam h0 h1)
      (U : Set (Vec d)), IsOpen U →
      (∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y) →
      ∀ (t : ℝ≥0), 0 < t → ∀ (x : Vec d), x ∈ U →
        ∀ A : Set (Vec d), MeasurableSet A →
        (r.pathLaw x) {γ | (t : ℝ≥0∞) < Diffusion.localityExitTime U γ ∧ γ t ∈ A} =
        (r'.pathLaw x) {γ | (t : ℝ≥0∞) < Diffusion.localityExitTime U γ ∧ γ t ∈ A}) :
    Blueprint.node_app_u3A_factorization_u23_past_u2D_kernelStmt := by
  apply Blueprint.c2_s3_past_kernel_of_requested_locality
  apply s2_past_supplied_stopped_locality_of_killed_fdd
  apply s7_supplied_killed_fdd_locality_of_killed_marginals
  intro d hd Λ hΛ ω ω' hω hω' lam h0 h1 r r' U hU hfields t x hx A hA
  by_cases ht : t = 0
  · subst t
    rw [← s7SuppliedKilledKernel_apply r.pathLaw U hU 0 x hA,
      ← s7SuppliedKilledKernel_apply r'.pathLaw U hU 0 x hA]
    have bridge (G : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1) :
        s7SuppliedKilledKernel G.pathLaw U hU 0 x A =
          gmpKilledEndpointKernel G U hU 0 x A := by
      rw [s7SuppliedKilledKernel_apply G.pathLaw U hU 0 x hA,
        gmpKilledEndpointKernel_apply, Measure.map_apply (measurable_pathPosition 0) hA,
        Measure.restrict_apply ((measurable_pathPosition 0) hA)]
      congr 1
      ext γ
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, pathPosition]
      tauto
    have bridge' (G : GantertFixedEnvironmentRealization hd Λ hΛ ω' hω' lam h0 h1) :
        s7SuppliedKilledKernel G.pathLaw U hU 0 x A =
          gmpKilledEndpointKernel G U hU 0 x A := by
      rw [s7SuppliedKilledKernel_apply G.pathLaw U hU 0 x hA,
        gmpKilledEndpointKernel_apply, Measure.map_apply (measurable_pathPosition 0) hA,
        Measure.restrict_apply ((measurable_pathPosition 0) hA)]
      congr 1
      ext γ
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, pathPosition]
      tauto
    rw [bridge r, bridge' r', gmpKilledEndpointKernel_zero r U hU x,
      gmpKilledEndpointKernel_zero r' U hU x]
  · exact hpart hd Λ hΛ ω ω' hω hω' lam h0 h1 r r' U hU hfields t
      (pos_iff_ne_zero.mpr ht) x hx A hA

end EinsteinFull
