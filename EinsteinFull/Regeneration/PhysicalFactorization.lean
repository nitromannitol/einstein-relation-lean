import EinsteinFull.PhysicalRegeneration.Regeneration.GantertRegenerationTailProof
import EinsteinFull.PhysicalRegeneration.Calculus.C14S3ConditionIterateFinal
import EinsteinFull.PhysicalRegeneration.Calculus.C7S3IndependenceAssembly
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.W1Queue0315
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.W2Queue0440
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.CLSection3Reductions
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.Proofs.F2PastKernelReduction
import EinsteinFull.PhysicalRegeneration.Calculus.SbxTakeoverFutureKernelReductionR01
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_regen_u2D_tails
import EinsteinFull.Work.W5.StructuralRegenerationMomentsProof

/-!
# The regeneration factorization for the physical diffusion

GMP 2012, Theorem 5.6 (= Shen 2003, Theorem 2.5) regenerates the physical process itself. The
statements of `app:factorization` and of its dependencies hold for the split coupling of the
physical quenched kernel: the regeneration tails come from GMP Lemma 5.8 for that coupling,
and the factorization nodes follow from them as for the reduced kernel.
-/

namespace EinsteinFull.Blueprint

open EinsteinRelation

/-- The regeneration tails (`app:regen-tails`) for the split coupling of the physical kernel,
from GMP Lemma 5.8 for that coupling. -/
theorem node_app_u3A_regen_u2D_tails_phys : node_app_u3A_regen_u2D_tailsStmt_phys := by
  intro d hd Λ₀ r₀
  obtain ⟨l₀, hl₀, hr₀, hG⟩ := External.gantert_regeneration_tail_holds_phys d hd Λ₀ r₀
  refine ⟨l₀, hl₀, hr₀, ?_⟩
  intro l hl δ hδ₀ hδ₁
  obtain ⟨c, C, hc, hC, hGtail⟩ := hG l hl δ hδ₀ hδ₁
  let B : ℝ := (1 + C) / (1 - Real.exp (-(c / 4)))
  have hB : 0 < B := div_pos (by linarith)
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))
  refine ⟨c, C, c / 4, 2 * B, hc, hC, by positivity, by linarith, by positivity, ?_⟩
  intro Q lam h₀ h₁ P K hK
  have hno := (hGtail Q lam h₀ h₁ P K hK).1
  have htau := (hGtail Q lam h₀ h₁ P K hK).2
  have hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0 :=
    ne_of_gt ((ENNReal.ofReal_pos.mpr (by norm_num : (0 : ℝ) < 1 / 2)).trans_le hno)
  have hm := Work.W5.regeneration_first_exponentialMoment_le_of_tail
    hd Q lam l c C h₀ hc hC K hK.1 htau
  have hmD := Work.W5.regenerationConditioned_exponentialMoment_le_of_annealed
    hd Q lam l (c / 4) (1 / 2) B (by norm_num) K hK.1 hD hno 1 hm
  have he : B / (1 / 2) = 2 * B := by ring
  rw [he] at hmD
  exact ⟨hD, hno, htau, hm.trans (ENNReal.ofReal_le_ofReal (by linarith)), hmD⟩

/-- The slices of the first regeneration time, for the physical coupling. -/
theorem node_app_u3A_factorization_u23_slices_phys :
    node_app_u3A_factorization_u23_slicesStmt_phys :=
  node_app_u3A_factorization_u23_slices_of_deps_phys

/-- The past kernel locality, for the physical coupling. -/
theorem node_app_u3A_factorization_u23_past_u2D_kernel_phys :
    node_app_u3A_factorization_u23_past_u2D_kernelStmt_phys :=
  node_app_u3A_factorization_u23_past_u2D_kernel_of_deps_phys

/-- The future kernel locality, for the physical coupling. -/
theorem node_app_u3A_factorization_u23_future_u2D_kernel_phys :
    node_app_u3A_factorization_u23_future_u2D_kernelStmt_phys :=
  node_app_u3A_factorization_u23_future_u2D_kernel_of_deps_phys

/-- The endpoint disintegration, for the physical coupling. -/
theorem node_app_u3A_factorization_u23_endpoint_u2D_disintegration_phys :
    node_app_u3A_factorization_u23_endpoint_u2D_disintegrationStmt_phys :=
  node_app_u3A_factorization_u23_endpoint_u2D_disintegration_of_deps_phys
    node_app_u3A_factorization_u23_slices_phys

/-- The coupling scope, for the physical coupling. -/
theorem node_app_u3A_factorization_u23_coupling_u2D_scope_phys :
    node_app_u3A_factorization_u23_coupling_u2D_scopeStmt_phys :=
  node_app_u3A_factorization_u23_coupling_u2D_scope_of_deps_phys node_app_u3A_regen_u2D_tails_phys

/-- The slice independence and the first marginal, for the physical coupling. -/
theorem node_app_u3A_factorization_u23_independence_phys :
    node_app_u3A_factorization_u23_independenceStmtV2_phys :=
  node_app_u3A_factorization_u23_independence_of_deps_phys
    node_app_u3A_factorization_u23_endpoint_u2D_disintegration_phys
    node_app_u3A_factorization_u23_past_u2D_kernel_phys
    node_app_u3A_factorization_u23_future_u2D_kernel_phys
    node_app_u3A_regen_u2D_tails_phys
    node_app_u3A_factorization_u23_slices_phys
    node_app_u3A_factorization_u23_coupling_u2D_scope_phys

/-- The conditioned factorization and its iteration (`app:factorization`), for the physical
coupling. -/
theorem node_app_u3A_factorization_u23_condition_u2D_iterate_phys :
    node_app_u3A_factorization_u23_condition_u2D_iterateStmt_phys :=
  node_app_u3A_factorization_u23_condition_u2D_iterate_of_deps_phys
    node_app_u3A_factorization_u23_independence_phys
    node_app_u3A_factorization_u23_slices_phys
    node_app_u3A_regen_u2D_tails_phys

end EinsteinFull.Blueprint
