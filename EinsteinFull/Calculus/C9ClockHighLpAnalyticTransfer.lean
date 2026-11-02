import EinsteinFull.Calculus.ComplexHighExponentAnalyticSupport
import EinsteinFull.Calculus.C9AnalyticClockGradientFlux

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull

/-- Local higher moments lift an entire L2 orbit to its actual finite-p representatives. -/
theorem clock_highLp_analytic_transfer_of_local_moments
    {d : ℕ} {Λ R : ℝ} (Q : EnvironmentLaw d Λ R)
    (p q : ℝ) (hp : 2 ≤ p) (hpq : p < q) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
    ∀ F : ℂ → Lp ℂ 2 (reducedLaw Q),
      (∀ z, AnalyticAt ℂ F z) →
      (∀ z₀ : ℂ, ∃ δ K : ℝ, 0 < δ ∧ 0 ≤ K ∧
        ∀ z : ℂ, ‖z - z₀‖ < δ →
          MemLp (F z : FieldPair d → ℂ) (ENNReal.ofReal q) (reducedLaw Q) ∧
          eLpNorm (F z : FieldPair d → ℂ) (ENNReal.ofReal q) (reducedLaw Q) ≤
            ENNReal.ofReal K) →
      ∃ Fp : ℂ → Lp ℂ (ENNReal.ofReal p) (reducedLaw Q),
        (∀ z, (Fp z : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
          (F z : FieldPair d → ℂ)) ∧ Differentiable ℂ Fp := by
  classical
  let := reducedLaw_probability Q
  let : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  intro F hF hmom
  have hp2 : (2 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    exact_mod_cast ENNReal.ofReal_le_ofReal hp
  have hmem (z : ℂ) : MemLp (F z : FieldPair d → ℂ)
      (ENNReal.ofReal p) (reducedLaw Q) := by
    obtain ⟨δ, K, hδ, _, hb⟩ := hmom z
    exact (hb z (by simpa only [sub_self, norm_zero] using hδ)).1.mono_exponent
      (ENNReal.ofReal_le_ofReal hpq.le)
  let Fp (z : ℂ) : Lp ℂ (ENNReal.ofReal p) (reducedLaw Q) := (hmem z).toLp (F z)
  have hae (z : ℂ) : (Fp z : FieldPair d → ℂ) =ᵐ[reducedLaw Q] F z :=
    (hmem z).coeFn_toLp
  have hinc (z : ℂ) : complexLpToL2 (reducedLaw Q) hp2 (Fp z) = F z := by
    apply Lp.ext
    exact hae z
  have hcF : Continuous F := continuous_iff_continuousAt.mpr (fun z => (hF z).continuousAt)
  have hc : Continuous Fp := by
    apply continuous_iff_continuousAt.mpr
    intro z₀
    obtain ⟨δ, K, hδ, _, hb⟩ := hmom z₀
    have hcball : Continuous (fun z : Metric.ball z₀ δ => Fp z) := by
      apply continuous_highLp_of_L2_of_bound hp hpq _
        (M := fun _ => K) (hM := continuous_const)
      · simpa only [hinc, Function.comp_def] using hcF.comp continuous_subtype_val
      · intro z
        rw [eLpNorm_congr_ae (hae z)]
        exact (hb z (by simpa only [Metric.mem_ball, dist_eq_norm] using z.property)).2
    exact (continuousOn_iff_continuous_domRestrict.mpr hcball).continuousAt
      (Metric.ball_mem_nhds z₀ hδ)
  refine ⟨Fp, hae, ?_⟩
  apply differentiable_of_injective_clm_comp (complexLpToL2CLM (reducedLaw Q) hp2)
    (complexLpToL2_injective (reducedLaw Q) hp2) hc
  have heq : (fun z => complexLpToL2CLM (reducedLaw Q) hp2 (Fp z)) = F := by
    funext z
    exact hinc z
  rw [heq]
  exact fun z => (hF z).differentiableAt

end EinsteinFull.Blueprint
