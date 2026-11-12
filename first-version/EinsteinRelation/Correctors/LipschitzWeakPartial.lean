import EinsteinRelation.Calculus.Weak
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

open MeasureTheory Set
open scoped NNReal

namespace EinsteinRelation.Correctors

/-- The actual a.e. derivative of a Lipschitz scalar field is its weak
coordinate derivative. This supplies the bounded initial divergence in
paper/main.tex:850–852, without assuming a weak divergence representative. -/
theorem lipschitzWith_hasWeakPartialDerivative {d : ℕ} {L : ℝ≥0}
    {f : Vec d → ℝ} (hf : LipschitzWith L f) (i : Fin d) :
    HasWeakPartialDerivative univ i f
      (fun x => fderiv ℝ f x (unitVector i)) := by
  have hL_one : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by norm_num
  -- Part 1: f is locally integrable (Lipschitz implies continuous)
  have h_loc_f : LocallyIntegrableOn f univ volume :=
    hf.continuous.locallyIntegrable.locallyIntegrableOn univ
  -- Part 2: the derivative is locally integrable
  have h_loc_fderiv : LocallyIntegrableOn (fun x => fderiv ℝ f x (unitVector i)) univ volume := by
    have h_line : LocallyIntegrable (fun x => lineDeriv ℝ f x (unitVector i)) volume :=
      hf.locallyIntegrable_lineDeriv (unitVector i)
    have h_ae_eq : (fun x => lineDeriv ℝ f x (unitVector i)) =ᵐ[volume]
        (fun x => fderiv ℝ f x (unitVector i)) := by
      filter_upwards [hf.ae_differentiableAt] with x hx
      exact hx.lineDeriv_eq_fderiv (v := unitVector i)
    have h_line_on : LocallyIntegrableOn (fun x => lineDeriv ℝ f x (unitVector i)) univ volume :=
      h_line.locallyIntegrableOn univ
    -- Transfer local integrability via a.e. equality
    intro x hx
    rcases h_line_on x hx with ⟨t, ht, ht_int⟩
    refine ⟨t, ht, ?_⟩
    rwa [integrableOn_congr_fun_ae (ae_restrict_of_ae h_ae_eq)] at ht_int
  -- Part 3: the integral identity
  refine ⟨h_loc_f, h_loc_fderiv, ?_⟩
  intro φ hφ
  have hφ_contDiff : ContDiff ℝ (⊤ : ℕ∞) φ := hφ.1
  have hφ_compact : HasCompactSupport φ := hφ.2.1
  have hφ_diff : Differentiable ℝ φ :=
    hφ_contDiff.differentiable hL_one
  -- Get Lipschitz constant for φ
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hφ_compact hφ_contDiff hL_one
  -- Apply integration by parts for line derivatives
  have h_ibp := hf.integral_lineDeriv_mul_eq (μ := volume) hC hφ_compact (unitVector i)
  -- h_ibp : ∫ x, lineDeriv ℝ f x (unitVector i) * φ x ∂volume =
  --         ∫ x, lineDeriv ℝ φ x (-unitVector i) * f x ∂volume
  -- Convert lineDeriv φ to coordinateDerivative on RHS
  have h_lineDeriv_φ (x : Vec d) : lineDeriv ℝ φ x (-unitVector i) = -coordinateDerivative i φ x := by
    rw [(hφ_diff x).lineDeriv_eq_fderiv (v := -unitVector i), coordinateDerivative,
      ContinuousLinearMap.map_neg]
  have h_rhs : (∫ x, lineDeriv ℝ φ x (-unitVector i) * f x ∂volume) =
      -(∫ x, coordinateDerivative i φ x * f x ∂volume) := by
    calc
      (∫ x, lineDeriv ℝ φ x (-unitVector i) * f x ∂volume)
          = (∫ x, (-coordinateDerivative i φ x) * f x ∂volume) := by
        refine integral_congr_ae (ae_of_all _ (fun x => ?_))
        simp [h_lineDeriv_φ x]
      _ = (∫ x, -(coordinateDerivative i φ x * f x) ∂volume) := by
        refine integral_congr_ae (ae_of_all _ (fun x => ?_))
        ring
      _ = -(∫ x, coordinateDerivative i φ x * f x ∂volume) := by rw [integral_neg]
  -- Convert lineDeriv f to fderiv f on LHS (a.e.)
  have h_ae_eq_fderiv : (fun x => lineDeriv ℝ f x (unitVector i)) =ᵐ[volume]
      (fun x => fderiv ℝ f x (unitVector i)) := by
    filter_upwards [hf.ae_differentiableAt] with x hx
    exact hx.lineDeriv_eq_fderiv (v := unitVector i)
  have h_lhs : (∫ x, lineDeriv ℝ f x (unitVector i) * φ x ∂volume) =
      (∫ x, fderiv ℝ f x (unitVector i) * φ x ∂volume) := by
    exact integral_congr_ae (h_ae_eq_fderiv.mul (ae_of_all _ (fun _ => rfl)))
  -- Combine everything
  calc
    (∫ x in univ, f x * coordinateDerivative i φ x) = (∫ x, f x * coordinateDerivative i φ x) := by
      rw [setIntegral_univ]
    _ = (∫ x, coordinateDerivative i φ x * f x) := by
      refine integral_congr_ae (ae_of_all _ (fun x => ?_))
      ring
    _ = -(∫ x, fderiv ℝ f x (unitVector i) * φ x) := by
      rw [← h_lhs, h_ibp, h_rhs]
      simp
    _ = -(∫ x in univ, fderiv ℝ f x (unitVector i) * φ x) := by rw [setIntegral_univ]

end EinsteinRelation.Correctors
