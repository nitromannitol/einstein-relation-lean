import EinsteinFull.Blueprint.G4.node_p_u3A_integration_u23_actual_u2D_kernel_u2D_application
import EinsteinFull.Blueprint.G4.node_finite_u2D_time_u2D_analyticity
import EinsteinFull.Blueprint.G4.node_p_u3A_integration_u23_kernel_u2D_measurability_u2D_reality
import EinsteinFull.Blueprint.G4.node_p_u3A_integration_u23_common_u2D_window_u2D_data
import EinsteinFull.Proofs.KernelIntegration

open MeasureTheory Filter
open scoped Topology NNReal BigOperators

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Apply the proved kernel-integration theorem to the actual clock and each
velocity coordinate using the common structural constants and windows. -/
theorem node_p_u3A_integration_u23_actual_u2D_kernel_u2D_application_of_deps
    (hanalytic : node_finite_u2D_time_u2D_analyticityStmt)
    (hmeasurable : node_p_u3A_integration_u23_kernel_u2D_measurability_u2D_realityStmt)
    (hprofile : node_p_u3A_profileStmt)
    (hcommon : node_p_u3A_integration_u23_common_u2D_window_u2D_dataStmt) :
    node_p_u3A_integration_u23_actual_u2D_kernel_u2D_applicationStmt := by
  classical
  intro d hd D
  obtain ⟨αp, Cp, _hαp, hCp, _hp, _hw⟩ := hprofile d hd D
  obtain ⟨α, C, c, CT, hα, hα4, hC, hc, hCT, Cw, Tw, hCw, hTw, hdata⟩ :=
    hcommon d hd D
  obtain ⟨Co, ls, hCo, hls, hlse, hintegrate⟩ :=
    Proofs.kernel_integration d hd α C c CT hα hα4 hC hc hCT Cw Tw hCw hTw
  refine ⟨Co + Cp, ls, add_pos hCo hCp, hls, hlse, ?_⟩
  intro Q hQ β a μ Z covariance hβ ha hμ hZ hcov P hP
  obtain ⟨hγc, hγC, hamp, hinit, hfixed, hwindow, htail⟩ :=
    hdata Q hQ β a μ Z covariance hβ ha hμ hZ hcov P hP
  obtain ⟨Ca, hCa, hentire⟩ := hanalytic d hd D 0 0 le_rfl le_rfl
  obtain ⟨hv, hj, _hbound⟩ := hentire Q hQ β a μ hβ ha hμ P hP
  obtain ⟨hmv, hmj, hrv, hrj⟩ := hmeasurable d hd D Q hQ β a μ hβ ha hμ P hP
  dsimp only
  let first : Fin d := ⟨0, by omega⟩
  let A := homogenizedCoefficient Q
  let p₀ : ℝ := (2 * Real.pi) ^ (-(d : ℝ) / 2) / Real.sqrt A.det
  let γ : ℝ := A first first / 2
  let u₀ : Option (Fin d) → ℝ := fun κ => match κ with
    | none => 0
    | some i => p₀ / 4 * ∑ j, ∑ k,
        (A⁻¹) j k * covariance (.inl (j, first)) (.inl (k, i))
  let u₂ : Option (Fin d) → ℝ := fun κ => match κ with
    | none => p₀ / 2 * covariance (.inl (first, first)) (.inr ())
    | some i => p₀ / 4 * covariance (.inl (first, first)) (.inl (first, i))
  let K : Option (Fin d) → ℝ → ℂ → ℂ := fun κ t z => match κ with
    | none => clockCorrelation Q first z (P z) β μ t.toNNReal
    | some i => velocityCorrelation Q first i z (P z) β a t.toNNReal
  have hγ : 0 < γ := hc.trans_le hγc
  have hK : ∀ (κ : Option (Fin d)) (t : ℝ), 0 ≤ t → Differentiable ℂ (K κ t) := by
    intro κ t _ht
    cases κ with
    | none => exact hj t.toNNReal
    | some i => exact hv t.toNNReal i
  have hm : ∀ (κ : Option (Fin d)) (z : ℂ), Measurable (fun t : ℝ => K κ t z) := by
    intro κ z
    cases κ with
    | none => exact hmj z
    | some i => exact hmv z i
  have hR : ∀ (κ : Option (Fin d)) (t : ℝ), 0 ≤ t →
      ∀ lam : ℝ, (K κ t (lam : ℂ)).im = 0 := by
    intro κ t _ht lam
    cases κ with
    | none => exact hrj lam t.toNNReal
    | some i => exact hrv lam t.toNNReal i
  have hi := fun κ => hintegrate (u₀ κ) (u₂ κ) γ hγ (K κ) (hamp κ) hγc hγC
    (hK κ) (hm κ) (hR κ) (hinit κ) (hfixed κ)
    (fun C₀ hC₀ => hwindow C₀ hC₀ κ) (htail κ)
  choose hI hcoeff hcrit herror using hi
  have hCo' : Co ≤ Co + Cp := le_add_of_nonneg_right hCp.le
  refine ⟨hγ, hK, hR, hI, fun κ j => (hcoeff κ j).trans hCo',
    fun κ => (hcrit κ).trans hCo', ?_⟩
  intro κ lam h₀ h₁ hsmall
  obtain ⟨hint, herr⟩ := herror κ lam h₀ h₁ hsmall
  refine ⟨hint, herr.trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hCo' (pow_nonneg (abs_nonneg lam) d))
    (Real.exp_nonneg _)

end EinsteinFull.Blueprint
