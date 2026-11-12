import EinsteinRelation.External.AKMCorrectorOscillation
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! Source: `paper/main.tex:722,756`. Genuine integrability on arbitrary
finite positive time windows follows by restriction from the source mesh. -/
open MeasureTheory
open Set
open Filter

noncomputable section
namespace EinsteinRelation.Correctors

open External.AKM HeatSelectedSkewMeaning

/-- Every compact positive-time window inherits both genuine integrals
from a larger original cutoff window. The endpoints need not be integers. -/
theorem heat_selected_integrable_positive_window {d : ℕ}
    {g : Vec d → Vec d} {G : Fin d → Fin d → Vec d → Vec d}
    (h : IsHeatSelectedFluxGradient g G) (j k l : Fin d) (R : ℕ)
    (a b : ℝ) (ha : 0 < a) :
    ∀ᵐ x ∂(volume.restrict (ball 0 ((R : ℝ) + 1))),
      (∀ᵐ t ∂(volume.restrict (Set.Icc a b)),
        Integrable (fun y => akmHeatGradientDensity g t j k l x y) volume) ∧
      Integrable (fun t => akmHeatGradientSpaceIntegral g t j k l x)
        (volume.restrict (Set.Icc a b)) := by
  have ha_inv_pos : 0 < a⁻¹ := inv_pos.mpr ha
  obtain ⟨N, hN⟩ := exists_nat_gt a⁻¹
  have hNpos : 0 < (N : ℝ) := by linarith
  have h_inv_lt_a : ((N : ℝ)⁻¹) < a := by
    have htemp : 1 / (N : ℝ) < 1 / (a⁻¹) :=
      (one_div_lt_one_div hNpos ha_inv_pos).mpr hN
    have h_one_div_inv : 1 / (a⁻¹) = a := by field_simp [ha.ne.symm]
    rw [h_one_div_inv] at htemp
    simpa [one_div] using htemp
  have h_m_ineq : ((N + 1 : ℕ) : ℝ)⁻¹ ≤ a := by
    have hpos_N1 : 0 < ((N + 1 : ℕ) : ℝ) := by
      have hpos_nat : 0 < (N + 1 : ℕ) := Nat.succ_pos N
      exact Nat.cast_pos.mpr hpos_nat
    have h_lt : ((N + 1 : ℕ) : ℝ)⁻¹ < ((N : ℝ)⁻¹) := by
      have h_cast_lt : (N : ℝ) < ((N + 1 : ℕ) : ℝ) := by
        push_cast
        exact_mod_cast Nat.lt_succ_self N
      simpa [one_div] using (one_div_lt_one_div hpos_N1 hNpos).mpr h_cast_lt
    linarith
  obtain ⟨M, hM⟩ := exists_nat_gt b
  have h_n_ineq : b ≤ ((M + 1 : ℕ) : ℝ) := by
    have h_lt : b < ((M + 1 : ℕ) : ℝ) := by
      have hM_cast_lt : (M : ℝ) < ((M + 1 : ℕ) : ℝ) := by
        push_cast
        exact_mod_cast Nat.lt_succ_self M
      linarith
    linarith
  let T := Set.Icc (((N + 1 : ℕ) : ℝ)⁻¹) ((M + 1 : ℕ) : ℝ)
  have h_subset : Set.Icc a b ⊆ T := by
    intro t ht
    rcases ht with ⟨ht_left, ht_right⟩
    refine ⟨by linarith, by linarith⟩
  have h_mn := h j k l R
  rcases h_mn with ⟨h_forall_mn, _⟩
  have h_NM := h_forall_mn N M
  refine h_NM.mono fun x hx => ?_
  rcases hx with ⟨hx_t, hx_int⟩
  have hx_t' : ∀ᵐ t ∂(volume.restrict (Set.Icc a b)),
      Integrable (fun y => akmHeatGradientDensity g t j k l x y) volume :=
    ae_restrict_of_ae_restrict_of_subset (fun t ht => h_subset ht) hx_t
  have hx_int' : Integrable (fun t => akmHeatGradientSpaceIntegral g t j k l x)
      (volume.restrict (Set.Icc a b)) :=
    IntegrableOn.mono_set hx_int h_subset
  exact ⟨hx_t', hx_int'⟩

end EinsteinRelation.Correctors
