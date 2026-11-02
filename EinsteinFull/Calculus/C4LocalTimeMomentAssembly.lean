import EinsteinFull.Calculus.C4LocalTimeDerivativeMoment
import EinsteinFull.Calculus.C10LocalTimeForwardDerivativeMoment
import EinsteinFull.Calculus.C10LocalTimeForwardGradientMoment
import EinsteinFull.Calculus.C9LocalTimeTransposeMomentAssembly

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull

/-- The full physical energy is bounded by the sum of its gradient and time
parts. The comparison retains the actual fixed `Lp` representatives. -/
theorem local_time_combined_energy_le
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (t : ℝ≥0) (ρ : ℝ) (hρ : 0 < ρ) (z : Vec d)
    (G : Fin d → Lp ℂ 2 (reducedLaw Q)) (V : Lp ℂ 2 (reducedLaw Q)) :
    ∀ᵐ ω ∂reducedLaw Q,
      localSpatialEnergy Q t ρ hρ z G V ω ≤
        localSpatialEnergy Q t ρ hρ z G 0 ω + localSpatialEnergy Q t ρ hρ z 0 V ω := by
  have hfin : volume {x : Vec d | euclideanNorm (x - z) < ρ} ≠ ⊤ :=
    (ENNReal.toReal_pos_iff.mp (localSpatialEnergy_window_volume z ρ hρ)).2.ne
  filter_upwards [ae_integrableOn_localSpatialEnergy_integrand Q t G V hfin,
    ae_integrableOn_localSpatialEnergy_integrand Q t G 0 hfin,
    ae_integrableOn_localSpatialEnergy_integrand Q t 0 V hfin] with ω hI hG hV
  have hs : localSpatialEnergy Q t ρ hρ z G V ω ^ 2 ≤
      localSpatialEnergy Q t ρ hρ z G 0 ω ^ 2 +
        localSpatialEnergy Q t ρ hρ z 0 V ω ^ 2 := by
    rw [localSpatialEnergy_sq, localSpatialEnergy_sq, localSpatialEnergy_sq,
      ← average_add hG hV]
    simp only [average_eq, measureReal_restrict_apply_univ, smul_eq_mul]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (measureReal_nonneg))
    apply integral_mono hI (hG.add hV)
    intro x
    have hzG : 0 ≤ ∑ j : Fin d, ‖(0 : Fin d → Lp ℂ 2 (reducedLaw Q)) j
        (translate x ω)‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hzV : 0 ≤ (t : ℝ) * ‖(0 : Lp ℂ 2 (reducedLaw Q)) (translate x ω)‖ ^ 2 :=
      mul_nonneg t.property (sq_nonneg _)
    change (∑ j, ‖G j (translate x ω)‖ ^ 2) + (t : ℝ) * ‖V (translate x ω)‖ ^ 2 ≤
      ((∑ j, ‖G j (translate x ω)‖ ^ 2) +
        (t : ℝ) * ‖(0 : Lp ℂ 2 (reducedLaw Q)) (translate x ω)‖ ^ 2) +
      ((∑ j, ‖(0 : Fin d → Lp ℂ 2 (reducedLaw Q)) j (translate x ω)‖ ^ 2) +
        (t : ℝ) * ‖V (translate x ω)‖ ^ 2)
    linarith
  have hE : 0 ≤ localSpatialEnergy Q t ρ hρ z G V ω := Real.sqrt_nonneg _
  have hEG : 0 ≤ localSpatialEnergy Q t ρ hρ z G 0 ω := Real.sqrt_nonneg _
  have hEV : 0 ≤ localSpatialEnergy Q t ρ hρ z 0 V ω := Real.sqrt_nonneg _
  nlinarith [mul_nonneg hEG hEV]

/-- Gradient and derivative moment estimates combine at the same exponent
without changing their actual witnesses. -/
theorem local_time_combined_energy_moment
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (t : ℝ≥0) (ρ : ℝ) (hρ : 0 < ρ) (z : Vec d)
    (G : Fin d → Lp ℂ 2 (reducedLaw Q)) (V : Lp ℂ 2 (reducedLaw Q))
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hG : MemLp (localSpatialEnergy Q t ρ hρ z G 0) p (reducedLaw Q))
    (hV : MemLp (localSpatialEnergy Q t ρ hρ z 0 V) p (reducedLaw Q)) :
    MemLp (localSpatialEnergy Q t ρ hρ z G V) p (reducedLaw Q) ∧
      (eLpNorm (localSpatialEnergy Q t ρ hρ z G V) p (reducedLaw Q)).toReal ≤
        (eLpNorm (localSpatialEnergy Q t ρ hρ z G 0) p (reducedLaw Q)).toReal +
        (eLpNorm (localSpatialEnergy Q t ρ hρ z 0 V) p (reducedLaw Q)).toReal := by
  have hm := localSpatialEnergy_aestronglyMeasurable Q t ρ hρ z G V
  have hdom : ∀ᵐ ω ∂reducedLaw Q,
      ‖localSpatialEnergy Q t ρ hρ z G V ω‖ ≤
        ‖(localSpatialEnergy Q t ρ hρ z G 0 + localSpatialEnergy Q t ρ hρ z 0 V) ω‖ := by
    filter_upwards [local_time_combined_energy_le Q t ρ hρ z G V] with ω hω
    have hE : 0 ≤ localSpatialEnergy Q t ρ hρ z G V ω := Real.sqrt_nonneg _
    have hEG : 0 ≤ localSpatialEnergy Q t ρ hρ z G 0 ω := Real.sqrt_nonneg _
    have hEV : 0 ≤ localSpatialEnergy Q t ρ hρ z 0 V ω := Real.sqrt_nonneg _
    simpa only [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg hE,
      abs_of_nonneg (add_nonneg hEG hEV)] using hω
  have he := (eLpNorm_mono_ae hm hdom).trans (eLpNorm_add_le hp)
  refine ⟨(hG.add hV).mono hm hdom, ?_⟩
  exact (ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
    ⟨hG.eLpNorm_lt_top.ne, hV.eLpNorm_lt_top.ne⟩) he).trans_eq
      (ENNReal.toReal_add hG.eLpNorm_lt_top.ne hV.eLpNorm_lt_top.ne)

/-- Independently chosen endpoint witnesses agree at positive times. This
allows moment estimates to be transported to the common endpoint witnesses. -/
theorem local_time_endpoint_witness_unique
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (ζ : ℂ) (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (ν : EndpointIndex d) (t : ℝ≥0)
    {G H : Fin d → Lp ℂ 2 (reducedLaw Q)} {V W : Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (indexedEndpoint hd Q ν ζ P Pdag β a μ t) G)
    (hH : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (indexedEndpoint hd Q ν ζ P Pdag β a μ t) H)
    (hV : HasDerivAt (fun r : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ r.toNNReal)
      V (t : ℝ))
    (hW : HasDerivAt (fun r : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ r.toNNReal)
      W (t : ℝ)) : G = H ∧ V = W := by
  exact ⟨hG.unique hH, hV.unique hW⟩

/-- Increasing either constant preserves the literal local-time moment
coefficient, including the real power and the signed complex force. -/
theorem local_time_moment_coefficient_mono
    {C C' Cp Cp' t N : ℝ} (ζ : ℂ) (hC : 0 ≤ C) (hCC : C ≤ C')
    (hCp : Cp ≤ Cp') (ht : 0 < t) (hN : 0 ≤ N) :
    C * (1 + ‖ζ‖ * Real.sqrt t) ^ C * t ^ (-(1 / 2 : ℝ)) *
      Real.exp (Cp * ‖ζ‖ ^ 2 * t) * N ≤
    C' * (1 + ‖ζ‖ * Real.sqrt t) ^ C' * t ^ (-(1 / 2 : ℝ)) *
      Real.exp (Cp' * ‖ζ‖ ^ 2 * t) * N := by
  have hA : 1 ≤ 1 + ‖ζ‖ * Real.sqrt t := by
    linarith [mul_nonneg (norm_nonneg ζ) (Real.sqrt_nonneg t)]
  have hpow := Real.rpow_le_rpow_of_exponent_le hA hCC
  have hexp : Real.exp (Cp * ‖ζ‖ ^ 2 * t) ≤ Real.exp (Cp' * ‖ζ‖ ^ 2 * t) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCp (sq_nonneg _)) ht.le
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul (mul_le_mul_of_nonneg_right
      (mul_le_mul hCC hpow (Real.rpow_nonneg (by positivity) _) (hC.trans hCC))
        (Real.rpow_nonneg ht.le _)) hexp (Real.exp_pos _).le
        (mul_nonneg (mul_nonneg (hC.trans hCC)
          (Real.rpow_nonneg (zero_le_one.trans hA) _)) (Real.rpow_nonneg ht.le _))) hN

/-- Two moment estimates can share a single pair of constants; their sum
has the same exponent and time scale with a doubled common prefactor. -/
theorem local_time_moment_coefficients_add
    {C₁ C₂ Cp₁ Cp₂ t N : ℝ} (ζ : ℂ) (hC₁ : 1 ≤ C₁) (hC₂ : 1 ≤ C₂)
    (ht : 0 < t) (hN : 0 ≤ N) :
    C₁ * (1 + ‖ζ‖ * Real.sqrt t) ^ C₁ * t ^ (-(1 / 2 : ℝ)) *
        Real.exp (Cp₁ * ‖ζ‖ ^ 2 * t) * N +
      C₂ * (1 + ‖ζ‖ * Real.sqrt t) ^ C₂ * t ^ (-(1 / 2 : ℝ)) *
        Real.exp (Cp₂ * ‖ζ‖ ^ 2 * t) * N ≤
      (2 * max C₁ C₂) * (1 + ‖ζ‖ * Real.sqrt t) ^ (2 * max C₁ C₂) *
        t ^ (-(1 / 2 : ℝ)) * Real.exp (max Cp₁ Cp₂ * ‖ζ‖ ^ 2 * t) * N := by
  let M := max C₁ C₂
  have hM : 1 ≤ M := hC₁.trans (le_max_left _ _)
  have hleft := local_time_moment_coefficient_mono ζ (zero_le_one.trans hC₁)
    (le_max_left C₁ C₂) (le_max_left Cp₁ Cp₂) ht hN
  have hright := local_time_moment_coefficient_mono ζ (zero_le_one.trans hC₂)
    (le_max_right C₁ C₂) (le_max_right Cp₁ Cp₂) ht hN
  have hpower : (1 + ‖ζ‖ * Real.sqrt t) ^ M ≤
      (1 + ‖ζ‖ * Real.sqrt t) ^ (2 * M) :=
    Real.rpow_le_rpow_of_exponent_le
      (by linarith [mul_nonneg (norm_nonneg ζ) (Real.sqrt_nonneg t)]) (by linarith)
  have hsum :
      2 * (M * (1 + ‖ζ‖ * Real.sqrt t) ^ M * t ^ (-(1 / 2 : ℝ)) *
        Real.exp (max Cp₁ Cp₂ * ‖ζ‖ ^ 2 * t) * N) ≤
      (2 * M) * (1 + ‖ζ‖ * Real.sqrt t) ^ (2 * M) * t ^ (-(1 / 2 : ℝ)) *
        Real.exp (max Cp₁ Cp₂ * ‖ζ‖ ^ 2 * t) * N := by
    calc
      _ = (2 * M) * (1 + ‖ζ‖ * Real.sqrt t) ^ M * t ^ (-(1 / 2 : ℝ)) *
          Real.exp (max Cp₁ Cp₂ * ‖ζ‖ ^ 2 * t) * N := by ring
      _ ≤ _ := by gcongr
  exact (add_le_add hleft hright).trans (by simpa only [← two_mul] using hsum)

/-- Separate moment estimates give the full local energy estimate with constants
chosen before the environment, force, radius, or endpoint witnesses. -/
theorem local_time_combined_energy_moment_bound
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) (ρ : ℝ) (hρ : 0 < ρ) (z : Vec d)
    (G : Fin d → Lp ℂ 2 (reducedLaw Q)) (V : Lp ℂ 2 (reducedLaw Q))
    {p : ℝ≥0∞} (hp : 1 ≤ p) (ζ : ℂ)
    {C₁ C₂ Cp₁ Cp₂ N : ℝ} (hC₁ : 1 ≤ C₁) (hC₂ : 1 ≤ C₂) (hN : 0 ≤ N)
    (hG : MemLp (localSpatialEnergy Q t ρ hρ z G 0) p (reducedLaw Q))
    (hV : MemLp (localSpatialEnergy Q t ρ hρ z 0 V) p (reducedLaw Q))
    (hGb : (eLpNorm (localSpatialEnergy Q t ρ hρ z G 0) p (reducedLaw Q)).toReal ≤
      C₁ * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C₁ * (t : ℝ) ^ (-(1 / 2 : ℝ)) *
        Real.exp (Cp₁ * ‖ζ‖ ^ 2 * (t : ℝ)) * N)
    (hVb : (eLpNorm (localSpatialEnergy Q t ρ hρ z 0 V) p (reducedLaw Q)).toReal ≤
      C₂ * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C₂ * (t : ℝ) ^ (-(1 / 2 : ℝ)) *
        Real.exp (Cp₂ * ‖ζ‖ ^ 2 * (t : ℝ)) * N) :
    MemLp (localSpatialEnergy Q t ρ hρ z G V) p (reducedLaw Q) ∧
      (eLpNorm (localSpatialEnergy Q t ρ hρ z G V) p (reducedLaw Q)).toReal ≤
        (2 * max C₁ C₂) * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ (2 * max C₁ C₂) *
          (t : ℝ) ^ (-(1 / 2 : ℝ)) *
          Real.exp (max Cp₁ Cp₂ * ‖ζ‖ ^ 2 * (t : ℝ)) * N := by
  obtain ⟨hm, hb⟩ := local_time_combined_energy_moment Q t ρ hρ z G V hp hG hV
  exact ⟨hm, hb.trans ((add_le_add hGb hVb).trans
    (local_time_moment_coefficients_add ζ hC₁ hC₂ ht hN))⟩

/-- Moment estimates for independent gradient and derivative witnesses transfer
to any actual witnesses of the same endpoint. -/
theorem local_time_endpoint_energy_moment_bound
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (ζ : ℂ) (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (ν : EndpointIndex d) (t : ℝ≥0) (ht : 0 < (t : ℝ))
    (ρ : ℝ) (hρ : 0 < ρ) (z : Vec d)
    {G H : Fin d → Lp ℂ 2 (reducedLaw Q)} {V W : Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (indexedEndpoint hd Q ν ζ P Pdag β a μ t) G)
    (hH : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (indexedEndpoint hd Q ν ζ P Pdag β a μ t) H)
    (hV : HasDerivAt (fun r : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ r.toNNReal)
      V (t : ℝ))
    (hW : HasDerivAt (fun r : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ r.toNNReal)
      W (t : ℝ))
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    {C₁ C₂ Cp₁ Cp₂ N : ℝ} (hC₁ : 1 ≤ C₁) (hC₂ : 1 ≤ C₂) (hN : 0 ≤ N)
    (hGm : MemLp (localSpatialEnergy Q t ρ hρ z G 0) p (reducedLaw Q))
    (hWm : MemLp (localSpatialEnergy Q t ρ hρ z 0 W) p (reducedLaw Q))
    (hGb : (eLpNorm (localSpatialEnergy Q t ρ hρ z G 0) p (reducedLaw Q)).toReal ≤
      C₁ * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C₁ * (t : ℝ) ^ (-(1 / 2 : ℝ)) *
        Real.exp (Cp₁ * ‖ζ‖ ^ 2 * (t : ℝ)) * N)
    (hWb : (eLpNorm (localSpatialEnergy Q t ρ hρ z 0 W) p (reducedLaw Q)).toReal ≤
      C₂ * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C₂ * (t : ℝ) ^ (-(1 / 2 : ℝ)) *
        Real.exp (Cp₂ * ‖ζ‖ ^ 2 * (t : ℝ)) * N) :
    MemLp (localSpatialEnergy Q t ρ hρ z H V) p (reducedLaw Q) ∧
      (eLpNorm (localSpatialEnergy Q t ρ hρ z H V) p (reducedLaw Q)).toReal ≤
        (2 * max C₁ C₂) * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ (2 * max C₁ C₂) *
          (t : ℝ) ^ (-(1 / 2 : ℝ)) *
          Real.exp (max Cp₁ Cp₂ * ‖ζ‖ ^ 2 * (t : ℝ)) * N := by
  obtain ⟨hGH, hVW⟩ := local_time_endpoint_witness_unique hd Q β a μ ζ P Pdag ν t
    hG hH hV hW
  subst H
  subst W
  exact local_time_combined_energy_moment_bound Q t ht ρ hρ z G V hp ζ
    hC₁ hC₂ hN hGm hWm hGb hWb

/-- The audited forward and clock moment bound holds for every actual time
derivative witness, with its constants fixed before the endpoint data. -/
theorem local_time_forward_derivative_moment_for_witness
    (h0 : node_l_u3A_forced_u2D_local_u23_centered_u2D_sourceStmt)
    (h1 : node_e_u3A_lp_u2D_growthStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (p : ℝ) (hp : 2 ≤ p) :
    ∃ C Cp : ℝ, 1 ≤ C ∧ 0 < Cp ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag →
    ∀ ν : EndpointIndex d, ν ≠ .inr true →
    ∀ (t : ℝ≥0) (ht : 0 < (t : ℝ)) (V : Lp ℂ 2 (reducedLaw Q)),
      HasDerivAt (fun r : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ r.toNNReal)
        V (t : ℝ) →
      MemLp (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8) : FieldPair d → ℂ)
        (ENNReal.ofReal p) (reducedLaw Q) ∧
      ∀ (ρ : ℝ) (x : Vec d) (hρ : Real.sqrt (t : ℝ) ≤ ρ),
        MemLp (localSpatialEnergy Q t ρ (lt_of_lt_of_le (Real.sqrt_pos.mpr ht) hρ)
          x 0 V) (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm (localSpatialEnergy Q t ρ (lt_of_lt_of_le (Real.sqrt_pos.mpr ht) hρ)
          x 0 V) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        C * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C * (t : ℝ) ^ (-(1 / 2 : ℝ)) *
          Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
          (eLpNorm (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8) : FieldPair d → ℂ)
            (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  obtain ⟨C, Cp, hC, hCp, hmoment⟩ :=
    local_time_forward_derivative_moment_of_deps h0 h1 d hd D p hp
  refine ⟨C, Cp, hC, hCp, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hν t ht V hV
  obtain ⟨G, W, hGW, hWm⟩ := hmoment Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hν
  have heq : W t = V := (hGW t ht).2.2.unique hV
  simpa only [heq] using hWm t ht

/-- The forward and clock endpoints satisfy the full local-time energy moment
bound, with one common gradient and derivative witness. -/
theorem local_time_forward_energy_moment_of_deps
  (h0 : EinsteinFull.Blueprint.node_l_u3A_forced_u2D_local_u23_centered_u2D_sourceStmt)
  (h1 : EinsteinFull.Blueprint.node_e_u3A_lp_u2D_growthStmt) :
∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∀ p : ℝ, 2 ≤ p → ∃ C Cp : ℝ, 1 ≤ C ∧ 0 < Cp ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d, ν ≠ .inr true →
    ∃ G : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
    ∃ V : ℝ≥0 → Lp ℂ 2 (reducedLaw Q),
    (∀ t : ℝ≥0, 0 < (t : ℝ) →
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (indexedEndpoint hd Q ν ζ P Pdag β a μ t) (G t) ∧
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (uncenteredEndpoint hd Q ν ζ P Pdag β a μ t) (G t) ∧
      HasDerivAt (fun r : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ r.toNNReal)
        (V t) (t : ℝ)) ∧
    (∀ (t : ℝ≥0) (ht : 0 < (t : ℝ)),
      let U₈ := indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8)
      MemLp (U₈ : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
      (∀ (ρ : ℝ) (x : Vec d) (hρ : Real.sqrt (t : ℝ) ≤ ρ),
        MemLp (localSpatialEnergy Q t ρ (lt_of_lt_of_le (Real.sqrt_pos.mpr ht) hρ) x (G t) (V t)) (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm (localSpatialEnergy Q t ρ (lt_of_lt_of_le (Real.sqrt_pos.mpr ht) hρ) x (G t) (V t))
          (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        C * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C * (t : ℝ) ^ (-(1 / 2 : ℝ)) *
          Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
          (eLpNorm (U₈ : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal)) := by
  intro d hd D p hp
  obtain ⟨Cg, Cpg, hCg, hCpg, hgm⟩ :=
    local_time_forward_gradient_moment_of_deps h0 h1 d hd D p hp
  obtain ⟨Cv, Cpv, hCv, hCpv, hvm⟩ :=
    local_time_forward_derivative_moment_for_witness h0 h1 d hd D p hp
  refine ⟨2 * max Cg Cv, max Cpg Cpv, ?_, hCpg.trans_le (le_max_left _ _), ?_⟩
  · have := hCg.trans (le_max_left Cg Cv)
    linarith
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hν
  obtain ⟨G, V, hGV, hGm⟩ := hgm Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hν
  refine ⟨G, V, hGV, ?_⟩
  intro t ht U₈
  obtain ⟨hu8, hgrad⟩ := hGm t ht
  obtain ⟨_, hder⟩ := hvm Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hν
    t ht (V t) (hGV t ht).2.2
  refine ⟨hu8, ?_⟩
  intro ρ x hρ
  obtain ⟨hGmem, hGb⟩ := hgrad ρ x hρ
  obtain ⟨hVmem, hVb⟩ := hder ρ x hρ
  have hp' : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  exact local_time_combined_energy_moment_bound Q t ht ρ
    (lt_of_lt_of_le (Real.sqrt_pos.mpr ht) hρ) x (G t) (V t) hp' ζ
    hCg hCv ENNReal.toReal_nonneg hGmem hVmem hGb hVb

/-- Every endpoint satisfies the derivative moment with common structural constants. -/
theorem local_time_derivative_moment_of_deps
  (h0 : EinsteinFull.Blueprint.node_l_u3A_forced_u2D_local_u23_centered_u2D_sourceStmt)
  (h1 : EinsteinFull.Blueprint.node_e_u3A_lp_u2D_growthStmt) :
∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∀ p : ℝ, 2 ≤ p → ∃ C Cp : ℝ, 1 ≤ C ∧ 0 < Cp ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
    ∃ G : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
    ∃ V : ℝ≥0 → Lp ℂ 2 (reducedLaw Q),
    (∀ t : ℝ≥0, 0 < (t : ℝ) →
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (indexedEndpoint hd Q ν ζ P Pdag β a μ t) (G t) ∧
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (uncenteredEndpoint hd Q ν ζ P Pdag β a μ t) (G t) ∧
      HasDerivAt (fun r : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ r.toNNReal)
        (V t) (t : ℝ)) ∧
    (∀ (t : ℝ≥0) (ht : 0 < (t : ℝ)),
      let U := indexedEndpoint hd Q ν ζ P Pdag β a μ t
      let U₈ := indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8)
      MemLp (U₈ : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
      (∀ (ρ : ℝ) (x : Vec d) (hρ : Real.sqrt (t : ℝ) ≤ ρ),
        MemLp (localSpatialEnergy Q t ρ (lt_of_lt_of_le (Real.sqrt_pos.mpr ht) hρ) x (0) (V t)) (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm (localSpatialEnergy Q t ρ (lt_of_lt_of_le (Real.sqrt_pos.mpr ht) hρ) x (0) (V t))
          (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        C * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C * (t : ℝ) ^ (-(1 / 2 : ℝ)) *
          Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
          (eLpNorm (U₈ : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal)) := by
  intro d hd D p hp
  obtain ⟨Cf, Cpf, hCf, hCpf, hf⟩ :=
    local_time_forward_derivative_moment_of_deps h0 h1 d hd D p hp
  obtain ⟨Ct, Cpt, hCt, hCpt, htr⟩ :=
    local_time_transpose_derivative_moment_of_deps h0 h1 d hd D p hp
  refine ⟨max Cf Ct, max Cpf Cpt, hCf.trans (le_max_left _ _),
    hCpf.trans_le (le_max_left _ _), ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  by_cases hν : ν = .inr true
  · obtain ⟨G, V, hGV, hm⟩ := htr Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hν
    refine ⟨G, V, hGV, ?_⟩
    intro t ht U U₈
    obtain ⟨hu, he⟩ := hm t ht
    refine ⟨hu, ?_⟩
    intro ρ x hρ
    obtain ⟨hmem, hb⟩ := he ρ x hρ
    exact ⟨hmem, hb.trans (local_time_moment_coefficient_mono ζ
      (by linarith : 0 ≤ Ct) (le_max_right _ _) (le_max_right _ _) ht
      ENNReal.toReal_nonneg)⟩
  · obtain ⟨G, V, hGV, hm⟩ := hf Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hν
    refine ⟨G, V, hGV, ?_⟩
    intro t ht U U₈
    obtain ⟨hu, he⟩ := hm t ht
    refine ⟨hu, ?_⟩
    intro ρ x hρ
    obtain ⟨hmem, hb⟩ := he ρ x hρ
    exact ⟨hmem, hb.trans (local_time_moment_coefficient_mono ζ
      (by linarith : 0 ≤ Cf) (le_max_left _ _) (le_max_left _ _) ht
      ENNReal.toReal_nonneg)⟩

end EinsteinFull.Blueprint
