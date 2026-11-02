import EinsteinFull.Calculus.C3DyadicGainL2Extraction
import EinsteinFull.Calculus.C10DyadicFluxWeightCompression
import EinsteinFull.Calculus.C10DyadicWeightedAverageStep
import EinsteinFull.Blueprint.Foundation.Proofs.W2CenteredEquations
import EinsteinFull.Work.W2.CorrectorReuseSupport

open EinsteinRelation EinsteinFull MeasureTheory
open scoped NNReal ENNReal Topology
namespace EinsteinFull.Blueprint

theorem c14_dyadic_actual_average_improvement (hlocal : node_l_u3A_forced_u2D_localStmt) (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (b : ℝ) (hb : 0 < b) : ∃ ε growth₀ T₀ E : ℝ, 0 < ε ∧ 0 < growth₀ ∧ 8 ≤ T₀ ∧ 0 ≤ E ∧ ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)), IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ → ∀ ζ : ℂ, ∀ (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)), IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P → IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d, ∀ T t growth K Kp : ℝ, T₀ ≤ T → T ≤ t → t ≤ 2*T → ‖ζ‖ * Real.sqrt t ≤ 1 → growth₀ ≤ growth → 1 ≤ K → 1 ≤ Kp → (∀ r : ℝ≥0, 1 ≤ (r : ℝ) → (r : ℝ) ≤ T → ‖indexedEndpoint hd Q ν ζ P Pdag β a μ r‖ ≤ Kp * (Real.exp (growth * ‖ζ‖^2 * (r : ℝ)) * ((r : ℝ) ^ (-(1/2+(d : ℝ)/4)) + ‖ζ‖ * (r : ℝ) ^ (-(d : ℝ)/4)))) → ∀ s : ℝ, b*t ≤ s → ∀ hs : 0 < s, ‖gaussianAverage hd Q s hs (indexedEndpoint hd Q ν ζ P Pdag β a μ (t/2).toNNReal)‖ ≤ K * Real.exp (growth*‖ζ‖^2*(t/2)) * ((s) ^ (-(1/2+(d : ℝ)/4)) + ‖ζ‖ * (s) ^ (-(d : ℝ)/4)) → ‖gaussianAverage hd Q s hs (indexedEndpoint hd Q ν ζ P Pdag β a μ t.toNNReal)‖ ≤ (K + E*T^(-ε)*Kp) * Real.exp (growth*‖ζ‖^2*t) * ((s) ^ (-(1/2+(d : ℝ)/4)) + ‖ζ‖ * (s) ^ (-(d : ℝ)/4)) := by
  obtain ⟨ε, g₀, t₀, C, L, hε, hg₀, ht₀, hC, hgain⟩ :=
    c3_dyadic_actual_L2_flux_gain hlocal d hd D
  let M := max ((d : ℝ) / 2 * C 1 * (1 + b⁻¹) ^ L 1) (C 0 * (1 + b⁻¹) ^ L 0)
  have hM : 0 ≤ M := by
    dsimp [M]
    have hc0 := (hC 0).le
    have hc1 := (hC 1).le
    positivity
  let T₀ := max 16 (max (2 * t₀) (1 / b))
  let growth₀ := max g₀ (sourceReducedBound D.ellipticity)
  refine ⟨ε, growth₀, T₀, 2 ^ ε * M, hε, ?_, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le hg₀ (le_max_left _ _)
  · exact le_trans (by norm_num) (le_max_left _ _)
  · positivity
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν T t growth K Kp hT ht ht2 hforce hg hK hKp hpoint s hbs hs hinit
  have hT16 : 16 ≤ T := le_trans (le_max_left _ _) hT
  have htt₀ : 2 * t₀ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hTb : 1 / b ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
  have htpos : 0 < t := by linarith
  have hsone : 1 ≤ s := by have := (div_le_iff₀ hb).mp hTb; nlinarith
  have hgpos : 0 ≤ growth := le_trans (le_of_lt hg₀) (le_trans (le_max_left _ _) hg)
  have hrate : sourceReducedBound D.ellipticity ≤ growth := le_trans (le_max_right _ _) hg
  obtain ⟨G, J, hflux, hder⟩ := hgain Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  have hcoef : |homogenizedCoefficient Q ⟨0, by omega⟩ ⟨0, by omega⟩| ≤ growth := by
    have hc := PiLp.norm_apply_le (WithLp.toLp 2 ((homogenizedCoefficient Q).mulVec (unitVector ⟨0, by omega⟩))) ⟨0, by omega⟩
    rw [← TimeChange.euclideanNorm_eq_norm_toLp] at hc
    have hh := hc.trans (homogenizedCoefficient_column_bound Q ⟨0, by omega⟩)
    have hh' : |homogenizedCoefficient Q ⟨0, by omega⟩ ⟨0, by omega⟩| ≤ sourceReducedBound D.ellipticity := by
      simpa [Matrix.mulVec, dotProduct, unitVector, Pi.single_apply, Real.norm_eq_abs] using hh
    exact hh'.trans hrate
  have hfluxbound : ∀ r ∈ Set.Ioo (t/2) t, ‖c3BootstrapFluxVector hd Q ν ζ J s hs t r‖ ≤ M * Kp * Real.exp (growth * ‖ζ‖ ^ 2 * t) * (t/2) ^ (-1-ε) * (s ^ (-(1/2+(d : ℝ)/4)) + ‖ζ‖ * s ^ (-(d : ℝ)/4)) := by
    intro r hr
    have hrpos : 0 < r := by linarith [hr.1]
    have hr₀ : t₀ ≤ r := by linarith [hr.1]
    have hrforce : ‖ζ‖ * Real.sqrt r ≤ 1 := by
      exact le_trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hr.2.le) (norm_nonneg ζ)) hforce
    have hr8 : 1 ≤ r / 8 := by linarith [hr.1]
    have hr8T : r / 8 ≤ T := by linarith [hr.2]
    let u : ℝ≥0 := r.toNNReal / 8
    have hu : (u : ℝ) = r / 8 := by simp [u, Real.toNNReal_of_nonneg hrpos.le]
    have hpoint' := hpoint u (by rw [hu]; exact hr8) (by rw [hu]; exact hr8T)
    have hd' := hder r.toNNReal (by simpa [Real.toNNReal_of_nonneg hrpos.le] using hr₀)
      (by simpa [Real.toNNReal_of_nonneg hrpos.le] using hrforce) growth Kp
      (le_trans (le_max_left _ _) hg) hKp
      (Lp.memLp _) (by
        simpa [u, hu, Lp.norm_def, Real.toNNReal_of_nonneg hrpos.le, mul_div_assoc, mul_assoc] using hpoint') s hsone hs
    have hbnd := c10_dyadic_flux_common_weight_bound hd Q ν ζ J s hs t r b ε growth Kp L C
      htpos hr.1.le hr.2.le hb hbs hε.le (by linarith) (fun k => (hC k).le) hgpos hrate
      (by simpa [Real.toNNReal_of_nonneg hrpos.le] using hd')
    convert hbnd using 1 <;> dsimp [M] <;> ring
  have h := c10_dyadic_weighted_average_step node_e_u3A_centered_u2D_equations_of_deps hd D Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν G J hflux s hs t T growth ε K Kp M (by linarith) ht hgpos hε.le (by linarith) (by linarith) hM hcoef hinit hfluxbound
  simpa [mul_assoc] using h

end EinsteinFull.Blueprint
