import EinsteinFull.Blueprint.G4.node_p_u3A_integration_u23_common_u2D_window_u2D_data
import EinsteinFull.Blueprint.Roots.node_p_u3A_tail
import EinsteinFull.Blueprint.G4.node_p_u3A_integration_u23_compact_u2D_extension
import EinsteinFull.Blueprint.G4.node_p_u3A_integration_u23_uniform_u2D_profile_u2D_bounds
import EinsteinFull.Calculus.ComplexSemigroupUniquenessSupport
import EinsteinRelation.Mobility.DriftBoundPointwise
import EinsteinRelation.Correctors.HomogenizedMatrixBounds
import Mathlib.MeasureTheory.Function.Holder

open MeasureTheory Filter
open scoped Topology NNReal BigOperators

namespace EinsteinFull.Blueprint
open EinsteinRelation

private lemma pairing_bound {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (u v : Lp ℂ 2 (reducedLaw Q)) :
    ‖∫ ω, u ω * v ω ∂reducedLaw Q‖ ≤ ‖u‖ * ‖v‖ := by
  have hh := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using Lp.memLp u) (by simpa using Lp.memLp v)
  have hr (w : Lp ℂ 2 (reducedLaw Q)) :
      (∫ ω, ‖w ω‖ ^ (2 : ℝ) ∂reducedLaw Q) ^ (1 / (2 : ℝ)) = ‖w‖ := by
    simp_rw [Real.rpow_two]
    have hn : ‖w‖ ^ 2 = ∫ ω, ‖w ω‖ ^ 2 ∂reducedLaw Q := by
      calc
        ‖w‖ ^ 2 = inner ℝ w w := (real_inner_self_eq_norm_sq w).symm
        _ = ∫ ω, inner ℝ (w ω) (w ω) ∂reducedLaw Q := L2.inner_def w w
        _ = _ := by simp only [real_inner_self_eq_norm_sq]
    rw [← Real.sqrt_eq_rpow, ← hn, Real.sqrt_sq (norm_nonneg _)]
  exact (norm_integral_le_integral_norm _).trans
    (by simpa only [norm_mul, hr] using hh)

private lemma short_time_bound (d : ℕ) (D : StructuralData d) :
    ∃ Ck : ℝ, 0 ≤ Ck ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
      (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ →
    ∀ (i j : Fin d) (z : ℂ)
      (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q i z P →
    ∀ t : ℝ≥0, (t : ℝ) ≤ 1 → ‖z‖ ≤ 2 →
      ‖velocityCorrelation Q i j z P β a t‖ ≤ Ck ∧
      ‖clockCorrelation Q i z P β μ t‖ ≤ Ck := by
  let B := (1 / 2 : ℝ) * d * reducedLipschitzConstant D.ellipticity
  let A := Real.exp (2 * D.ellipticity) * D.ellipticity
  let E := Real.exp (complexForceShift d D.ellipticity (2 : ℂ))
  refine ⟨B * E * (B + 2 * A + 2 * Real.exp (2 * D.ellipticity)), ?_, ?_⟩
  · dsimp [B, A, E, reducedLipschitzConstant]
    have hL := D.one_le_ellipticity
    positivity
  intro Q hQ β a μ hβ ha hμ i j z P hP t ht hz
  letI := reducedLaw_probability Q
  have hL : 0 ≤ D.ellipticity := zero_le_one.trans Q.ellipticity_parameter
  have hB : 0 ≤ B := by dsimp [B, reducedLipschitzConstant]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hb (k : Fin d) : ‖β k‖ ≤ B := by
    suffices hh : ∀ᵐ ω ∂reducedLaw Q, ‖β k ω‖ ≤ B by
      simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound hB hh
    filter_upwards [hβ k, ae_abs_cdiv_le_reduced Q k] with ω hbω hω
    change β k ω = ((1 / 2 : ℝ) * DriftH5.cdiv k ω : ℝ) at hbω
    rw [hbω, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    exact (mul_le_mul_of_nonneg_left hω (by norm_num)).trans_eq (by dsimp [B]; ring)
  have hac : ‖a i j‖ ≤ A := by
    suffices hh : ∀ᵐ ω ∂reducedLaw Q, ‖a i j ω‖ ≤ A by
      simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound hA hh
    filter_upwards [ha i j, Correctors.ae_reducedEnvironmentLaw_origin_elliptic Q] with ω haω hω
    rw [haω, Complex.norm_real, Real.norm_eq_abs]
    apply abs_entry_le_of_quadratic_bounds hA (ω.1 0) (hω 0).1
    · intro ξ
      exact (mul_nonneg (inv_nonneg.mpr hA) (euclideanSq_nonneg_coords ξ)).trans
        ((hω 0).2 ξ).1
    · exact fun ξ => ((hω 0).2 ξ).2
  have hm : ‖μ‖ ≤ Real.exp (2 * D.ellipticity) := by
    suffices hh : ∀ᵐ ω ∂reducedLaw Q, ‖μ ω‖ ≤ Real.exp (2 * D.ellipticity) by
      simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound (Real.exp_nonneg _) hh
    have hh : ∀ᵐ ω ∂reducedLaw Q, |ω.2 0| ≤ Real.exp (2 * D.ellipticity) := by
      apply (ae_map_iff Probability.measurable_reduce.aemeasurable
        (measurableSet_le (((continuous_eval_const (0 : Vec d)).comp
          continuous_snd).abs.measurable) measurable_const)).mpr
      filter_upwards [Q.regular] with ω hω
      change |clockDensity ω 0| ≤ _
      rw [abs_of_pos (clockDensity_pos _ _)]
      exact (clockDensity_bounds ω 0 D.ellipticity (hω.2.1 0)).2
    filter_upwards [hμ, hh] with ω hμω hω
    simpa only [hμω, Complex.norm_real, Real.norm_eq_abs] using hω
  have hp : ‖P t‖ ≤ E := by
    apply (hP.norm_le t).trans
    apply Real.exp_le_exp.mpr
    have hs : complexForceShift d D.ellipticity z ≤
        complexForceShift d D.ellipticity (2 : ℂ) := by
      simp only [complexForceShift, Complex.norm_ofNat]
      gcongr
    exact (mul_le_mul_of_nonneg_right hs t.property).trans
      (mul_le_of_le_one_right (complexForceShift_nonneg Q _) ht)
  have hv : ‖β j + z • a i j‖ ≤ B + 2 * A :=
    (norm_add_le _ _).trans (add_le_add (hb j) (by
      rw [norm_smul]; exact mul_le_mul hz hac (norm_nonneg _) (by norm_num)))
  have hc : ‖z • μ‖ ≤ 2 * Real.exp (2 * D.ellipticity) := by
    rw [norm_smul]; exact mul_le_mul hz hm (norm_nonneg _) (by norm_num)
  constructor
  · exact (pairing_bound Q _ _).trans (by
      calc
        _ ≤ B * (E * (B + 2 * A)) := mul_le_mul (hb i)
          ((P t).le_of_opNorm_le hp _ |>.trans (mul_le_mul_of_nonneg_left hv (by dsimp [E]; positivity)))
          (norm_nonneg _) hB
        _ ≤ _ := by
          rw [← mul_assoc]
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hB (Real.exp_nonneg _))
          exact le_add_of_nonneg_right (by positivity))
  · exact (pairing_bound Q _ _).trans (by
      calc
        _ ≤ B * (E * (2 * Real.exp (2 * D.ellipticity))) := mul_le_mul (hb i)
          ((P t).le_of_opNorm_le hp _ |>.trans (mul_le_mul_of_nonneg_left hc (by dsimp [E]; positivity)))
          (norm_nonneg _) hB
        _ ≤ _ := by
          rw [← mul_assoc]
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hB (Real.exp_nonneg _))
          linarith)

private lemma weaken_profile_bound (d : ℕ) {α α₀ C₀ C t x : ℝ}
    (hα : α ≤ α₀) (hC₀ : 0 ≤ C₀) (hC : C₀ ≤ C) (ht : 1 ≤ t) :
    C₀ * t ^ (-1 - (d : ℝ) / 2 - α₀) * Real.exp (C₀ * x ^ 2) ≤
      C * t ^ (-1 - (d : ℝ) / 2 - α) * Real.exp (C * x ^ 2) := by
  apply mul_le_mul
  · exact mul_le_mul hC (Real.rpow_le_rpow_of_exponent_le ht (by linarith))
      (Real.rpow_nonneg (zero_le_one.trans ht) _) (hC₀.trans hC)
  · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hC (sq_nonneg _))
  · exact (Real.exp_pos _).le
  · exact mul_nonneg (hC₀.trans hC) (Real.rpow_nonneg (zero_le_one.trans ht) _)

/-- Assemble structural windows for all actual clock and velocity kernels. -/
theorem node_p_u3A_integration_u23_common_u2D_window_u2D_data_of_deps
    (hprofile : node_p_u3A_profileStmt)
    (htail : node_p_u3A_tailStmt)
    (hextension : node_p_u3A_integration_u23_compact_u2D_extensionStmt)
    (huniform : node_p_u3A_integration_u23_uniform_u2D_profile_u2D_boundsStmt) :
    node_p_u3A_integration_u23_common_u2D_window_u2D_dataStmt := by
  classical
  intro d hd D
  obtain ⟨αp, Cp, hαp, _hCp, _hp, hw⟩ := hprofile d hd D
  obtain ⟨αe, Ce, hαe, hαe4, hCe, he⟩ := hextension d hd D
  obtain ⟨Ct, ct, CT, hCt, hct, hCT, ht⟩ := htail d hd D
  obtain ⟨cb, B, hcb, hB, hb⟩ := huniform d hd D
  obtain ⟨Ck, hCk, hk⟩ := short_time_bound d D
  have hw' : ∀ C₀ : ℝ, ∃ Cw Tw : ℝ, 0 < Cw ∧ 4 ≤ Tw ∧
      (0 < C₀ → ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
      (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
      (covariance : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → IsJointObservation Q Z →
      IsJointCovariance Q Z covariance →
      ∀ t : ℝ≥0, Tw ≤ (t : ℝ) → ∀ lam : ℝ,
      |lam| * Real.sqrt (t : ℝ) ≤ C₀ * Real.log (Real.sqrt (t : ℝ)) ^ (1 / 4 : ℝ) →
      ∀ P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ (lam : ℂ) P → ∀ i : Fin d,
        ‖velocityCorrelation Q ⟨0, by omega⟩ i (lam : ℂ) P β a t -
          (((t : ℝ) ^ (-1 - (d : ℝ) / 2) : ℝ) : ℂ) *
            velocityGaussianProfile hd Q covariance i ((lam : ℂ) * (Real.sqrt (t : ℝ) : ℂ))‖ +
        ‖clockCorrelation Q ⟨0, by omega⟩ (lam : ℂ) P β μ t -
          (((t : ℝ) ^ (-1 - (d : ℝ) / 2) : ℝ) : ℂ) *
            clockGaussianProfile hd Q covariance ((lam : ℂ) * (Real.sqrt (t : ℝ) : ℂ))‖ ≤
          Cw * (t : ℝ) ^ (-1 - (d : ℝ) / 2 - αp) *
            Real.exp (Cw * (1 + |lam| * Real.sqrt (t : ℝ)) ^ 2)) := by
    intro C₀
    by_cases hC₀ : 0 < C₀
    · obtain ⟨Cw, Tw, hwpos, hTw, hw⟩ := hw C₀ hC₀
      exact ⟨Cw, Tw, hwpos, hTw, fun _ => hw⟩
    · exact ⟨1, 4, zero_lt_one, le_rfl, fun h => (hC₀ h).elim⟩
  choose Cw Tw hCw hTw hw using hw'
  let α := min αp αe
  let C := Ce + Ct + B + Ck + 1
  let c := min cb ct
  have hα : 0 < α := lt_min hαp hαe
  have hCeC : Ce ≤ C := by dsimp [C]; linarith
  have hCtC : Ct ≤ C := by dsimp [C]; linarith
  have hBC : B ≤ C := by dsimp [C]; linarith
  have hCkC : Ck ≤ C := by dsimp [C]; linarith
  have hC : 0 < C := lt_of_lt_of_le hCe hCeC
  have hc : 0 < c := lt_min hcb hct
  refine ⟨α, C, c, CT, hα, (min_le_right _ _).trans hαe4, hC, hc, hCT,
    Cw, Tw, (fun C₀ _ => hCw C₀), (fun C₀ _ => by linarith [hTw C₀]), ?_⟩
  intro Q hQ β a μ Z covariance hβ ha hμ hZ hcov P hP
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
  change c ≤ γ ∧ γ ≤ C ∧ (∀ κ, |u₀ κ| + |u₂ κ| ≤ C) ∧
    (∀ κ t, 0 ≤ t → t ≤ 1 → ∀ z, ‖z‖ ≤ 2 → ‖K κ t z‖ ≤ C) ∧
    (∀ κ t, 1 ≤ t → ∀ z, ‖z‖ * Real.sqrt t ≤ 2 →
      ‖kernelProfileRemainder d (u₀ κ) (u₂ κ) γ (K κ) t z‖ ≤
        C * t ^ (-1 - (d : ℝ) / 2 - α) * Real.exp (C * (1 + ‖z‖ * Real.sqrt t) ^ 2)) ∧
    (∀ C₀, 0 < C₀ → ∀ κ t, Tw C₀ ≤ t → ∀ lam,
      |lam| * Real.sqrt t ≤ C₀ * Real.log (Real.sqrt t) ^ (1 / 4 : ℝ) →
      ‖kernelProfileRemainder d (u₀ κ) (u₂ κ) γ (K κ) t (lam : ℂ)‖ ≤
        Cw C₀ * t ^ (-1 - (d : ℝ) / 2 - α) *
          Real.exp (Cw C₀ * (1 + |lam| * Real.sqrt t) ^ 2)) ∧
    (∀ κ lam, 0 < |lam| → |lam| ≤ Real.exp (-1) → ∀ t, CT / |lam| ^ 2 ≤ t →
      ‖K κ t (lam : ℂ)‖ ≤ C * |lam| ^ (d + 2) *
        Real.exp (C * Real.sqrt (Real.log (1 / |lam|)) - c * lam ^ 2 * t))
  have hb' := hb Q hQ Z covariance hZ hcov
  change cb ≤ γ ∧ γ ≤ B ∧ ∀ κ, |u₀ κ| + |u₂ κ| ≤ B ∧
    ∀ z, (match κ with
      | none => clockGaussianProfile hd Q covariance z
      | some i => velocityGaussianProfile hd Q covariance i z) =
        complexGaussianProfile (u₀ κ) (u₂ κ) γ z at hb'
  obtain ⟨hcbγ, hγB, hu⟩ := hb'
  refine ⟨(min_le_left _ _).trans hcbγ, hγB.trans hBC,
    fun κ => (hu κ).1.trans hBC, ?_, ?_, ?_, ?_⟩
  · intro κ t ht0 ht1 z hz
    have hk' := hk Q hQ β a μ hβ ha hμ first
    cases κ with
    | none => exact ((hk' first z (P z) (hP z) t.toNNReal
        (by simpa only [Real.coe_toNNReal t ht0] using ht1) hz).2).trans hCkC
    | some i => exact ((hk' i z (P z) (hP z) t.toNNReal
        (by simpa only [Real.coe_toNNReal t ht0] using ht1) hz).1).trans hCkC
  · intro κ t ht1 z hz
    exact (he Q hQ β a μ Z covariance hβ ha hμ hZ hcov P hP κ t ht1 z hz).trans
      (weaken_profile_bound d (min_le_right _ _) hCe.le hCeC ht1)
  · intro C₀ hC₀ κ t htt lam hlam
    have ht1 : 1 ≤ t := by linarith [hTw C₀]
    have ht0 : 0 ≤ t := zero_le_one.trans ht1
    have hw' := hw C₀ hC₀ Q hQ β a μ Z covariance hβ ha hμ hZ hcov
      t.toNNReal (by simpa only [Real.coe_toNNReal t ht0] using htt) lam
      (by simpa only [Real.coe_toNNReal t ht0] using hlam) (P (lam : ℂ)) (hP _)
    have hn := (hu κ).2 ((lam : ℂ) * (Real.sqrt t : ℂ))
    have hbound : ‖kernelProfileRemainder d (u₀ κ) (u₂ κ) γ (K κ) t (lam : ℂ)‖ ≤
        Cw C₀ * t ^ (-1 - (d : ℝ) / 2 - αp) *
          Real.exp (Cw C₀ * (1 + |lam| * Real.sqrt t) ^ 2) := by
      cases κ with
      | none =>
        have hh := (le_add_of_nonneg_left (norm_nonneg _)).trans (hw' first)
        simpa only [kernelProfileRemainder, if_pos ht1, K,
          Real.coe_toNNReal t ht0, hn] using hh
      | some i =>
        have hh := (le_add_of_nonneg_right (norm_nonneg _)).trans (hw' i)
        simpa only [kernelProfileRemainder, if_pos ht1, K,
          Real.coe_toNNReal t ht0, hn] using hh
    exact hbound.trans (weaken_profile_bound d (min_le_left _ _) (hCw C₀).le le_rfl ht1)
  · intro κ lam hlam hlam1 t htt
    have ht0 : 0 ≤ t := le_trans (by positivity) htt
    have ht' := ht Q hQ β a μ hβ ha hμ lam hlam hlam1 (P (lam : ℂ)) (hP _)
      t.toNNReal (by simpa only [Real.coe_toNNReal t ht0] using htt)
    have hbound : ‖K κ t (lam : ℂ)‖ ≤ Ct * |lam| ^ (d + 2) *
        Real.exp (Ct * Real.sqrt (Real.log (1 / |lam|)) - ct * lam ^ 2 * t) := by
      cases κ with
      | none => simpa only [K, Real.coe_toNNReal t ht0] using (ht' first).2
      | some i => simpa only [K, Real.coe_toNNReal t ht0] using (ht' i).1
    apply hbound.trans
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right hCtC (pow_nonneg (abs_nonneg _) _)
    · apply Real.exp_le_exp.mpr
      exact sub_le_sub (mul_le_mul_of_nonneg_right hCtC (Real.sqrt_nonneg _))
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (min_le_right cb ct) (sq_nonneg lam)) ht0)
    · exact (Real.exp_pos _).le
    · positivity

end EinsteinFull.Blueprint
