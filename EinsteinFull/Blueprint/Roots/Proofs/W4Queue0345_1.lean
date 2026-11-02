import EinsteinFull.Blueprint.G4.node_p_u3A_response_u23_core_u2D_extension
import EinsteinFull.Blueprint.G4.node_p_u3A_response_u23_cesaro_u2D_abel
import EinsteinFull.Blueprint.G4.Proofs.W2Queue0158_2
import EinsteinRelation.Diffusion.Velocity

open MeasureTheory Filter
open scoped Topology NNReal

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation
open W2CoreExtension

private theorem response_drift_bound {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    (j : Fin d) :
    ∀ᵐ ω ∂reducedLaw Q, ‖β j ω‖ ≤ (1 / 2 : ℝ) * d * reducedLipschitzConstant D.ellipticity := by
  have hb := ae_abs_cdiv_le_reduced Q j
  change ∀ᵐ ω ∂reducedLaw Q, |DriftH5.cdiv j ω| ≤ _ at hb
  filter_upwards [hβ j, hb] with ω hω hbω
  rw [hω, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  exact (mul_le_mul_of_nonneg_left hbω (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans_eq
    (mul_assoc _ _ _).symm

private theorem response_coefficient_bound {d : ℕ} {Λ r : ℝ}
    {Q : EnvironmentLaw d Λ r} {a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)}
    (ha : IsReducedCoefficientObservation Q a) (i j : Fin d) :
    ∀ᵐ ω ∂reducedLaw Q, ‖a i j ω‖ ≤ Real.exp (2 * Λ) * Λ := by
  have hK := mul_nonneg (Real.exp_pos (2 * Λ)).le (zero_le_one.trans Q.ellipticity_parameter)
  filter_upwards [ha i j, Correctors.ae_reducedEnvironmentLaw_origin_elliptic Q] with ω hω he
  rw [hω, Complex.norm_real, Real.norm_eq_abs]
  apply abs_entry_le_of_quadratic_bounds hK (ω.1 0) (he 0).1
  · intro ξ
    exact (mul_nonneg (inv_nonneg.mpr hK) (euclideanSq_nonneg_coords ξ)).trans ((he 0).2 ξ).1
  · exact fun ξ => ((he 0).2 ξ).2

private theorem response_clock_bound {d : ℕ} {Λ r : ℝ}
    {Q : EnvironmentLaw d Λ r} {μ : Lp ℂ 2 (reducedLaw Q)}
    (hμ : IsReducedClockObservation Q μ) :
    ∀ᵐ ω ∂reducedLaw Q, ‖μ ω‖ ≤ Real.exp (2 * Λ) := by
  have hb : ∀ᵐ ω ∂reducedLaw Q, ‖(ω.2 0 : ℂ)‖ ≤ Real.exp (2 * Λ) := by
    apply (ae_map_iff Probability.measurable_reduce.aemeasurable
      (isClosed_le (continuous_norm.comp (Complex.continuous_ofReal.comp
        ((continuous_eval_const (0 : Vec d)).comp continuous_snd))) continuous_const).measurableSet).mpr
    filter_upwards [Q.regular] with ω hω
    change ‖(clockDensity ω 0 : ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (clockDensity_pos ω 0)]
    exact (clockDensity_bounds ω 0 Λ (hω.2.1 0)).2
  filter_upwards [hμ, hb] with ω hω hbω
  rwa [hω]

private theorem real_mean {d : ℕ} {L r : ℝ} (Q : EnvironmentLaw d L r)
    (f : Lp ℂ 2 (reducedLaw Q))
    (hf : ∀ᵐ ω ∂reducedLaw Q, (f ω).im = 0) :
    (∫ ω, f ω ∂reducedLaw Q) = (∫ ω, (f ω).re ∂reducedLaw Q : ℝ) := by
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [hf] with ω hω
  exact Complex.ext rfl (by simpa only [Complex.ofReal_im] using hω)

private theorem drift_mean_zero {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    (i : Fin d) : (∫ ω, β i ω ∂reducedLaw Q) = 0 := by
  letI := reducedLaw_probability Q
  have hh := hβ.integral_mul i (Lp.const 2 (reducedLaw Q) 1) (fun _ => 0)
    (hasComplexHorizontalGradient_const (reducedLaw Q) (reducedLaw_stationary Q) 1)
  have hl : (∫ ω, β i ω * (Lp.const 2 (reducedLaw Q) (1 : ℂ)) ω ∂reducedLaw Q) =
      ∫ ω, β i ω ∂reducedLaw Q := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_const 2 (reducedLaw Q) (1 : ℂ)] with ω hω
    simp only [hω, Function.const_apply, mul_one]
  rw [hl] at hh
  have hz : (∫ ω, ∑ k : Fin d, (ω.1 0 k i : ℂ) * (0 : Lp ℂ 2 (reducedLaw Q)) ω
      ∂reducedLaw Q) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [Lp.coeFn_zero ℂ 2 (reducedLaw Q)] with ω hω
    simp only [hω, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  simpa only [hz, mul_zero] using hh

private theorem mean_add_smul {d : ℕ} {L r : ℝ} (Q : EnvironmentLaw d L r)
    (f g : Lp ℂ 2 (reducedLaw Q)) (z : ℂ) :
    (∫ ω, (f + z • g) ω ∂reducedLaw Q) =
      (∫ ω, f ω ∂reducedLaw Q) + z * ∫ ω, g ω ∂reducedLaw Q := by
  letI := reducedLaw_probability Q
  calc
    _ = ∫ ω, f ω + z * g ω ∂reducedLaw Q := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_add f (z • g), Lp.coeFn_smul z g] with ω ha hs
      simp only [ha, Pi.add_apply, hs, Pi.smul_apply, smul_eq_mul]
    _ = _ := by
      rw [integral_add ((Lp.memLp f).integrable (by norm_num))
        (((Lp.memLp g).integrable (by norm_num)).const_mul z), integral_const_mul]


private theorem abel_pair_limit {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    {i : Fin d} {lam : ℝ} (hlam : lam ≠ 0)
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i (lam : ℂ) P)
    (f : Lp ℂ 2 (reducedLaw Q)) {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ᵐ ω ∂reducedLaw Q, ‖f ω‖ ≤ M) {v : ℂ}
    (hv : Tendsto (fun s : ℝ => (s : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
      (Real.exp (-s * t) : ℂ) * ∫ ω, (P t.toNNReal f) ω ∂reducedLaw Q)
      (𝓝[>] (0 : ℝ)) (𝓝 v)) :
    Tendsto (fun s : ℝ => ∫ t in Set.Ioi (0 : ℝ), (Real.exp (-s * t) : ℂ) *
      ∫ ω, β i ω * (P t.toNNReal f) ω ∂reducedLaw Q)
      (𝓝[>] (0 : ℝ)) (𝓝 (((∫ ω, f ω ∂reducedLaw Q) - v) / (2 * lam : ℂ))) := by
  have hn : (2 * lam : ℂ) ≠ 0 := mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr hlam)
  apply ((tendsto_const_nhds.sub hv).div_const (2 * lam : ℂ)).congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have he := IsComplexEnvironmentSemigroup.abel_response_of_ae_bound hβ hP f hM hf s hs
  symm
  apply (eq_div_iff hn).mpr
  rw [he]
  ring

/-- Exact reduction of the response root from its two direct graph contracts. -/
theorem node_p_u3A_response_of_deps
    (hcore : node_p_u3A_response_u23_core_u2D_extensionStmt)
    (habel : node_p_u3A_response_u23_cesaro_u2D_abelStmt) :
    node_p_u3A_responseStmt := by
  intro d hd D Q hQ β a μ hβ ha hμ lam P hP
  letI := reducedLaw_probability Q
  letI := Q.probability
  let i : Fin d := ⟨0, by omega⟩
  constructor
  · intro F hF
    exact (hcore d hd D Q hQ β a μ hβ ha hμ lam P hP F hF).2
  · intro hlam Y hY velocity hv η hη
    obtain ⟨v, e, hv', he, hvl, _, hel, hb⟩ :=
      habel d hd D Q hQ β a μ hβ ha hμ lam hlam P hP Y hY
    have hp : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw Y ω) :=
      hY.mono fun _ h => h.1
    have hveq := hv'.unique hp hv
    subst v
    have heq : e = η := by
      obtain ⟨ω, hpω, heω, hηω⟩ := (hp.and (he.and hη)).exists
      letI := hpω
      obtain ⟨γ, heγ, hηγ⟩ := (heω.and hηω).exists
      exact tendsto_nhds_unique heγ hηγ
    subst e
    let A (j : Fin d) : ℝ := ∫ ω, (a i j ω).re ∂reducedLaw Q
    let m : ℝ := ∫ ω, (μ ω).re ∂reducedLaw Q
    let k (j : Fin d) : ℝ := (lam * A j - velocity j) / (2 * lam)
    let c : ℝ := (m - η) / 2
    have haMean (j : Fin d) : (∫ ω, a i j ω ∂reducedLaw Q) = (A j : ℂ) := by
      apply real_mean
      filter_upwards [ha i j] with ω hω
      simp only [hω, Complex.ofReal_im]
    have hμMean : (∫ ω, μ ω ∂reducedLaw Q) = (m : ℂ) := by
      apply real_mean
      filter_upwards [hμ] with ω hω
      simp only [hω, Complex.ofReal_im]
    refine ⟨k, c, ?_, ?_, ?_, ?_, ?_⟩
    · intro j
      let B := (1 / 2 : ℝ) * d * reducedLipschitzConstant D.ellipticity
      let C := Real.exp (2 * D.ellipticity) * D.ellipticity
      have hB : 0 ≤ B := by
        have hD := D.one_le_ellipticity
        dsimp [B, reducedLipschitzConstant]
        positivity
      have hC : 0 ≤ C := mul_nonneg (Real.exp_nonneg _) (zero_le_one.trans D.one_le_ellipticity)
      have hf : ∀ᵐ ω ∂reducedLaw Q, ‖(β j + (lam : ℂ) • a i j) ω‖ ≤ B + |lam| * C := by
        filter_upwards [Lp.coeFn_add (β j) ((lam : ℂ) • a i j),
          Lp.coeFn_smul (lam : ℂ) (a i j), response_drift_bound hβ j, response_coefficient_bound ha i j] with ω hadd hsm hbω haω
        rw [hadd, Pi.add_apply, hsm, Pi.smul_apply]
        exact (norm_add_le _ _).trans (add_le_add hbω (by
          simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs] using
            mul_le_mul_of_nonneg_left haω (abs_nonneg lam)))
      have hh := abel_pair_limit hβ hlam hP (β j + (lam : ℂ) • a i j)
        (add_nonneg hB (mul_nonneg (abs_nonneg lam) hC)) hf (hvl j).2
      rw [mean_add_smul, drift_mean_zero hβ j, zero_add, haMean] at hh
      simpa only [velocityCorrelation, k, A, Complex.ofReal_div, Complex.ofReal_sub,
        Complex.ofReal_mul, Complex.ofReal_ofNat] using hh
    · have hh := abel_pair_limit hβ hlam hP μ (Real.exp_nonneg _) (response_clock_bound hμ) hel
      have hscaled := hh.const_mul (lam : ℂ)
      have heq (s : ℝ) : (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-s * t) : ℂ) *
          clockCorrelation Q i (lam : ℂ) P β μ t.toNNReal) =
          (lam : ℂ) * ∫ t in Set.Ioi (0 : ℝ), (Real.exp (-s * t) : ℂ) *
            ∫ ω, β i ω * (P t.toNNReal μ) ω ∂reducedLaw Q := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun t => by
          have hs : clockCorrelation Q i (lam : ℂ) P β μ t.toNNReal =
              (lam : ℂ) * ∫ ω, β i ω * (P t.toNNReal μ) ω ∂reducedLaw Q := by
            rw [clockCorrelation, map_smul, ← integral_const_mul]
            apply integral_congr_ae
            filter_upwards [Lp.coeFn_smul (lam : ℂ) (P t.toNNReal μ)] with ω hω
            rw [hω, Pi.smul_apply, smul_eq_mul]
            ring
          dsimp only
          rw [hs]
          ring
      simp only [hμMean] at hscaled
      have hn : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlam
      have hc : (lam : ℂ) * (((m : ℂ) - (η : ℂ)) / (2 * lam : ℂ)) = (c : ℂ) := by
        dsimp [c]
        push_cast
        field_simp
      rw [hc] at hscaled
      exact hscaled.congr fun s => (heq s).symm
    · intro j
      dsimp [k]
      field_simp
      ring
    · dsimp [c]
      ring
    · intro lower upper hbounds
      exact (hb lower upper hbounds).2

end EinsteinFull.Blueprint
