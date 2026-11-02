import EinsteinFull.Calculus.C9FirstUnitGradientEnergy
import EinsteinFull.Calculus.C10DyadicGradientFluxSize
import EinsteinFull.Calculus.ComplexTransposeGradientTimeSupport
import EinsteinFull.Calculus.ComplexTransposeSupport
import EinsteinFull.Calculus.C10DyadicLargeWindowProjection
import EinsteinFull.Calculus.C1EndpointFiniteP
import EinsteinFull.Calculus.ComplexCenteringSourceSupport
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation

private theorem unit_time_integral_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) (hf : Continuous f) :
    ‖∫ r in Icc (0 : ℝ) 1, f r‖ ≤
      Real.sqrt (∫ r in Icc (0 : ℝ) 1, ‖f r‖^2) := by
  let ν := volume.restrict (Icc (0 : ℝ) 1)
  have hi : Integrable (fun r => ‖f r‖^2) ν := (hf.norm.pow 2).integrableOn_Icc
  have hm : MemLp (fun r => ‖f r‖) 2 ν :=
    (memLp_two_iff_integrable_sq_norm hf.norm.aestronglyMeasurable.restrict).mpr
      (by simpa only [norm_norm] using hi)
  have hc := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hm) (by simpa using (memLp_const (μ := ν) (p := 2) (1 : ℝ)))
  have hlen : ν.real univ = 1 := by simp [ν, Measure.real, Real.volume_Icc]
  simp only [norm_norm, norm_one, Real.rpow_two, one_pow, mul_one,
    integral_const, smul_eq_mul, hlen, Real.one_rpow] at hc
  rw [← Real.sqrt_eq_rpow] at hc
  exact (norm_integral_le_integral_norm _).trans hc

/-- Uniform Euclidean size of the actual flux increment on the first unit interval. -/
theorem first_unit_flux_size
    : ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d), ∃ C : ℝ, 1 ≤ C ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
        (β : Fin d → Lp ℂ 2 (reducedLaw Q))
        (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
        IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
        IsReducedClockObservation Q μ →
      ∀ (ζ : ℂ) (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
        IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
        IsComplexTransposeSemigroup Q P Pdag →
      ∀ (G F : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q)),
        IsFiniteTimeFlux hd Q ζ P Pdag β a μ G F → ‖ζ‖ ≤ 2 →
      ∀ ν : FluxIndex d, Real.sqrt (∑ j : Fin d, ‖F 1 ν j - F 0 ν j‖^2) ≤ C := by
  classical
  intro d hd D
  obtain ⟨C₀, hC₀, henergy⟩ := actual_first_unit_gradient_energy d D
  obtain ⟨M, hM, hobs⟩ := EndpointFiniteP.observation_bounds d D
  let K := Real.exp (2 * D.ellipticity) * D.ellipticity
  have hK : 0 < K := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one D.one_le_ellipticity)
  let S := K * (2 * ((d : ℝ) * K))^2
  have hS : 0 ≤ S := mul_nonneg hK.le (sq_nonneg _)
  let E := C₀ + 2*K*Real.exp (2*S)
  have hE : 0 < E := by dsimp only [E]; positivity
  let B := Real.sqrt E * (3*M)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  let U := Real.exp S * M
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  refine ⟨max 1 ((d : ℝ)*((d : ℝ)*K*B + 4*K*U)), le_max_left _ _, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd G F hF hζ ν
  let := reducedLaw_probability Q
  obtain ⟨hβb, hab, _⟩ := hobs Q hQ β a μ hβ ha hμ
  have norm_of_bound (f : Lp ℂ 2 (reducedLaw Q))
      (hf : ∀ᵐ ω ∂reducedLaw Q, ‖f ω‖ ≤ M) : ‖f‖ ≤ M := by
    simpa only [measureUnivNNReal, measure_univ, ENNReal.toNNReal_one,
      NNReal.coe_one, Real.one_rpow, one_mul] using Lp.norm_le_of_ae_bound hM.le hf
  have hb (j : Fin d) : ‖β j‖ ≤ M := norm_of_bound _ (hβb j)
  have ha' (j k : Fin d) : ‖a j k‖ ≤ M := norm_of_bound _ (hab j k)
  have hshift : complexForceShift d D.ellipticity ζ ≤ S := by
    change K * (‖ζ‖ * ((d : ℝ)*K))^2 ≤ K * (2 * ((d : ℝ)*K))^2
    apply mul_le_mul_of_nonneg_left _ hK.le
    exact pow_le_pow_left₀ (by positivity)
      (mul_le_mul_of_nonneg_right hζ (by positivity)) 2
  have hGenergy : (∫ r in Icc (0 : ℝ) 1, ∑ j, ‖G r.toNNReal ν j‖^2) ≤
      E * (3*M)^2 := by
    cases ν with
    | inl i =>
      let f := β i + ζ • a ⟨0, by omega⟩ i
      have hf : ‖f‖ ≤ 3*M := calc
        ‖f‖ ≤ ‖β i‖ + ‖ζ‖ * ‖a ⟨0, by omega⟩ i‖ := by
          simpa only [f, norm_smul] using norm_add_le (β i) (ζ • a ⟨0, by omega⟩ i)
        _ ≤ M + 2*M := add_le_add (hb i)
          (mul_le_mul hζ (ha' _ _) (norm_nonneg _) (by norm_num))
        _ = 3*M := by ring
      have he := (henergy Q ⟨0, by omega⟩ ζ P hP f hζ 1 (by norm_num) le_rfl).2
      have heq : (∫ r in Icc (0 : ℝ) 1, ∑ j, ‖G r.toNNReal (Sum.inl i) j‖^2) =
          ∫ r in Icc (0 : ℝ) 1, ∑ j, ‖hP.gradientOrbit f r j‖^2 := by
        rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc]
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
        have hg := (hP.centered_gradientOrbit_spec f hr.1).unique
          (hF.choose_spec.choose_spec.1 r.toNNReal (Sum.inl i))
        simp only [hg]
      rw [heq]
      apply he.trans
      apply mul_le_mul (show C₀ ≤ E from le_add_of_nonneg_right (by positivity))
        ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hf) (sq_nonneg _) hE.le
    | inr v =>
      have he := (hPd.integrableOn_Icc_sq_gradientOrbit hP (β ⟨0, by omega⟩)
        (t := 1) (by norm_num)).2
      have heq : (∫ r in Icc (0 : ℝ) 1, ∑ j, ‖G r.toNNReal (Sum.inr v) j‖^2) =
          ∫ r in Icc (0 : ℝ) 1,
            ‖complexTransposeGradientOrbit Q Pdag (β ⟨0, by omega⟩) r‖^2 := by
        rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc]
        apply integral_congr_ae
        filter_upwards [(hPd.gradientOrbit_horizon_energy hP (β ⟨0, by omega⟩) 1).2.1]
          with r hr
        have hg := hr.unique (hF.choose_spec.choose_spec.1 r.toNNReal (Sum.inr v))
        rw [PiLp.norm_sq_eq_of_L2]
        simp only [hg]
      rw [heq]
      apply he.trans
      simp only [mul_one]
      apply mul_le_mul _ ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
        ((hb _).trans (by linarith))) (sq_nonneg _) hE.le
      calc
        2*K*Real.exp (2*complexForceShift d D.ellipticity ζ) ≤
            2*K*Real.exp (2*S) := mul_le_mul_of_nonneg_left
              (Real.exp_le_exp.mpr (by linarith)) (by positivity)
        _ ≤ E := by dsimp only [E]; linarith
  have hcont (k : Fin d) : Continuous (fun r : ℝ => G r.toNNReal ν k) :=
    (hF.choose ν k).comp continuous_real_toNNReal
  have hsize (k : Fin d) : ‖∫ r in Icc (0 : ℝ) 1, G r.toNNReal ν k‖ ≤ B := by
    apply (unit_time_integral_bound _ (hcont k)).trans
    have hi : IntegrableOn (fun r : ℝ => ∑ j, ‖G r.toNNReal ν j‖^2) (Icc 0 1) :=
      integrable_finsetSum _ fun j _ => ((hcont j).norm.pow 2).integrableOn_Icc
    have hik : IntegrableOn (fun r : ℝ => ‖G r.toNNReal ν k‖^2) (Icc 0 1) :=
      ((hcont k).norm.pow 2).integrableOn_Icc
    calc
      Real.sqrt (∫ r in Icc (0 : ℝ) 1, ‖G r.toNNReal ν k‖^2) ≤
          Real.sqrt (∫ r in Icc (0 : ℝ) 1, ∑ j, ‖G r.toNNReal ν j‖^2) :=
        Real.sqrt_le_sqrt (integral_mono hik hi
          (fun r => Finset.single_le_sum (f := fun j : Fin d => ‖G r.toNNReal ν j‖^2)
            (fun j _ => sq_nonneg _) (Finset.mem_univ k)))
      _ ≤ Real.sqrt (E*(3*M)^2) := Real.sqrt_le_sqrt hGenergy
      _ = B := by rw [Real.sqrt_mul hE.le, Real.sqrt_sq (by positivity)]
  have hUsize : ‖∫ r in Icc (0 : ℝ) 1,
      transposeEndpoint Q ⟨0, by omega⟩ Pdag β r.toNNReal‖ ≤ U := by
    have hn := norm_setIntegral_le_of_norm_le_const
      (f := fun r : ℝ => transposeEndpoint Q ⟨0, by omega⟩ Pdag β r.toNNReal) (C := U)
      (isCompact_Icc.measure_lt_top (μ := volume)) (fun r (hr : r ∈ Icc (0 : ℝ) 1) => ?_)
    · simpa only [Real.volume_real_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1),
        sub_zero, mul_one] using hn
    · apply ((Pdag r.toNNReal).le_opNorm _).trans
      apply mul_le_mul _ (hb _) (norm_nonneg _) (Real.exp_pos _).le
      apply (hPd.norm_le hP _).trans
      apply Real.exp_le_exp.mpr
      rw [Real.toNNReal_of_nonneg hr.1]
      exact (mul_le_mul_of_nonneg_right hshift hr.1).trans
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hr.2 hS)
  have hcoord (j : Fin d) : ‖F 1 ν j - F 0 ν j‖ ≤ (d : ℝ)*K*B + 4*K*U := by
    rw [largeWindow_flux_split hd Q ζ P Pdag β a μ ha G F hF 0 1 (by norm_num) ν j]
    apply (norm_add_le _ _).trans
    apply add_le_add
    · apply (norm_sum_le _ _).trans
      calc
        (∑ k, ‖complexCoefficientMul Q j k
            (∫ r in Icc (0 : ℝ) 1, G r.toNNReal ν k)‖) ≤ ∑ _k : Fin d, K*B :=
          Finset.sum_le_sum fun k _ => ((complexCoefficientMul Q j k).le_opNorm _).trans
            (mul_le_mul (norm_complexCoefficientMul_le Q j k) (hsize k) (norm_nonneg _) hK.le)
        _ = _ := by simp; ring
    · cases ν with
      | inl i => simpa only [Sum.elim_inl, norm_zero] using mul_nonneg (by positivity : 0 ≤ 4*K) hU
      | inr v =>
        simp only [Sum.elim_inr, norm_smul]
        have hz : ‖(-2 : ℂ)*ζ‖ ≤ 4 := by
          rw [norm_mul]; norm_num; linarith
        exact mul_le_mul hz (((complexCoefficientMul Q j ⟨0, by omega⟩).le_opNorm _).trans
          (mul_le_mul (norm_complexCoefficientMul_le Q j _) hUsize (norm_nonneg _) hK.le))
          (norm_nonneg _) (by positivity) |>.trans_eq (by ring)
  apply le_trans _ (le_max_right _ _)
  calc
    Real.sqrt (∑ j, ‖F 1 ν j - F 0 ν j‖^2) ≤ ∑ j, ‖F 1 ν j - F 0 ν j‖ := by
      apply Real.sqrt_le_iff.mpr
      exact ⟨Finset.sum_nonneg (fun j _ => norm_nonneg _),
        Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ => norm_nonneg _)⟩
    _ ≤ ∑ _j : Fin d, ((d : ℝ)*K*B + 4*K*U) := Finset.sum_le_sum fun j _ => hcoord j
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end EinsteinFull.Blueprint
