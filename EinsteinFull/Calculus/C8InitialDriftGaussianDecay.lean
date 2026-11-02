import EinsteinFull.Calculus.C7UnitInitializationSupport
import EinsteinFull.Calculus.C8UnitUnforcedTranspose
import EinsteinFull.Calculus.C2TestReplacementSupport
open MeasureTheory
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation
open EinsteinFull.UnitInitialization

private instance probability {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r) :
    IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q

private theorem drift_average_flux {d : ℕ} (hd : 2 ≤ d) {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    {a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)}
    (ha : IsReducedCoefficientObservation Q a) (j : Fin d) (s : ℝ) (hs : 0 < s) :
    gaussianAverage hd Q s hs (β j) = (1 / 2 : ℝ) • ∑ l,
      gaussianDerivativeAverage hd Q s hs 1 (fun _ => l) (a l j) := by
  apply endpointPairing_ext Q
  intro g
  let V := homogeneousGaussianHorizontalGradient Q ⟨0, by omega⟩ s hs 0 g
  have hV := homogeneousAverage_hasComplexHorizontalGradient_allData Q
    ⟨0, by omega⟩ s hs 0 g
  have hw := hβ.integral_mul j (homogeneousAverage Q ⟨0, by omega⟩ s hs 0 g) V hV
  have hi (l : Fin d) : Integrable (fun ω => a l j ω * V l ω) (reducedLaw Q) :=
    (Lp.memLp (a l j)).integrable_mul (Lp.memLp (V l))
  have he : (∫ ω, ∑ l, (ω.1 0 l j : ℂ) * V l ω ∂reducedLaw Q) =
      ∑ l, c4EndpointPairing Q (a l j) (V l) := by
    simp only [c4EndpointPairing_apply]
    rw [← integral_finsetSum _ (fun l _ => hi l)]
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr (fun l => ha l j)] with ω hω
    simp only [hω]
  rw [he] at hw
  have hav := c4EndpointPairing_homogeneousAverage Q ⟨0, by omega⟩ s hs 0 (β j) g
  simp only [neg_zero] at hav
  change c4EndpointPairing Q (homogeneousAverage Q ⟨0, by omega⟩ s hs 0 (β j)) g = _
  rw [hav, c4EndpointPairing_apply, hw]
  have hder (l : Fin d) : c4EndpointPairing Q
      (gaussianDerivativeAverage hd Q s hs 1 (fun _ => l) (a l j)) g =
        -c4EndpointPairing Q (a l j) (V l) := by
    rw [c3EndpointPairing_gaussianDerivativeAverage_one,
      c3GaussianDerivativeAverage_one_eq_gradient]
  simp only [map_smul, map_sum, smul_apply,
    sum_apply]
  simp_rw [hder]
  rw [Finset.sum_neg_distrib]
  norm_num [Complex.real_smul]

private theorem derivative_norm_le {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (s : ℝ) (hs : 0 < s)
    (F : Lp ℂ 2 (reducedLaw Q)) (j : Fin d) (X : ℝ) (hX : 0 ≤ X)
    (hb : eLpNorm (fun ω => ∫ x,
      (fderiv ℝ (anisotropicGaussian (homogenizedCoefficient Q) s) x (unitVector j)) •
        F (translate x ω)) 2 (reducedLaw Q) ≤ ENNReal.ofReal X) :
    ‖gaussianDerivativeAverage hd Q s hs 1 (fun _ => j) F‖ ≤ X := by
  let k := fun x => fderiv ℝ (anisotropicGaussian (homogenizedCoefficient Q) s) x
    (unitVector j)
  have hk : Integrable k := integrable_homogenizedDensity_derivative Q j hs
  have hkc : Continuous k := by
    simp_rw [k, fderiv_anisotropicGaussian_coordinate (homogenizedCoefficient Q)
      (homogenizedMatrix_transpose Q)]
    have hg := (contDiff_anisotropicGaussian (homogenizedCoefficient Q) s).continuous
    unfold Matrix.mulVec dotProduct
    fun_prop
  have hkernel (x : Vec d) :
      fderiv ℝ (homogenizedGaussianKernel Q ⟨0, by omega⟩ s hs 0) x (unitVector j) =
        (k x : ℂ) := by
    rw [fderiv_homogenizedGaussianKernel_zero_coordinate,
      homogenizedGaussianKernel_zero_eq_ofReal, ← Complex.ofReal_mul]
    dsimp only [k]
    rw [fderiv_anisotropicGaussian_coordinate (homogenizedCoefficient Q) (homogenizedMatrix_transpose Q)]
  have he : gaussianDerivativeAverage hd Q s hs 1 (fun _ => j) F =
      -(∫ x, (k x : ℂ) • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x F) := by
    simp only [gaussianDerivativeAverage, iteratedFDeriv_one_apply,
      c3UnforcedGaussian_coordinateDerivative_neg, neg_smul, integral_neg]
    simp only [hkernel]
  rw [he, norm_neg]
  have hae := Calculus.C2TestReplacement.coeFn_complexKernel_average_translation Q
    (fun x => (k x : ℂ)) hk.ofReal (Complex.continuous_ofReal.comp hkc) F 0
  simp only [complexTranslation_zero, zero_add] at hae
  rw [Lp.norm_def]
  apply (ENNReal.toReal_mono ENNReal.ofReal_ne_top ?_).trans_eq
    (ENNReal.toReal_ofReal hX)
  rw [eLpNorm_congr_ae hae]
  exact hb

theorem initial_drift_gaussian_decay
    : ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d), ∃ C : ℝ, 0 < C ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
        (β : Fin d → Lp ℂ 2 (reducedLaw Q)), IsReducedDriftObservation Q hQ β →
      ∀ (i : Fin d) (s : ℝ) (hs : 0 < s),
        ‖gaussianAverage hd Q s hs (β i)‖ ≤ C * s ^ (-(1 / 2 + (d : ℝ) / 4)) := by
  intro d hd D
  let K := Real.exp (2 * D.ellipticity) * D.ellipticity
  have hK : 0 ≤ K := mul_nonneg (Real.exp_pos _).le
    (zero_le_one.trans D.one_le_ellipticity)
  obtain ⟨C, hC, hb⟩ := exists_homogenized_derivative_ball_average_bound d D.ellipticity
    D.dependenceRange 1 (2 * K) 2 (by norm_num) (by norm_num)
  refine ⟨(d : ℝ) * C + 1, by positivity, ?_⟩
  intro Q hQ β hβ i s hs
  let a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q) := fun l j =>
    ((memLp_reduced_coefficient_complex Q l j).mono_exponent (by simp : (2 : ℝ≥0∞) ≤ ∞)).toLp
      (fun ω => (ω.1 0 l j : ℂ))
  have ha : IsReducedCoefficientObservation Q a := fun l j =>
    ((memLp_reduced_coefficient_complex Q l j).mono_exponent (by simp : (2 : ℝ≥0∞) ≤ ∞)).coeFn_toLp
  have hfr : HasFiniteRange D.dependenceRange (reducedLaw Q) :=
    EinsteinRelation.Localization.finiteRange_map_reduce Q.measure Q.finiteRange
  have hbound (l : Fin d) :
      ‖gaussianDerivativeAverage hd Q s hs 1 (fun _ => l) (a l i)‖ ≤
        C * s ^ (-(1 : ℝ) / 2 - (d : ℝ) / 4) := by
    let c : FieldPair d → ℂ := fun ω => (max (-K) (min K (ω.1 0 l i)) : ℝ)
    have hcB (ω) : ‖c ω‖ ≤ K := by
      simp only [c, Complex.norm_real, Real.norm_eq_abs]
      exact abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
    have hloc : Measurable[localSigma {y : Vec d | euclideanNorm y < 1}] c := by
      have h0 : (0 : Vec d) ∈ {y : Vec d | euclideanNorm y < 1} := by
        simp [euclideanNorm, euclideanSq, dot]
      have he : Measurable[localSigma {y : Vec d | euclideanNorm y < 1}]
          (fun ω : FieldPair d => (ω.1 0, ω.2 0)) :=
        Measurable.of_comap_le (le_iSup_of_le ⟨0, h0⟩ le_rfl)
      exact Complex.measurable_ofReal.comp
        (measurable_const.max (measurable_const.min (((continuous_id : Continuous (fun A : Mat d => A)).matrix_elem l i).measurable.comp he.fst)))
    have hcm : Measurable c := hloc.mono (Probability.localSigma_le_borel _) le_rfl
    have hci : Integrable c (reducedLaw Q) :=
      (MemLp.of_bound hcm.aestronglyMeasurable K (ae_of_all _ hcB) :
        MemLp c 1 (reducedLaw Q)).integrable (by norm_num)
    have hca : c =ᵐ[reducedLaw Q] a l i := by
      filter_upwards [Correctors.ae_reducedEnvironmentLaw_origin_elliptic Q, ha l i]
        with ω he hea
      have heB : |ω.1 0 l i| ≤ K := by
        apply abs_entry_le_of_quadratic_bounds hK (ω.1 0) (he 0).1
        · intro ξ
          exact (mul_nonneg (inv_nonneg.mpr hK) (euclideanSq_nonneg_coords ξ)).trans
            ((he 0).2 ξ).1
        · exact fun ξ => ((he 0).2 ξ).2
      rw [hea]
      dsimp only [c]
      rw [min_eq_right (abs_le.mp heB).2, max_eq_right (abs_le.mp heB).1]
    let f : FieldPair d → ℂ := fun ω => c ω - ∫ ω, c ω ∂reducedLaw Q
    have hf : Measurable[localSigma {y : Vec d | euclideanNorm y < 1}] f :=
      hloc.sub measurable_const
    have hfB (ω) : ‖f ω‖ ≤ 2 * K := by
      have hm : ‖∫ ω, c ω ∂reducedLaw Q‖ ≤ K :=
        by simpa using norm_integral_le_of_norm_le_const (ae_of_all (reducedLaw Q) hcB)
      exact (norm_sub_le _ _).trans (by linarith [hcB ω])
    have hfmean : (∫ ω, f ω ∂reducedLaw Q) = 0 := by
      simp [f, integral_sub hci (integrable_const _)]
    have hfe : f =ᵐ[reducedLaw Q] centeredComplexLp Q (a l i) := by
      have hm := integral_congr_ae hca
      filter_upwards [hca, centeredComplexLp_ae Q (a l i)] with ω he hc
      exact (congrArg₂ (fun x y : ℂ => x - y) he hm).trans hc.symm
    have hh := hb Q (reducedLaw Q) (reducedLaw_stationary Q) hfr f hf hfB hfmean l s hs
    have he := kernel_average_congr_ae (reducedLaw Q) (reducedLaw_stationary Q) hfe
      (fun x => fderiv ℝ (anisotropicGaussian (homogenizedCoefficient Q) s) x (unitVector l))
    rw [← gaussianDerivativeAverage_one_centered hd Q s hs (a l i) l]
    apply derivative_norm_le hd Q s hs _ l _ (mul_nonneg hC (Real.rpow_nonneg hs.le _))
    rw [← eLpNorm_congr_ae he]
    simpa only [ENNReal.ofReal_ofNat] using hh.2
  rw [drift_average_flux hd hβ ha]
  calc
    ‖(1 / 2 : ℝ) • ∑ l, gaussianDerivativeAverage hd Q s hs 1 (fun _ => l) (a l i)‖
        ≤ (1 / 2 : ℝ) * ∑ l, ‖gaussianDerivativeAverage hd Q s hs 1 (fun _ => l) (a l i)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by norm_num)
    _ ≤ (1 / 2 : ℝ) * ∑ _l : Fin d, C * s ^ (-(1 : ℝ) / 2 - (d : ℝ) / 4) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun l _ => hbound l) (by norm_num)
    _ ≤ ((d : ℝ) * C + 1) * s ^ (-(1 / 2 + (d : ℝ) / 4)) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hexp : -(1 : ℝ) / 2 - (d : ℝ) / 4 = -(1 / 2 + (d : ℝ) / 4) := by ring
      rw [hexp]
      have hp := Real.rpow_nonneg hs.le (-(1 / 2 + (d : ℝ) / 4))
      nlinarith [mul_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d) hC]
end EinsteinFull.Blueprint
