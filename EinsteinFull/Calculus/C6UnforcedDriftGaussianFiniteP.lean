import EinsteinFull.Calculus.C6UnforcedDriftProductDerivativeDecay
import EinsteinFull.Calculus.C7UnforcedCoefficientDerivativeDecay
import EinsteinFull.Calculus.C4GaussianDerivativeRowWeakProduct
import EinsteinFull.Calculus.C8InitialDriftGaussianDecay
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation
open EinsteinFull.UnitInitialization

private theorem c6_eLp_add {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (q : ℝ≥0∞) (hq : 1 ≤ q) (f g : Lp ℂ 2 μ) :
    eLpNorm (f + g : Lp ℂ 2 μ) q μ ≤ eLpNorm f q μ + eLpNorm g q μ := by
  rw [eLpNorm_congr_ae (Lp.coeFn_add f g)]
  exact eLpNorm_add_le hq

private theorem c6_eLp_smul {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (q : ℝ≥0∞) (c : ℝ) (f : Lp ℂ 2 μ) :
    eLpNorm (c • f : Lp ℂ 2 μ) q μ = ENNReal.ofReal |c| * eLpNorm f q μ := by
  rw [eLpNorm_congr_ae (Lp.coeFn_smul c f), eLpNorm_const_smul]
  simp only [← ofReal_norm, Real.norm_eq_abs]

/-- Finite Lp balls are closed in L2, by convergence in measure and Fatou. -/
private theorem c6_isClosed_lp_ball {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (q : ℝ≥0∞) (B : ℝ) :
    IsClosed {f : Lp ℂ 2 μ | eLpNorm f q μ ≤ ENNReal.ofReal B} := by
  apply isSeqClosed_iff_isClosed.mp
  intro f g hf hfg
  exact eLpNorm_le_of_tendstoInMeasure (Eventually.of_forall hf)
    (tendstoInMeasure_of_tendsto_Lp hfg) (fun n => Lp.aestronglyMeasurable (f n))

private theorem c6_convex_lp_ball {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (q : ℝ≥0∞) (hq : 1 ≤ q) (B : ℝ) :
    Convex ℝ {f : Lp ℂ 2 μ | eLpNorm f q μ ≤ ENNReal.ofReal B} := by
  intro f hf g hg a b ha hb hab
  apply (c6_eLp_add μ q hq _ _).trans
  rw [c6_eLp_smul, c6_eLp_smul, abs_of_nonneg ha, abs_of_nonneg hb]
  calc
    _ ≤ ENNReal.ofReal a * ENNReal.ofReal B + ENNReal.ofReal b * ENNReal.ofReal B :=
      add_le_add (mul_le_mul_right hf _) (mul_le_mul_right hg _)
    _ = ENNReal.ofReal B := by
      rw [← add_mul, ← ENNReal.ofReal_add ha hb, hab, ENNReal.ofReal_one, one_mul]

/-- A uniform finite-p bound survives the actual L2 time integral. -/
private theorem c6_eLp_integral_Icc {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (q : ℝ≥0∞) (hq : 1 ≤ q) {f : ℝ → Lp ℂ 2 μ} {t B : ℝ}
    (ht : 0 ≤ t) (_hB : 0 ≤ B) (hf : IntegrableOn f (Icc 0 t))
    (hb : ∀ᵐ r ∂volume.restrict (Icc 0 t), eLpNorm (f r) q μ ≤ ENNReal.ofReal B) :
    eLpNorm (∫ r in Icc 0 t, f r : Lp ℂ 2 μ) q μ ≤ ENNReal.ofReal (B * t) := by
  by_cases ht0 : t = 0
  · subst t
    simp only [Icc_self, Measure.restrict_singleton, measure_singleton, zero_smul, integral_zero_measure, mul_zero, ENNReal.ofReal_zero]
    rw [eLpNorm_congr_ae (Lp.coeFn_zero ℂ 2 μ), eLpNorm_zero]
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  have hmeasure : volume (Icc 0 t) = ENNReal.ofReal t := by simp
  have hmem := (c6_convex_lp_ball μ q hq B).set_average_mem
    (c6_isClosed_lp_ball μ q B) (by rw [hmeasure]; exact (ENNReal.ofReal_pos.mpr htpos).ne')
    (by rw [hmeasure]; exact ENNReal.ofReal_ne_top) hb hf
  change eLpNorm (⨍ r in Icc 0 t, f r : Lp ℂ 2 μ) q μ ≤ ENNReal.ofReal B at hmem
  rw [average_eq, measureReal_def, Measure.restrict_apply_univ, hmeasure, ENNReal.toReal_ofReal ht] at hmem
  have he : (∫ r in Icc 0 t, f r : Lp ℂ 2 μ) =
      t • (t⁻¹ • ∫ r in Icc 0 t, f r) := by rw [smul_smul, mul_inv_cancel₀ ht0, one_smul]
  rw [he, c6_eLp_smul, abs_of_nonneg ht, mul_comm B t, ENNReal.ofReal_mul ht]
  exact mul_le_mul_right hmem _

private theorem c6_eLp_sum {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (q : ℝ≥0∞) (hq : 1 ≤ q) (S : Finset ι) (f : ι → Lp ℂ 2 μ) :
    eLpNorm (∑ i ∈ S, f i : Lp ℂ 2 μ) q μ ≤ ∑ i ∈ S, eLpNorm (f i) q μ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [eLpNorm_congr_ae (Lp.coeFn_zero ℂ 2 μ), eLpNorm_zero]
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    exact (c6_eLp_add μ q hq _ _).trans (add_le_add le_rfl ih)

private theorem c6_eLp_of_real_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (q : ℝ≥0∞) (f : Lp ℂ 2 μ) (hf : MemLp f q μ) {B : ℝ}
    (hb : (eLpNorm f q μ).toReal ≤ B) : eLpNorm f q μ ≤ ENNReal.ofReal B := by
  exact (le_of_eq (ENNReal.ofReal_toReal hf.eLpNorm_ne_top).symm).trans
    (ENNReal.ofReal_le_ofReal hb)

private theorem c6_mem_of_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (q : ℝ≥0∞) (f : Lp ℂ 2 μ) {B : ℝ} (hb : eLpNorm f q μ ≤ ENNReal.ofReal B) :
    MemLp f q μ := by
  exact hb.trans_lt ENNReal.ofReal_lt_top

private instance c6_probability {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r) :
    IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q

private theorem c6_drift_average_flux {d : ℕ} (hd : 2 ≤ d) {D : StructuralData d}
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

private theorem c6_derivative_bound {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (s : ℝ) (hs : 0 < s)
    (F : Lp ℂ 2 (reducedLaw Q)) (j : Fin d) (p X : ℝ)
    (hb : eLpNorm (fun ω => ∫ x,
      (fderiv ℝ (anisotropicGaussian (homogenizedCoefficient Q) s) x (unitVector j)) •
        F (translate x ω)) (ENNReal.ofReal p) (reducedLaw Q) ≤ ENNReal.ofReal X) :
    eLpNorm (gaussianDerivativeAverage hd Q s hs 1 (fun _ => j) F)
      (ENNReal.ofReal p) (reducedLaw Q) ≤ ENNReal.ofReal X := by
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
  rw [he, eLpNorm_congr_ae (Lp.coeFn_neg _), eLpNorm_neg]
  have hae := Calculus.C2TestReplacement.coeFn_complexKernel_average_translation Q
    (fun x => (k x : ℂ)) hk.ofReal (Complex.continuous_ofReal.comp hkc) F 0
  simp only [complexTranslation_zero, zero_add] at hae
  rw [eLpNorm_congr_ae hae]
  exact hb

private theorem c6_initial_drift_decay
    : ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (p : ℝ), 2 ≤ p → ∃ C : ℝ, 0 < C ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
        (β : Fin d → Lp ℂ 2 (reducedLaw Q)), IsReducedDriftObservation Q hQ β →
      ∀ (i : Fin d) (s : ℝ) (hs : 0 < s),
        eLpNorm (gaussianAverage hd Q s hs (β i)) (ENNReal.ofReal p) (reducedLaw Q) ≤ ENNReal.ofReal (C * s ^ (-(1 / 2 + (d : ℝ) / 4))) := by
  intro d hd D p hp
  let K := Real.exp (2 * D.ellipticity) * D.ellipticity
  have hK : 0 ≤ K := mul_nonneg (Real.exp_pos _).le
    (zero_le_one.trans D.one_le_ellipticity)
  obtain ⟨C, hC, hb⟩ := exists_homogenized_derivative_ball_average_bound d D.ellipticity
    D.dependenceRange 1 (2 * K) p (by norm_num) (by linarith)
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
      eLpNorm (gaussianDerivativeAverage hd Q s hs 1 (fun _ => l) (a l i))
        (ENNReal.ofReal p) (reducedLaw Q) ≤
        ENNReal.ofReal (C * s ^ (-(1 : ℝ) / 2 - (d : ℝ) / 4)) := by
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
    apply c6_derivative_bound hd Q s hs _ l p _
    rw [← eLpNorm_congr_ae he]
    simpa only [ENNReal.ofReal_ofNat] using hh.2
  rw [c6_drift_average_flux hd hβ ha, c6_eLp_smul]
  have hq : 1 ≤ ENNReal.ofReal p := by
    exact_mod_cast ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith)
  have hsum := (c6_eLp_sum (reducedLaw Q) (ENNReal.ofReal p) hq Finset.univ
    (fun l => gaussianDerivativeAverage hd Q s hs 1 (fun _ => l) (a l i))).trans
      (Finset.sum_le_sum (fun l _ => hbound l))
  have hexp : -(1 : ℝ) / 2 - (d : ℝ) / 4 = -(1 / 2 + (d : ℝ) / 4) := by ring
  rw [hexp] at hsum
  have hsum' : eLpNorm (∑ l, gaussianDerivativeAverage hd Q s hs 1 (fun _ => l) (a l i) : Lp ℂ 2 (reducedLaw Q))
      (ENNReal.ofReal p) (reducedLaw Q) ≤
      ENNReal.ofReal ((d : ℝ) * (C * s ^ (-(1 / 2 + (d : ℝ) / 4)))) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ENNReal.ofReal_mul (Nat.cast_nonneg d), ENNReal.ofReal_natCast] using hsum
  apply (mul_le_mul_right hsum' _).trans
  rw [← ENNReal.ofReal_mul (abs_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  norm_num only [abs_div, abs_one, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hpow := Real.rpow_nonneg hs.le (-(1 / 2 + (d : ℝ) / 4))
  nlinarith [mul_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d) hC]

private theorem c6_gaussian_first_derivative_has_derivative
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (s : ℝ) (hs : 0 < s) (f : Lp ℂ 2 (reducedLaw Q)) (l k : Fin d) :
    HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) l
      (gaussianDerivativeAverage hd Q s hs 1 (fun _ => k) f)
      (gaussianDerivativeAverage hd Q s hs 2 (Fin.cases l (fun _ => k)) f) := by
  obtain ⟨g, hg, hg₂⟩ := UnforcedIdentification.homogeneousAverage_hasHorizontalJet_two
    Q ⟨0, by omega⟩ s hs 0 (Fin.cases l (fun _ => k)) f
  have hg₁ : HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) k
      (homogeneousAverage Q ⟨0, by omega⟩ s hs 0 f)
      (gaussianDerivativeAverage hd Q s hs 1 (fun _ => k) f) := by
    rw [c3GaussianDerivativeAverage_one_eq_gradient]
    exact homogeneousAverage_hasComplexHorizontalGradient_allData Q ⟨0, by omega⟩ s hs 0 f k
  have he : g = gaussianDerivativeAverage hd Q s hs 1 (fun _ => k) f := by
    exact hg.unique hg₁
  rw [he] at hg₂
  simpa only [Fin.cases_zero, homogeneousDerivativeAverage, neg_zero,
    gaussianDerivativeAverage] using hg₂

/-- The second Gaussian derivative annihilates the subtracted mean exactly. -/
private theorem c6_gaussian_second_derivative_centered
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (s : ℝ) (hs : 0 < s) (f : Lp ℂ 2 (reducedLaw Q)) (l k : Fin d) :
    gaussianDerivativeAverage hd Q s hs 2 (Fin.cases l (fun _ => k))
        (centeredComplexLp Q f) =
      gaussianDerivativeAverage hd Q s hs 2 (Fin.cases l (fun _ => k)) f := by
  have h := c6_gaussian_first_derivative_has_derivative hd Q s hs (centeredComplexLp Q f) l k
  rw [gaussianDerivativeAverage_one_centered] at h
  exact h.unique (c6_gaussian_first_derivative_has_derivative hd Q s hs f l k)

private theorem c6_gaussian_coefficient_row_derivative
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (hβ : IsReducedDriftObservation Q hQ β)
    (u : Lp ℂ 2 (reducedLaw Q)) (G : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) u G)
    (l : Fin d) (H R : Lp ℂ 2 (reducedLaw Q))
    (hH : (H : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      fun ω => ∑ k : Fin d, (ω.1 0 l k : ℂ) * G k ω)
    (hR : (R : FieldPair d → ℂ) =ᵐ[reducedLaw Q] fun ω => β l ω * u ω)
    (s : ℝ) (hs : 0 < s) (j : Fin d) :
    gaussianDerivativeAverage hd Q s hs 1 (fun _ => j) H =
      (∑ k : Fin d, gaussianDerivativeAverage hd Q s hs 2
        (Fin.cases j (fun _ => k)) (complexCoefficientMul Q l k u)) -
      (2 : ℂ) • gaussianDerivativeAverage hd Q s hs 1 (fun _ => j) R := by
  classical
  have havg (f : Lp ℂ 2 (reducedLaw Q)) :
      HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) j
        (gaussianAverage hd Q s hs f)
        (gaussianDerivativeAverage hd Q s hs 1 (fun _ => j) f) := by
    rw [c3GaussianDerivativeAverage_one_eq_gradient]
    exact homogeneousAverage_hasComplexHorizontalGradient_allData Q ⟨0, by omega⟩ s hs 0 f j
  have hsum (S : Finset (Fin d)) :
      HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) j
        (∑ k ∈ S, gaussianDerivativeAverage hd Q s hs 1 (fun _ => k)
          (complexCoefficientMul Q l k u))
        (∑ k ∈ S, gaussianDerivativeAverage hd Q s hs 2
          (Fin.cases j (fun _ => k)) (complexCoefficientMul Q l k u)) := by
    induction S using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using
        HasComplexHorizontalDerivative.zero (reducedLaw Q) (reducedLaw_stationary Q) j
    | @insert k S hk ih =>
      simpa only [Finset.sum_insert hk] using
        (c6_gaussian_first_derivative_has_derivative hd Q s hs
          (complexCoefficientMul Q l k u) j k).add ih
  have hright := (hsum Finset.univ).add ((havg R).smul (-2 : ℂ))
  simp only [neg_smul, ← sub_eq_add_neg] at hright
  rw [← gaussian_coefficient_row_weak_product hd D Q hQ β hβ u G hG l H R hH hR s hs]
    at hright
  exact (havg H).unique hright

private theorem c6_flux_increment
    {d : ℕ} (hd : 2 ≤ d) {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P)
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    {a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)}
    (ha : IsReducedCoefficientObservation Q a)
    (t : ℝ≥0) (j : Fin d) (s : ℝ) (hs : 0 < s) :
    gaussianAverage hd Q s hs (P t (β j)) = gaussianAverage hd Q s hs (β j) +
      (1 / 2 : ℝ) • ∑ l, gaussianDerivativeAverage hd Q s hs 1 (fun _ => l)
        (∫ r in Icc (0 : ℝ) (t : ℝ), ∑ k,
          complexCoefficientMul Q l k (hP.gradientOrbit (β j) r k)) := by
  have hzero := unforced_gaussian_centered_flux hd hP hβ ha 0 j s hs
  simp [hP.1, gaussianDerivativeAverage_one_centered] at hzero
  rw [unforced_gaussian_centered_flux hd hP hβ ha t j s hs]
  simp only [gaussianDerivativeAverage_one_centered]
  have hadd (l : Fin d) (f g : Lp ℂ 2 (reducedLaw Q)) :
      gaussianDerivativeAverage hd Q s hs 1 (fun _ => l) (f+g) =
        gaussianDerivativeAverage hd Q s hs 1 (fun _ => l) f +
        gaussianDerivativeAverage hd Q s hs 1 (fun _ => l) g := by
    simpa only [gaussianDerivativeAverageCLM_apply] using
      (gaussianDerivativeAverageCLM hd Q s hs 1 (fun _ => l)).map_add f g
  simp_rw [hadd]
  simp only [one_div] at hzero ⊢
  rw [Finset.sum_add_distrib, smul_add, ← hzero]

/-- Literal centered and uncentered product representatives have identical
first Gaussian derivatives. -/
private theorem c6_gaussian_product_derivative_of_representatives
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (f g H R : Lp ℂ 2 (reducedLaw Q))
    (hH : (H : FieldPair d → ℂ) =ᵐ[reducedLaw Q] fun ω =>
      f ω * g ω - ∫ η, f η * g η ∂reducedLaw Q)
    (hR : (R : FieldPair d → ℂ) =ᵐ[reducedLaw Q] fun ω => f ω * g ω)
    (s : ℝ) (hs : 0 < s) (j : Fin d) :
    gaussianDerivativeAverage hd Q s hs 1 (fun _ => j) H =
      gaussianDerivativeAverage hd Q s hs 1 (fun _ => j) R := by
  have he : H = centeredComplexLp Q R := by
    apply Lp.ext
    have hi := integral_congr_ae hR
    filter_upwards [hH, centeredComplexLp_ae Q R, hR] with ω hHω hcω hRω
    rw [hHω, hcω, hRω, hi]
  rw [he, gaussianDerivativeAverage_one_centered]

private theorem c6_bound_add {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (q : ℝ≥0∞) (hq : 1 ≤ q) (f g : Lp ℂ 2 μ) {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hf : eLpNorm f q μ ≤ ENNReal.ofReal B) (hg : eLpNorm g q μ ≤ ENNReal.ofReal C) :
    eLpNorm (f+g : Lp ℂ 2 μ) q μ ≤ ENNReal.ofReal (B+C) := by
  exact (c6_eLp_add μ q hq f g).trans
    ((add_le_add hf hg).trans_eq (ENNReal.ofReal_add hB hC).symm)

private theorem c6_bound_smul {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (q : ℝ≥0∞) (c : ℝ) (f : Lp ℂ 2 μ) {B : ℝ}
    (hf : eLpNorm f q μ ≤ ENNReal.ofReal B) :
    eLpNorm (c • f : Lp ℂ 2 μ) q μ ≤ ENNReal.ofReal (|c| * B) := by
  rw [c6_eLp_smul]
  exact (mul_le_mul_right hf _).trans_eq (ENNReal.ofReal_mul (abs_nonneg c)).symm

private theorem c6_bound_sum {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (q : ℝ≥0∞) (hq : 1 ≤ q) (f : ι → Lp ℂ 2 μ)
    {B : ℝ} (_hB : 0 ≤ B) (hf : ∀ i, eLpNorm (f i) q μ ≤ ENNReal.ofReal B) :
    eLpNorm (∑ i, f i : Lp ℂ 2 μ) q μ ≤ ENNReal.ofReal ((Fintype.card ι : ℝ)*B) := by
  have h := (c6_eLp_sum μ q hq Finset.univ f).trans
    (Finset.sum_le_sum (fun i _ => hf i))
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast] using h

private theorem c6_operator_integral_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (q : ℝ≥0∞) (hq : 1 ≤ q)
    (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (f : ℝ≥0 → Lp ℂ 2 μ)
    (hf : Continuous f) (t : ℝ≥0) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ r : ℝ≥0, r ≤ t → eLpNorm (A (f r)) q μ ≤ ENNReal.ofReal B) :
    eLpNorm (A (∫ r in Icc (0 : ℝ) (t : ℝ), f r.toNNReal)) q μ ≤
      ENNReal.ofReal (B*(t : ℝ)) := by
  have hi := integrableOn_comp_toNNReal_Icc f hf (t : ℝ)
  rw [← A.integral_comp_comm hi]
  apply c6_eLp_integral_Icc μ q hq t.coe_nonneg hB (A.integrable_comp hi)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
  exact hb r.toNNReal (by rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr.1]; exact hr.2)

private theorem c6_bound_sub {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (q : ℝ≥0∞) (hq : 1 ≤ q) (f g : Lp ℂ 2 μ) {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hf : eLpNorm f q μ ≤ ENNReal.ofReal B) (hg : eLpNorm g q μ ≤ ENNReal.ofReal C) :
    eLpNorm (f-g : Lp ℂ 2 μ) q μ ≤ ENNReal.ofReal (B+C) := by
  rw [eLpNorm_congr_ae (Lp.coeFn_sub f g)]
  exact (eLpNorm_sub_le hq).trans
    ((add_le_add hf hg).trans_eq (ENNReal.ofReal_add hB hC).symm)

private theorem c6_bound_complex_smul {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (q : ℝ≥0∞) (c : ℂ) (f : Lp ℂ 2 μ) {B : ℝ}
    (hf : eLpNorm f q μ ≤ ENNReal.ofReal B) :
    eLpNorm (c • f : Lp ℂ 2 μ) q μ ≤ ENNReal.ofReal (‖c‖ * B) := by
  rw [eLpNorm_congr_ae (Lp.coeFn_smul c f), eLpNorm_const_smul, ← ofReal_norm]
  exact (mul_le_mul_right hf _).trans_eq (ENNReal.ofReal_mul (norm_nonneg c)).symm

/-- Uniform finite-p Gaussian decay of the actual zero-force drift orbit. -/
theorem unforced_drift_gaussian_decay_finite_p
    : ∀ (hlocal : node_e_u3A_forced_u2D_localityStmt)
        (hends : node_stationary_u2D_analytic_u2D_semigroup_u23_endpointsStmt)
        (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (T p : ℝ), 0 ≤ T → 2 ≤ p →
      ∃ C : ℝ, 0 < C ∧ ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
        (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q))
        (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
        IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ →
      ∀ (P Pdag : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
        (∀ ζ, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (P ζ)) →
        (∀ ζ, IsComplexTransposeSemigroup Q (P ζ) (Pdag ζ)) →
      ∀ (t : ℝ≥0), (t : ℝ) ≤ T → ∀ (i : Fin d) (s : ℝ) (hs : 0 < s),
        MemLp (gaussianAverage hd Q s hs (P 0 t (β i)) : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm (gaussianAverage hd Q s hs (P 0 t (β i)) : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ C * s ^ (-(1/2+(d : ℝ)/4)) := by
  intro hlocal hends d hd D T p hT hp
  obtain ⟨Cs, hCs, hsmall⟩ := point_bound hlocal d hd D T hT
  obtain ⟨Ci, hCi, hinit⟩ := c6_initial_drift_decay d hd D p hp
  obtain ⟨Cc, hCc, hcoef⟩ :=
    unforced_coefficient_product_derivative_decay hlocal hends d hd D T p hT hp
  obtain ⟨Cr, hCr, hdrift⟩ :=
    unforced_drift_product_derivative_decay hlocal hends d hd D T p hT hp
  have hCs0 : 0 ≤ Cs := by linarith
  have hCc0 : 0 ≤ Cc := by linarith
  have hCr0 : 0 ≤ Cr := by linarith
  let C := Cs + Ci + (d : ℝ) * T * ((d : ℝ) * Cc + 2 * Cr) + 1
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro Q hQ β a μ hβ ha hμ P Pdag hP hPdag t ht i s hs
  let q := ENNReal.ofReal p
  have hq : 1 ≤ q := by
    exact_mod_cast ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith)
  let z := s ^ (-(1/2+(d : ℝ)/4))
  have hz : 0 ≤ z := Real.rpow_nonneg hs.le _
  have hCB : 0 ≤ C := by dsimp only [C]; positivity
  suffices hb : eLpNorm (gaussianAverage hd Q s hs (P 0 t (β i))) q (reducedLaw Q) ≤
      ENNReal.ofReal (C*z) by
    exact ⟨c6_mem_of_bound _ _ _ hb,
      (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb)
        ENNReal.ofReal_ne_top).mpr hb |>.trans_eq (ENNReal.toReal_ofReal (mul_nonneg hCB hz))⟩
  by_cases hs₁ : s ≤ 1
  · have h := hsmall Q hQ β a μ hβ ha hμ 0 (P 0) (Pdag 0) (hP 0) (hPdag 0)
      (.inl i) (by norm_num) t ht q
    simp only [indexedEndpoint] at h
    rw [UnforcedIdentification.velocityEndpoint_zero hd Q (P 0) (hP 0) β hβ a t i] at h
    have hg := gaussian_average_bound hd Q p hp _ h.1 s hs
    apply c6_eLp_of_real_bound _ _ _ hg.1
    have hz1 : 1 ≤ z := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hs hs₁
      (neg_nonpos.mpr (by positivity))
    apply (hg.2.trans h.2).trans
    apply (le_mul_of_one_le_right hCs0 hz1).trans
    apply mul_le_mul_of_nonneg_right _ hz
    dsimp only [C]
    have hn : 0 ≤ (d : ℝ)*T*((d : ℝ)*Cc+2*Cr) := by positivity
    linarith
  have hs₁ : 1 ≤ s := le_of_lt (lt_of_not_ge hs₁)
  have hpow₂ : s ^ (-((2 : ℝ)/2+(d : ℝ)/4)) ≤ z :=
    Real.rpow_le_rpow_of_exponent_le hs₁ (by norm_num; linarith)
  let U : Lp ℂ 2 (reducedLaw Q) := ∫ r in Icc (0 : ℝ) (t : ℝ), P 0 r.toNNReal (β i)
  have hcoefU (l k : Fin d) :
      eLpNorm (gaussianDerivativeAverage hd Q s hs 2 (Fin.cases l (fun _ => k))
        (complexCoefficientMul Q l k U)) q (reducedLaw Q) ≤
        ENNReal.ofReal ((Cc*z)*(t : ℝ)) := by
    let A := (gaussianDerivativeAverageCLM hd Q s hs 2 (Fin.cases l (fun _ => k))).comp
      (complexCoefficientMul Q l k)
    have hb (r : ℝ≥0) (hr : r ≤ t) : eLpNorm (A (P 0 r (β i))) q (reducedLaw Q) ≤
        ENNReal.ofReal (Cc*z) := by
      have hc := hcoef Q hQ β a μ hβ ha hμ P Pdag hP hPdag r
        ((show (r : ℝ) ≤ t from hr).trans ht) i l k 2 (by decide) (by decide)
        (Fin.cases l (fun _ => k)) s hs
      have he := c6_gaussian_second_derivative_centered hd Q s hs
        (complexCoefficientMul Q l k (P 0 r (β i))) l k
      dsimp only at hc
      rw [he] at hc
      simpa only [A, ContinuousLinearMap.comp_apply, gaussianDerivativeAverageCLM_apply] using
        c6_eLp_of_real_bound _ _ _ hc.1
          (hc.2.trans (mul_le_mul_of_nonneg_left hpow₂ hCc0))
    simpa only [A, U, ContinuousLinearMap.comp_apply, gaussianDerivativeAverageCLM_apply] using
      c6_operator_integral_bound (reducedLaw Q) q hq A (fun r => P 0 r (β i))
        ((hP 0).2.2.1 (β i)) t (mul_nonneg hCc0 hz) hb
  obtain ⟨K, _, hobs⟩ := EndpointFiniteP.observation_bounds d D
  have hβB := (hobs Q hQ β a μ hβ ha hμ).1
  have hβtop (l : Fin d) : MemLp (β l : FieldPair d → ℂ) ∞ (reducedLaw Q) :=
    MemLp.of_bound (Lp.memLp _).aestronglyMeasurable K (hβB l)
  let M (l : Fin d) : Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q) :=
    (ContinuousLinearMap.mul ℂ ℂ).holderL (reducedLaw Q) ∞ 2 2 ((hβtop l).toLp (β l))
  have hM (l : Fin d) (f : Lp ℂ 2 (reducedLaw Q)) :
      (M l f : FieldPair d → ℂ) =ᵐ[reducedLaw Q] fun ω => β l ω * f ω := by
    filter_upwards [(hβtop l).coeFn_toLp,
      (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) ((hβtop l).toLp (β l)) f]
      with ω h1 h2
    simpa only [M, ContinuousLinearMap.holderL_apply_apply,
      ContinuousLinearMap.mul_apply', h1] using h2
  have hdriftU (l : Fin d) :
      eLpNorm (gaussianDerivativeAverage hd Q s hs 1 (fun _ => l) (M l U)) q (reducedLaw Q) ≤
        ENNReal.ofReal ((Cr*z)*(t : ℝ)) := by
    let A := (gaussianDerivativeAverageCLM hd Q s hs 1 (fun _ => l)).comp (M l)
    have hb (r : ℝ≥0) (hr : r ≤ t) : eLpNorm (A (P 0 r (β i))) q (reducedLaw Q) ≤
        ENNReal.ofReal (Cr*z) := by
      obtain ⟨H, hH, hHb⟩ := hdrift Q hQ β a μ hβ ha hμ P Pdag hP hPdag r
        ((show (r : ℝ) ≤ t from hr).trans ht) i l
      have he := c6_gaussian_product_derivative_of_representatives hd Q
        (β l) (P 0 r (β i)) H (M l (P 0 r (β i))) hH (hM l _) s hs l
      have hh := hHb 1 (by decide) (by decide) (fun _ => l) s hs
      rw [he] at hh
      simpa only [A, ContinuousLinearMap.comp_apply, gaussianDerivativeAverageCLM_apply,
        Nat.cast_one] using c6_eLp_of_real_bound _ _ _ hh.1 hh.2
    simpa only [U, A, ContinuousLinearMap.comp_apply, gaussianDerivativeAverageCLM_apply] using
      c6_operator_integral_bound (reducedLaw Q) q hq A (fun r => P 0 r (β i))
        ((hP 0).2.2.1 (β i)) t (mul_nonneg hCr0 hz) hb
  let V := ∫ r in Icc (0 : ℝ) (t : ℝ), (hP 0).gradientOrbit (β i) r
  let H (l : Fin d) := ∑ k, complexCoefficientMul Q l k (V k)
  have hHG (l : Fin d) : (H l : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      fun ω => ∑ k : Fin d, (ω.1 0 l k : ℂ) * V k ω := by
    filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun k => complexCoefficientMul Q l k (V k)),
      ae_all_iff.mpr (fun k => complexCoefficientMul_coe Q l k (V k))] with ω hsum hcoeff
    simpa only [H, Finset.sum_apply, hcoeff] using hsum
  have hrow (l : Fin d) :
      eLpNorm (gaussianDerivativeAverage hd Q s hs 1 (fun _ => l)
        (∫ r in Icc (0 : ℝ) (t : ℝ), ∑ k,
          complexCoefficientMul Q l k ((hP 0).gradientOrbit (β i) r k))) q (reducedLaw Q) ≤
      ENNReal.ofReal (((d : ℝ)*Cc+2*Cr)*(t : ℝ)*z) := by
    rw [(hP 0).integral_flux_gradientOrbit]
    change eLpNorm (gaussianDerivativeAverage hd Q s hs 1 (fun _ => l) (H l)) q _ ≤ _
    rw [c6_gaussian_coefficient_row_derivative hd D Q hQ β hβ U (fun k => V k)
      ((hP 0).integral_orbit_gradient (β i) t) l (H l) (M l U) (hHG l) (hM l U) s hs l]
    have hc := c6_bound_sum (reducedLaw Q) q hq _ (by positivity : 0 ≤ (Cc*z)*(t : ℝ)) (hcoefU l)
    have hr := c6_bound_complex_smul (reducedLaw Q) q (2 : ℂ) _ (hdriftU l)
    norm_num only [Complex.norm_ofNat] at hr
    have hb := c6_bound_sub (reducedLaw Q) q hq _ _
      (by positivity : 0 ≤ (Fintype.card (Fin d) : ℝ)*((Cc*z)*(t : ℝ)))
      (by positivity : 0 ≤ 2*((Cr*z)*(t : ℝ))) hc hr
    convert hb using 1 <;> simp only [Fintype.card_fin] <;> congr 1 <;> ring
  have hsum := c6_bound_sum (reducedLaw Q) q hq _
    (by positivity : 0 ≤ ((d : ℝ)*Cc+2*Cr)*(t : ℝ)*z) hrow
  have hhalf := c6_bound_smul (reducedLaw Q) q (1/2) _ hsum
  norm_num only [abs_div, abs_one, abs_of_pos (by norm_num : (0 : ℝ) < 2), Fintype.card_fin] at hhalf
  rw [c6_flux_increment hd (hP 0) hβ ha t i s hs]
  apply (c6_bound_add (reducedLaw Q) q hq _ _ (mul_nonneg hCi.le hz)
    (by positivity) (hinit Q hQ β hβ i s hs) hhalf).trans
  apply ENNReal.ofReal_le_ofReal
  have hb := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left ht (show 0 ≤ (d : ℝ)*((d : ℝ)*Cc+2*Cr) by positivity)) hz
  dsimp only [C]
  have hn : 0 ≤ (d : ℝ)*((d : ℝ)*Cc+2*Cr)*(t : ℝ)*z := by positivity
  nlinarith only [hb, hn, mul_nonneg hCs0 hz, hz]

end EinsteinFull.Blueprint
