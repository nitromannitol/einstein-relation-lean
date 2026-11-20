import EinsteinFull.Homogenization.CoefficientEllipticity
import EinsteinFull.Homogenization.CoefficientCarrier
import Homogenization.Probability.Source.AKL.RegQuotientAdapter
import EinsteinRelation.External.AKMEnergyDensity
import HCPoly.Frozen.Stationarity
import HCPoly.Frozen.UnitRange

/-!
# The high-contrast coefficient space of a source coefficient

A coefficient of Armstrong, Kuusi and Mourrat, *Quantitative Stochastic Homogenization and
Large-Scale Regularity*, (0.6)–(0.11), defines a point of the coefficient space of Armstrong,
Kuusi and Loher, *Homogenization at a polynomial scale in high contrast*, after the spatial
dilation `x ↦ 2x`. The dilation turns the Euclidean range of dependence of the source law,
which requires a gap strictly larger than one, into the unit range of dependence for the
sup-distance used there; it preserves stationarity under integer translations.

The map is measurable for the test-integral sigma algebras, and the pushforward of a source law
is a stationary probability law of unit range.
-/

open MeasureTheory
open scoped Pointwise

namespace EinsteinFull.Homogenization

open EinsteinRelation EinsteinRelation.Environment.AKMTestIntegralSupport
  EinsteinRelation.External.AKM

variable {d : ℕ} {K : ℝ}

/-- The representative field of a source coefficient dilated by two, `x ↦ a(2x)`. -/
noncomputable def dilatedField (a : Coefficient d K) (x : Vec d) : Mat d :=
  (regularCoefficient a).toFun ((2 : ℝ) • x)

theorem aestronglyMeasurable_dilatedField (a : Coefficient d K) :
    AEStronglyMeasurable (dilatedField a) volume :=
  (_root_.Homogenization.Source.AKL.aestronglyMeasurable_regularField
    (regularCoefficient a)).comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_smul (volume : Measure (Vec d)) two_ne_zero)

/-- The dilated representative agrees almost everywhere with the dilated coefficient. -/
theorem dilatedField_ae_eq (a : Coefficient d K) :
    dilatedField a =ᵐ[volume] fun x => a.field ((2 : ℝ) • x) :=
  (Measure.quasiMeasurePreserving_smul (volume : Measure (Vec d)) two_ne_zero).ae_eq_comp
    (regularCoefficient_ae_eq a)

theorem ae_isEllipticMatrix_dilatedField (hK : 1 ≤ K) (a : Coefficient d K) :
    ∀ᵐ x ∂(volume : Measure (Vec d)),
      _root_.Homogenization.IsEllipticMatrix 1 K (dilatedField a x) := by
  filter_upwards [dilatedField_ae_eq a] with x hx
  rw [hx]
  exact source_isEllipticMatrix a hK le_rfl _

/-- The high-contrast coefficient-space point of a source coefficient, dilated by two. -/
noncomputable def toHighContrast (hK : 1 ≤ K) (a : Coefficient d K) :
    _root_.Homogenization.HighContrast.CoeffSpace d :=
  ⟨AEEqFun.mk (dilatedField a) (aestronglyMeasurable_dilatedField a),
    _root_.Homogenization.HighContrast.aeUniformlyEllipticField_of_ae_isEllipticMatrix
      one_pos hK (by
        filter_upwards [AEEqFun.coeFn_mk (dilatedField a)
          (aestronglyMeasurable_dilatedField a),
          ae_isEllipticMatrix_dilatedField hK a] with x hx hell
        rw [hx]
        exact hell)⟩

theorem toHighContrast_ae_eq (hK : 1 ≤ K) (a : Coefficient d K) :
    ((toHighContrast hK a).1 : Vec d → Mat d) =ᵐ[volume]
      fun x => a.field ((2 : ℝ) • x) :=
  (AEEqFun.coeFn_mk _ _).trans (dilatedField_ae_eq a)

theorem ae_isEllipticMatrix_toHighContrast (hK : 1 ≤ K) (a : Coefficient d K) :
    ∀ᵐ x ∂(volume : Measure (Vec d)),
      _root_.Homogenization.IsEllipticMatrix 1 K ((toHighContrast hK a).1 x) := by
  filter_upwards [toHighContrast_ae_eq hK a] with x hx
  rw [hx]
  exact source_isEllipticMatrix a hK le_rfl _

/-- The smooth test `y ↦ φ(y/2)`. -/
noncomputable def halfDilatedTest (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) : SmoothCompactTest d where
  toFun := fun y => φ ((2 : ℝ)⁻¹ • y)
  smooth := hφ.comp (contDiff_const_smul _)
  compact := hc.comp_smul (inv_ne_zero two_ne_zero)

theorem tsupport_halfDilatedTest_subset (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) {U : Set (Vec d)} (hU : tsupport φ ⊆ U) :
    tsupport (halfDilatedTest φ hφ hc).toFun ⊆ (2 : ℝ) • U := by
  refine (closure_minimal ?_ ((isClosed_tsupport φ).smul₀ (2 : ℝ))).trans
    (Set.smul_set_mono hU)
  intro y hy
  refine ⟨(2 : ℝ)⁻¹ • y, subset_tsupport φ hy, ?_⟩
  simp [smul_smul]

/-- The observation of the dilated coefficient is an observation of the source coefficient. -/
theorem coeffPairing_toHighContrast (hK : 1 ≤ K) (e e' : Vec d) (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) (a : Coefficient d K) :
    _root_.Homogenization.HighContrast.coeffPairing e e' φ (toHighContrast hK a) =
      ((2 : ℝ) ^ d)⁻¹ * ∑ i : Fin d, ∑ j : Fin d,
        e' i * e j * testIntegral a (halfDilatedTest φ hφ hc) i j := by
  let ψ := halfDilatedTest φ hφ hc
  let F : Vec d → ℝ := fun y =>
    _root_.Homogenization.vecDot e' (_root_.Homogenization.matVecMul (a.field y) e) * ψ y
  have h1 : _root_.Homogenization.HighContrast.coeffPairing e e' φ (toHighContrast hK a) =
      ∫ x, F ((2 : ℝ) • x) := by
    unfold _root_.Homogenization.HighContrast.coeffPairing
    refine integral_congr_ae ?_
    filter_upwards [toHighContrast_ae_eq hK a] with x hx
    simp only [F, ψ, halfDilatedTest, hx, smul_smul]
    norm_num
  have h2 : ∫ x, F ((2 : ℝ) • x) = ((2 : ℝ) ^ d)⁻¹ * ∫ y, F y := by
    rw [Measure.integral_comp_smul, Module.finrank_fin_fun, smul_eq_mul]
    congr 1
    rw [abs_of_pos (by positivity)]
  have hint (i j : Fin d) : Integrable (fun y => e' i * e j * (ψ y * a.field y i j)) := by
    exact (integrable_testIntegrand a ψ i j).const_mul _
  have h3 : ∫ y, F y = ∑ i : Fin d, ∑ j : Fin d, e' i * e j * testIntegral a ψ i j := by
    have hF : F = fun y => ∑ i : Fin d, ∑ j : Fin d, e' i * e j * (ψ y * a.field y i j) := by
      funext y
      simp only [F, _root_.Homogenization.vecDot, _root_.Homogenization.matVecMul,
        Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hF, integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hint i j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun j _ => hint i j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
    rfl
  rw [h1, h2, h3]

/-- Each observation of the dilated coefficient on `U` is measurable for the source local
sigma algebra of `2U`. -/
theorem measurable_coeffPairing_toHighContrast (hK : 1 ≤ K) (e e' : Vec d) {U : Set (Vec d)}
    {φ : Vec d → ℝ} (hφ : _root_.Homogenization.HighContrast.IsLocalTest U φ) :
    @Measurable (Coefficient d K) ℝ
      (Environment.AKMTestIntegralSupport.localSigma ((2 : ℝ) • U)) inferInstance
      (fun a => _root_.Homogenization.HighContrast.coeffPairing e e' φ
        (toHighContrast hK a)) := by
  simp_rw [coeffPairing_toHighContrast hK e e' φ hφ.contDiff hφ.hasCompactSupport]
  let ψ := halfDilatedTest φ hφ.contDiff hφ.hasCompactSupport
  have hψ : tsupport ψ.toFun ⊆ (2 : ℝ) • U :=
    tsupport_halfDilatedTest_subset φ hφ.contDiff hφ.hasCompactSupport hφ.tsupport_subset
  have hm (i j : Fin d) : @Measurable (Coefficient d K) ℝ
      (Environment.AKMTestIntegralSupport.localSigma ((2 : ℝ) • U))
      inferInstance (fun a => testIntegral a ψ i j) := by
    rw [measurable_iff_comap_le]
    exact le_iSup_of_le ⟨ψ, hψ⟩ (le_iSup_of_le i (le_iSup_of_le j le_rfl))
  refine Measurable.const_mul ?_ _
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  exact (hm i j).const_mul _

/-- The local sigma algebra of `U` pulls back into the source local sigma algebra of `2U`. -/
theorem comap_coeffSigma_toHighContrast_le (hK : 1 ≤ K) (U : Set (Vec d)) :
    (_root_.Homogenization.HighContrast.coeffSigma d U).comap (toHighContrast hK) ≤
      Environment.AKMTestIntegralSupport.localSigma (K := K) ((2 : ℝ) • U) := by
  unfold _root_.Homogenization.HighContrast.coeffSigma
  rw [MeasurableSpace.comap_generateFrom]
  refine MeasurableSpace.generateFrom_le ?_
  rintro _ ⟨s, ⟨e, e', φ, hφ, t, ht, rfl⟩, rfl⟩
  exact measurable_coeffPairing_toHighContrast hK e e' hφ ht

theorem localSigma_le_coefficientSigma (U : Set (Vec d)) :
    Environment.AKMTestIntegralSupport.localSigma (K := K) U ≤
      Environment.AKMTestIntegralSupport.coefficientSigma := by
  refine iSup_le fun u => iSup_le fun i => iSup_le fun j => ?_
  exact le_iSup_of_le u.1 (le_iSup_of_le i (le_iSup_of_le j le_rfl))

theorem measurable_toHighContrast (hK : 1 ≤ K) :
    Measurable (toHighContrast (d := d) hK) := by
  rw [measurable_iff_comap_le]
  refine (comap_coeffSigma_toHighContrast_le hK Set.univ).trans ?_
  exact localSigma_le_coefficientSigma _

/-- Dilation by two intertwines the source translation by `2z` with the integer translation
by `z`. -/
theorem toHighContrast_translate (hK : 1 ≤ K) (z : Fin d → ℤ) (a : Coefficient d K) :
    toHighContrast hK (translateCoefficient (latticeShift (2 • z)) a) =
      _root_.Homogenization.HighContrast.translateCoeff z (toHighContrast hK a) := by
  apply Subtype.ext
  apply AEEqFun.ext
  have hshift : ∀ x : Vec d, latticeShift (2 • z) + (2 : ℝ) • x =
      (2 : ℝ) • (x + _root_.Homogenization.Source.AKL.intTranslation z) := by
    intro x
    funext i
    simp only [latticeShift, _root_.Homogenization.Source.AKL.intTranslation, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    push_cast [nsmul_eq_mul]
    ring
  have hτ : MeasurePreserving (fun x : Vec d =>
      x + _root_.Homogenization.Source.AKL.intTranslation z) volume volume :=
    measurePreserving_add_right _ _
  have hR := hτ.quasiMeasurePreserving.ae_eq_comp (toHighContrast_ae_eq hK a)
  refine (toHighContrast_ae_eq hK _).trans ?_
  refine Filter.EventuallyEq.trans ?_
    (_root_.Homogenization.Source.AKL.translateField_ae z (toHighContrast hK a).1).symm
  refine Filter.EventuallyEq.trans ?_ hR.symm
  refine Filter.Eventually.of_forall fun x => ?_
  change a.field (latticeShift (2 • z) + (2 : ℝ) • x) =
    a.field ((2 : ℝ) • (x + _root_.Homogenization.Source.AKL.intTranslation z))
  rw [hshift]

/-- The pushforward of a stationary source law is stationary under integer translations. -/
theorem isStationaryLaw_map_toHighContrast (hK : 1 ≤ K) {P : Measure (Coefficient d K)}
    (hP : LawHypotheses P) :
    HCPoly.Frozen.IsStationaryLaw (P.map (toHighContrast hK)) := by
  intro z
  rw [Measure.map_map (_root_.Homogenization.HighContrast.measurable_translateCoeff z)
    (measurable_toHighContrast hK)]
  have hcomp : (_root_.Homogenization.HighContrast.translateCoeff z ∘ toHighContrast hK) =
      toHighContrast hK ∘ translateCoefficient (latticeShift (2 • z)) := by
    funext a
    exact (toHighContrast_translate hK z a).symm
  rw [hcomp, ← Measure.map_map (measurable_toHighContrast hK)
    (measurable_translateCoefficient _), hP.2.1 (2 • z)]

theorem norm_le_euclideanNorm (w : Vec d) : ‖w‖ ≤ euclideanNorm w := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
  rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
  refine Real.sqrt_le_sqrt ?_
  change w i ^ 2 ≤ ∑ j, w j * w j
  rw [sq]
  exact Finset.single_le_sum (f := fun j => w j * w j) (fun j _ => mul_self_nonneg (w j))
    (Finset.mem_univ i)

/-- The pushforward of a source law has unit range of dependence for the sup-distance. -/
theorem isUnitRangeLaw_map_toHighContrast (hK : 1 ≤ K) {P : Measure (Coefficient d K)}
    (hP : LawHypotheses P) :
    HCPoly.Frozen.IsUnitRangeLaw (P.map (toHighContrast hK)) := by
  intro U V hU hV hsep
  have hsep' : ∃ s : ℝ, 1 < s ∧ ∀ x ∈ (2 : ℝ) • U, ∀ y ∈ (2 : ℝ) • V,
      s ≤ euclideanNorm (x - y) := by
    refine ⟨2, by norm_num, ?_⟩
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    have h1 : (1 : ℝ) ≤ ‖u - v‖ := hsep hu hv
    have h2 := norm_le_euclideanNorm (u - v)
    rw [← smul_sub, euclideanNorm_smul 2 (by norm_num)]
    linarith
  have hind := hP.2.2 _ _ (hU.const_smul_of_ne_zero two_ne_zero)
    (hV.const_smul_of_ne_zero two_ne_zero) hsep'
  rw [ProbabilityTheory.Indep_iff] at hind ⊢
  intro t1 t2 ht1 ht2
  have hglob (W : Set (Vec d)) :
      _root_.Homogenization.HighContrast.coeffSigma d W ≤
        _root_.Homogenization.HighContrast.instMeasurableSpaceCoeffSpace d := by
    unfold _root_.Homogenization.HighContrast.coeffSigma
    refine MeasurableSpace.generateFrom_le ?_
    rintro s ⟨e, e', φ, hφ, t, ht, rfl⟩
    exact MeasurableSpace.measurableSet_generateFrom
      ⟨e, e', φ, ⟨hφ.contDiff, hφ.hasCompactSupport, Set.subset_univ _⟩, t, ht, rfl⟩
  have hm1 : MeasurableSet t1 := hglob U t1 ht1
  have hm2 : MeasurableSet t2 := hglob V t2 ht2
  have hι := measurable_toHighContrast (d := d) hK
  rw [Measure.map_apply hι (hm1.inter hm2), Measure.map_apply hι hm1, Measure.map_apply hι hm2,
    Set.preimage_inter]
  exact hind _ _ (comap_coeffSigma_toHighContrast_le hK U _ ⟨t1, ht1, rfl⟩)
    (comap_coeffSigma_toHighContrast_le hK V _ ⟨t2, ht2, rfl⟩)

theorem isProbabilityMeasure_map_toHighContrast (hK : 1 ≤ K) {P : Measure (Coefficient d K)}
    (hP : LawHypotheses P) : IsProbabilityMeasure (P.map (toHighContrast hK)) :=
  haveI := hP.1
  inferInstance

end EinsteinFull.Homogenization
