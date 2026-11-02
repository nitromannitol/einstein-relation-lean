import EinsteinFull.Calculus.C3JointLocalizationSupport
import EinsteinFull.Calculus.C3CoarseSignedMeasurability
import EinsteinFull.Blueprint.G3.node_p_u3A_covariance_u23_joint_u2D_localization
import EinsteinFull.Calculus.C3CoarseCenteringContraction

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull EinsteinRelation.External.AKM

open EinsteinFull.External.Source.AKM
open EinsteinRelation.Environment.AKMTestIntegralSupport
attribute [local irreducible] covarianceSourceLocalizedEnergy

/-- An elementary two-error domination bound in literal scalar L². -/
private theorem c10_two_error_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {f A B : Ω → ℝ} {c T : ℝ}
    (hc : 0 ≤ c) (hT : 0 ≤ T) (hf : MemLp f 2 P)
    (hA : MemLp A 2 P) (hB : MemLp B 2 P)
    (hdom : ∀ ω, |f ω| ≤ c * (|A ω| + |B ω|))
    (hAb : Real.sqrt (∫ ω, A ω ^ 2 ∂P) ≤ T)
    (hBb : Real.sqrt (∫ ω, B ω ^ 2 ∂P) ≤ T) :
    Real.sqrt (∫ ω, f ω ^ 2 ∂P) ≤ 2 * c * T := by
  have hi : (∫ ω, f ω ^ 2 ∂P) ≤
      2 * c ^ 2 * ((∫ ω, A ω ^ 2 ∂P) + ∫ ω, B ω ^ 2 ∂P) := by
    calc
      _ ≤ ∫ ω, 2 * c ^ 2 * (A ω ^ 2 + B ω ^ 2) ∂P := by
        apply integral_mono hf.integrable_sq
          ((hA.integrable_sq.add hB.integrable_sq).const_mul _)
        intro ω
        have hh := hdom ω
        have ha := abs_nonneg (A ω)
        have hb := abs_nonneg (B ω)
        have hab := sq_nonneg (|A ω| - |B ω|)
        have hf0 := abs_nonneg (f ω)
        have hs : |f ω| ^ 2 ≤ (c * (|A ω| + |B ω|)) ^ 2 :=
          sq_le_sq₀ hf0 (mul_nonneg hc (add_nonneg ha hb)) |>.2 hh
        have hab2 : (|A ω| + |B ω|) ^ 2 ≤ 2 * (A ω ^ 2 + B ω ^ 2) := by
          nlinarith [sq_abs (A ω), sq_abs (B ω)]
        calc
          _ = |f ω| ^ 2 := (sq_abs _).symm
          _ ≤ c ^ 2 * (|A ω| + |B ω|) ^ 2 := by simpa only [mul_pow] using hs
          _ ≤ _ := by
            convert mul_le_mul_of_nonneg_left hab2 (sq_nonneg c) using 1
            dsimp only [Pi.add_apply]
            ring
      _ = _ := by rw [integral_const_mul, integral_add hA.integrable_sq hB.integrable_sq]
  have hAs : (Real.sqrt (∫ ω, A ω ^ 2 ∂P)) ^ 2 = ∫ ω, A ω ^ 2 ∂P :=
    Real.sq_sqrt (integral_nonneg fun ω => sq_nonneg (A ω))
  have hBs : (Real.sqrt (∫ ω, B ω ^ 2 ∂P)) ^ 2 = ∫ ω, B ω ^ 2 ∂P :=
    Real.sq_sqrt (integral_nonneg fun ω => sq_nonneg (B ω))
  have hAA : (∫ ω, A ω ^ 2 ∂P) ≤ T ^ 2 := by
    nlinarith [Real.sqrt_nonneg (∫ ω, A ω ^ 2 ∂P)]
  have hBB : (∫ ω, B ω ^ 2 ∂P) ≤ T ^ 2 := by
    nlinarith [Real.sqrt_nonneg (∫ ω, B ω ^ 2 ∂P)]
  apply (Real.sqrt_le_iff).2
  refine ⟨by positivity, ?_⟩
  nlinarith [mul_nonneg (sq_nonneg c) (sub_nonneg.mpr hAA),
    mul_nonneg (sq_nonneg c) (sub_nonneg.mpr hBB)]

/-- Uncentered selected polarization in physical coefficient units. -/
private def c10UncenteredEntry (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (r : ℝ) (x : Vec d) (j k : Fin d) : FieldPair d → ℝ :=
  covariancePhysicalLift Q (fun a => (ellipticityScale D.ellipticity)⁻¹ *
    (covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q a
      (D.dependenceRange⁻¹ • x) (r / D.dependenceRange)
      (unitVector j + unitVector k)
      ((ellipticityScale D.ellipticity • homogenizedCoefficient Q).mulVec (unitVector j)) -
    covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q a
      (D.dependenceRange⁻¹ • x) (r / D.dependenceRange)
      (unitVector j - unitVector k)
      ((ellipticityScale D.ellipticity • homogenizedCoefficient Q).mulVec (unitVector j))) / 2)

private theorem c10_uncentered_memLp
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (r : ℝ) (x : Vec d) (j k : Fin d) :
    MemLp (c10UncenteredEntry d hd D s δ γ η β h Q r x j k) 2 (reducedLaw Q) := by
  let := actualCoefficientLaw_probability Q
  let z := D.dependenceRange⁻¹ • x
  let ρ := r / D.dependenceRange
  let q := (ellipticityScale D.ellipticity • homogenizedCoefficient Q).mulVec (unitVector j)
  have hm (p : Vec d) := (covarianceSourceLocalizedEnergy_joint_measurable_real
    d hd D s δ γ η β h Q ρ p q).comp
      (measurable_const.prodMk measurable_id : Measurable
        (fun a : Coefficient d (AKMUpperEllipticity D.ellipticity) => (z, a)))
  have hL (p : Vec d) := covarianceSourceLocalizedEnergy_memLp
    d hd D s δ γ η β h Q (actualCoefficientLaw Q) 2 z ρ p q
  apply covariancePhysicalLift_memLp
  · exact (((hm _).sub (hm _)).const_mul _).div_const 2
  · simpa only [div_eq_mul_inv, Pi.sub_apply, z, ρ, q] using
      (((hL (unitVector j + unitVector k)).sub
        (hL (unitVector j - unitVector k))).const_mul
          (ellipticityScale D.ellipticity)⁻¹).mul_const (2 : ℝ)⁻¹

private theorem c10_polarization_abs (c lp ln gp gn : ℝ) (hc : 0 ≤ c) :
    |c * (lp - ln) / 2 - c * ((gp - gn) / 2)| ≤
      c * (|gp - lp| + |gn - ln|) := by
  calc
    _ = (c / 2) * |(gn - ln) - (gp - lp)| := by
      rw [← abs_of_nonneg (div_nonneg hc (by norm_num)), ← abs_mul]
      congr 1
      ring
    _ ≤ (c / 2) * (|gn - ln| + |gp - lp|) :=
      mul_le_mul_of_nonneg_left (abs_sub _ _) (div_nonneg hc (by norm_num))
    _ ≤ _ := by nlinarith [mul_nonneg hc (abs_nonneg (gp - lp)),
      mul_nonneg hc (abs_nonneg (gn - ln))]

/-- The actual uncentered selected entry approximates the actual coarse entry,
with a constant chosen before the environment law. -/
private theorem c10_uncentered_error_rate
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β) :
    ∃ C : ℝ, 0 < C ∧
    ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      HasSmoothBounds D Q → ∀ r : ℝ, 2 * D.dependenceRange ≤ r →
      ∀ (x : Vec d) (j k : Fin d),
        MemLp (fun ω => c10UncenteredEntry d hd D s δ γ η β h Q r x j k ω -
          covarianceCoarseEntry D Q r x j k ω) 2 (reducedLaw Q) ∧
        Real.sqrt (∫ ω, (c10UncenteredEntry d hd D s δ γ η β h Q r x j k ω -
          covarianceCoarseEntry D Q r x j k ω) ^ 2 ∂reducedLaw Q) ≤ C * r ^ (-γ) := by
  obtain ⟨C, hC, hbound⟩ := covariancePhysicalPolarization_abs_error_l2
    d hd D s δ γ η β h
  have hc : 0 < (ellipticityScale D.ellipticity)⁻¹ :=
    inv_pos.mpr (ellipticityScale_pos D.one_le_ellipticity)
  refine ⟨2 * (ellipticityScale D.ellipticity)⁻¹ * C, by positivity, ?_⟩
  intro Q hQ r hr x j k
  have hr' : D.dependenceRange ≤ r := by linarith [D.one_le_dependenceRange]
  have hrpos : 0 ≤ r := by linarith [D.one_le_dependenceRange]
  have hm := coarseEntry_signed_aestronglyMeasurable d hd D Q hQ r hr' x j k
  have hf := (c10_uncentered_memLp d hd D s δ γ η β h Q r x j k).sub
    ((covarianceCoarse_entry_memLp_four hd D Q r hr' x j k hm).mono_exponent
      (by norm_num : (2 : ENNReal) ≤ 4))
  refine ⟨hf, ?_⟩
  let A (ε : ℝ) := covariancePhysicalLift Q (fun a =>
    |gaussianEnergyJ1 a (D.dependenceRange⁻¹ • x) (r / D.dependenceRange)
      (unitVector j + ε • unitVector k)
      ((ellipticityScale D.ellipticity • homogenizedCoefficient Q).mulVec (unitVector j)) -
    covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q a
      (D.dependenceRange⁻¹ • x) (r / D.dependenceRange)
      (unitVector j + ε • unitVector k)
      ((ellipticityScale D.ellipticity • homogenizedCoefficient Q).mulVec (unitVector j))|)
  have hp := hbound Q r hr x j k 1 (by norm_num)
  have hn := hbound Q r hr x j k (-1) (by norm_num)
  have hdom (ω : FieldPair d) :
      |c10UncenteredEntry d hd D s δ γ η β h Q r x j k ω -
        covarianceCoarseEntry D Q r x j k ω| ≤
      (ellipticityScale D.ellipticity)⁻¹ * (|A 1 ω| + |A (-1) ω|) := by
    dsimp only [c10UncenteredEntry, covariancePhysicalLift, covarianceCoarseEntry, A]
    split_ifs with hω
    · simp only [one_smul, neg_smul,
        sub_eq_add_neg, abs_abs, coarsenedCoefficient]
      exact c10_polarization_abs _ _ _ _ _ hc.le
    · simp
  have hb := c10_two_error_bound hc.le (mul_nonneg hC.le (Real.rpow_nonneg hrpos _))
    hf hp.1 hn.1 hdom hp.2 hn.2
  simpa only [mul_assoc, Pi.sub_apply] using hb

/-- Centering the actual uncentered error gives precisely the selected local
entry minus the centered coarse entry, on the full-measure physical range. -/
private theorem c10_centered_error_eq
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (r : ℝ) (hr : 2 * D.dependenceRange ≤ r) (x : Vec d) (j k : Fin d) :
    (fun ω => covarianceLocalizedEntry d hd D s δ γ η β h Q r x j k ω -
      covarianceCenteredCoarseEntry D Q r x j k ω) =ᵐ[reducedLaw Q]
    (fun ω => (c10UncenteredEntry d hd D s δ γ η β h Q r x j k ω -
      covarianceCoarseEntry D Q r x j k ω) -
      ∫ ω, (c10UncenteredEntry d hd D s δ γ η β h Q r x j k ω -
        covarianceCoarseEntry D Q r x j k ω) ∂reducedLaw Q) := by
  let := actualCoefficientLaw_probability Q
  let z := D.dependenceRange⁻¹ • x
  let ρ := r / D.dependenceRange
  let q := (ellipticityScale D.ellipticity • homogenizedCoefficient Q).mulVec (unitVector j)
  let L (p : Vec d) := fun a => covarianceSourceLocalizedEnergy d hd D s δ γ η β h Q a z ρ p q
  have hmL (p : Vec d) : Measurable (L p) :=
    (covarianceSourceLocalizedEnergy_joint_measurable_real
      d hd D s δ γ η β h Q ρ p q).comp (measurable_const.prodMk measurable_id)
  have hiL (p : Vec d) : Integrable (L p) (actualCoefficientLaw Q) :=
    memLp_one_iff_integrable.mp (covarianceSourceLocalizedEnergy_memLp
      d hd D s δ γ η β h Q (actualCoefficientLaw Q) 1 z ρ p q)
  have hU := covariancePhysicalLift_polarization_integral Q
    (L (unitVector j + unitVector k)) (L (unitVector j - unitVector k))
    (ellipticityScale D.ellipticity)⁻¹ (hmL _) (hmL _) (hiL _) (hiL _)
  have hr' : D.dependenceRange ≤ r := by linarith [D.one_le_dependenceRange]
  have hm := coarseEntry_signed_aestronglyMeasurable d hd D Q hQ r hr' x j k
  have hK := (covarianceCoarse_entry_memLp_four hd D Q r hr' x j k hm).mono_exponent
    (by norm_num : (2 : ENNReal) ≤ 4)
  have hUi := (c10_uncentered_memLp d hd D s δ γ η β h Q r x j k).integrable
    (by norm_num : (1 : ENNReal) ≤ 2)
  have hKi := hK.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hsupport : ∀ᵐ ω ∂reducedLaw Q,
      ω ∈ ReductionImageV3.physicalReducedRange D.ellipticity := by
    have hpres := covariancePhysicalReduction_measurePreserving Q
    rw [← hpres.map_eq]
    apply (ae_map_iff hpres.measurable.aemeasurable
      (ReductionImageV3.measurableSet_physicalReducedRange D.ellipticity)).2
    exact Filter.Eventually.of_forall fun ω => ⟨ω.1, ω.2, rfl⟩
  rw [covarianceCoarse_centered_eq_sub_integral D Q r x j k hm]
  filter_upwards [hsupport] with ω hω
  rw [integral_sub hUi hKi]
  change covarianceLocalizedEntry d hd D s δ γ η β h Q r x j k ω -
    (covarianceCoarseEntry D Q r x j k ω - _) =
    (c10UncenteredEntry d hd D s δ γ η β h Q r x j k ω -
      covarianceCoarseEntry D Q r x j k ω) -
    ((∫ ω, c10UncenteredEntry d hd D s δ γ η β h Q r x j k ω ∂reducedLaw Q) - _)
  rw [show (∫ ω, c10UncenteredEntry d hd D s δ γ η β h Q r x j k ω ∂reducedLaw Q) =
      (ellipticityScale D.ellipticity)⁻¹ *
        ((∫ a, L (unitVector j + unitVector k) a ∂actualCoefficientLaw Q) -
          ∫ a, L (unitVector j - unitVector k) a ∂actualCoefficientLaw Q) / 2 from hU]
  simp only [covarianceLocalizedEntry, c10UncenteredEntry, covariancePhysicalLift,
    dite_eq_left hω, centeredLocalizedEnergy]
  change (ellipticityScale D.ellipticity)⁻¹ *
    ((L (unitVector j + unitVector k) _ - _) -
      (L (unitVector j - unitVector k) _ - _)) / 2 - (_ - _) = _
  ring

/-- The literal selected matrix error has uniform physical L² decay. -/
theorem covariance_joint_localization_centered_error :
∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β),
    ∃ C : ℝ, 0 < C ∧
    ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      HasSmoothBounds D Q → ∀ r : ℝ, 2 * D.dependenceRange ≤ r →
      ∀ x : Vec d,
        let error := fun ω : FieldPair d => fun a : JointObservationIndex d =>
          match a with
          | .inl (j,k) => covarianceLocalizedField d hd D s δ γ η β h Q r x ω a -
              covarianceCenteredCoarseEntry D Q r x j k ω
          | .inr _ => 0
        MemLp (fun ω => covarianceVectorSize (error ω)) 2 (reducedLaw Q) ∧
        covarianceL2Size (reducedLaw Q) error ≤ C * r ^ (-γ)
 := by
  classical
  intro d hd D s δ γ η β h
  obtain ⟨C, hC, hraw⟩ := c10_uncentered_error_rate d hd D s δ γ η β h
  refine ⟨(Real.sqrt (Fintype.card (JointObservationIndex d) : ℝ) + 1) * C,
    by positivity, ?_⟩
  intro Q hQ r hr x
  have hrpos : 0 ≤ r := by linarith [D.one_le_dependenceRange]
  let error := fun ω : FieldPair d => fun a : JointObservationIndex d =>
    match a with
    | .inl (j,k) => covarianceLocalizedField d hd D s δ γ η β h Q r x ω a -
        covarianceCenteredCoarseEntry D Q r x j k ω
    | .inr _ => 0
  change MemLp (fun ω => covarianceVectorSize (error ω)) 2 (reducedLaw Q) ∧
    covarianceL2Size (reducedLaw Q) error ≤ _
  have hcoords (a : JointObservationIndex d) :
      MemLp (fun ω => error ω a) 2 (reducedLaw Q) ∧
      Real.sqrt (∫ ω, (error ω a) ^ 2 ∂reducedLaw Q) ≤ C * r ^ (-γ) := by
    rcases a with ⟨j, k⟩ | a
    · obtain ⟨hm, hb⟩ := hraw Q hQ r hr x j k
      obtain ⟨hcm, hcb⟩ := coarseCentered_secondMoment_le hm
      have heq := c10_centered_error_eq d hd D s δ γ η β h Q hQ r hr x j k
      refine ⟨hcm.ae_eq heq.symm, ?_⟩
      change Real.sqrt (∫ ω, (covarianceLocalizedEntry d hd D s δ γ η β h Q r x j k ω -
        covarianceCenteredCoarseEntry D Q r x j k ω) ^ 2 ∂reducedLaw Q) ≤ _
      calc
        _ = Real.sqrt (∫ ω, ((c10UncenteredEntry d hd D s δ γ η β h Q r x j k ω -
            covarianceCoarseEntry D Q r x j k ω) -
            ∫ ω, (c10UncenteredEntry d hd D s δ γ η β h Q r x j k ω -
              covarianceCoarseEntry D Q r x j k ω) ∂reducedLaw Q) ^ 2 ∂reducedLaw Q) :=
          congrArg Real.sqrt (integral_congr_ae (heq.mono fun _ he => congrArg (· ^ 2) he))
        _ ≤ _ := (Real.sqrt_le_sqrt hcb).trans hb
    · refine ⟨memLp_const 0, ?_⟩
      simpa only [error, zero_pow (by norm_num : (2 : ℕ) ≠ 0), integral_zero,
        Real.sqrt_zero] using (mul_nonneg hC.le (Real.rpow_nonneg hrpos (-γ)))
  refine ⟨(coarseFiniteVector_secondMoment (fun a => (hcoords a).1)).1, ?_⟩
  change Real.sqrt (∫ ω, (Real.sqrt (∑ a, (error ω a) ^ 2)) ^ 2 ∂reducedLaw Q) ≤ _
  calc
    _ ≤ Real.sqrt (Fintype.card (JointObservationIndex d) : ℝ) * (C * r ^ (-γ)) :=
      coarseFiniteVector_L2_le (mul_nonneg hC.le (Real.rpow_nonneg hrpos _))
        (fun a => (hcoords a).1) (fun a => (hcoords a).2)
    _ ≤ _ := by
      have ht := mul_nonneg hC.le (Real.rpow_nonneg hrpos (-γ))
      nlinarith

#print axioms covariance_joint_localization_centered_error
#lint
end EinsteinFull.Blueprint
