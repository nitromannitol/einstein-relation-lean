import EinsteinFull.Calculus.ParabolicLibraryBridgeAffine

/-!
# Affine images of energy-class functions and weak solutions
-/

noncomputable section
namespace EinsteinFull.ParabolicBridge

open MeasureTheory Set PDE

variable {d : ℕ}

theorem integrableOn_of_L2c {U : Set (Vec d)} {ψ : Vec d → ℝ} (hψ : IsL2c U ψ) :
    IntegrableOn ψ U volume := by
  obtain ⟨K, hK, hKU, hz⟩ := hψ.2
  haveI : IsFiniteMeasure (volume.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  have h := integrableOn_mul_of_supported hKU (f := fun _ => (1 : ℝ)) (memLp_const 1) hψ.1 hz
  simpa using h

theorem vecDot_smul_left' (c : ℝ) (x y : Vec d) : vecDot (c • x) y = c * vecDot x y := by
  simp only [vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem matVecMul_smul' (A : Mat d) (c : ℝ) (v : Vec d) :
    matVecMul A (c • v) = c • matVecMul A v := by
  funext i
  simp [matVecMul, Finset.mul_sum, mul_left_comm]

/-- The affine image `μ + λ u` of an energy-class function on a domain of finite measure. -/
def affineParH1 {U : Set (Vec d)} {I : Set ℝ} (hI : MeasurableSet I)
    (hfin : volume (U ×ˢ I) ≠ ⊤) (μ lam : ℝ) (u : ParH1Function U I) : ParH1Function U I where
  toFun z := μ + lam * u.toFun z
  grad z := lam • u.grad z
  memL2 := by
    haveI : IsFiniteMeasure (volume.restrict (U ×ˢ I)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hfin.lt_top⟩
    exact (memLp_const μ).add (u.memL2.const_mul lam)
  gradMemL2 i := (u.gradMemL2 i).const_mul lam
  sliceWeakGradient := by
    filter_upwards [u.sliceWeakGradient, ae_restrict_mem hI] with t ht htI
    refine hasWeakGradientOn_affine μ lam ht ?_
    intro K hK hKU
    haveI : IsFiniteMeasure (volume.restrict K) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
    exact (u.sliceL2loc t htI K hK hKU).integrable one_le_two
  sliceL2loc := by
    intro t ht K hK hKU
    haveI : IsFiniteMeasure (volume.restrict K) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
    exact (memLp_const μ).add ((u.sliceL2loc t ht K hK hKU).const_mul lam)
  weakCont := by
    intro ψ hψ
    have hcont := u.weakCont ψ hψ
    obtain ⟨K, hK, hKU, hz⟩ := hψ.2
    refine (continuousOn_const (c := μ * ∫ x in U, ψ x ∂volume)).add
      (continuousOn_const (c := lam).mul hcont) |>.congr ?_
    intro t ht
    have hu1 : IntegrableOn (fun x => u.toFun (x, t) * ψ x) U volume :=
      integrableOn_mul_of_supported hKU (u.sliceL2loc t ht K hK hKU) hψ.1 hz
    have hu2 : IntegrableOn ψ U volume := integrableOn_of_L2c hψ
    have e : (fun x => (μ + lam * u.toFun (x, t)) * ψ x) =
        fun x => μ * ψ x + lam * (u.toFun (x, t) * ψ x) := by
      funext x; ring
    show ∫ x in U, (μ + lam * u.toFun (x, t)) * ψ x ∂volume = _
    rw [e, integral_add (hu2.const_mul μ) (hu1.const_mul lam), integral_const_mul,
      integral_const_mul]
    rfl

/-- The affine image of a weak solution is a weak solution. -/
theorem isParabolicWeakSolution_affine {a : ParCoeffField d} {U : Set (Vec d)} {I : Set ℝ}
    (hI : MeasurableSet I) (hfin : volume (U ×ˢ I) ≠ ⊤) (μ lam : ℝ) (u : ParH1Function U I)
    (hu : IsParabolicWeakSolution a U I u) :
    IsParabolicWeakSolution a U I (affineParH1 hI hfin μ lam u) := by
  intro φ
  obtain ⟨hint, hzero⟩ := hu φ
  have hφ1 : ContDiff ℝ 1 φ.toFun := φ.contDiff
  have hdt : Continuous (parTimeDeriv φ.toFun) :=
    (hφ1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdtc : HasCompactSupport (parTimeDeriv φ.toFun) := φ.hasCompactSupport.fderiv_apply ℝ _
  have hdtint : IntegrableOn (parTimeDeriv φ.toFun) (U ×ˢ I) volume :=
    (hdt.integrable_of_hasCompactSupport hdtc).integrableOn
  have hpt : ∀ z, parWeakIntegrand a (affineParH1 hI hfin μ lam u) φ.toFun z =
      lam * parWeakIntegrand a u φ.toFun z - μ * parTimeDeriv φ.toFun z := by
    intro z
    simp only [parWeakIntegrand, affineParH1, matVecMul_smul', vecDot_smul_left']
    ring
  have hzdt : ∫ z in U ×ˢ I, parTimeDeriv φ.toFun z ∂volume = 0 := by
    haveI : (volume : Measure (Vec d × ℝ)).IsAddHaarMeasure := by
      rw [Measure.volume_eq_prod]
      infer_instance
    have hvan : ∀ z, z ∉ U ×ˢ I → parTimeDeriv φ.toFun z = 0 := by
      intro z hz
      have hzs : z ∉ tsupport φ.toFun := fun h =>
        hz (prod_mono subset_rfl interior_subset (φ.tsupport_subset h))
      simp [parTimeDeriv, fderiv_of_notMem_tsupport (𝕜 := ℝ) hzs]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hvan]
    exact integral_fderiv_eq_zero_of_compactSupport hφ1 φ.hasCompactSupport _
  constructor
  · exact ((hint.const_mul lam).sub (hdtint.const_mul μ)).congr
      (Filter.Eventually.of_forall fun z => (hpt z).symm)
  · have e2 : ∫ z in U ×ˢ I, parWeakIntegrand a (affineParH1 hI hfin μ lam u) φ.toFun z ∂volume =
        ∫ z in U ×ˢ I, (lam * parWeakIntegrand a u φ.toFun z - μ * parTimeDeriv φ.toFun z)
          ∂volume :=
      integral_congr_ae (Filter.Eventually.of_forall hpt)
    rw [e2, integral_sub (hint.const_mul lam) (hdtint.const_mul μ), integral_const_mul,
      integral_const_mul, hzero, hzdt]
    ring

/-- Solutions are supersolutions. -/
theorem solution_supersolution {a : ParCoeffField d} {U : Set (Vec d)}
    {I : Set ℝ} {u : ParH1Function U I} (hu : IsParabolicWeakSolution a U I u) :
    IsParabolicWeakSupersolution a U I u := by
  intro φ _
  obtain ⟨h1, h2⟩ := hu φ
  exact ⟨h1, h2.ge⟩

end EinsteinFull.ParabolicBridge
