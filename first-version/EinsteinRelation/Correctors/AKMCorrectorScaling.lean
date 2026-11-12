import EinsteinRelation.Correctors.AKMWeakNormTesting
import EinsteinRelation.Correctors.SpatialWeakProduct

/-! # Scaling AKM correctors to unit slopes

Source: `paper/main.tex:948–955`; AKM (4.126), printed p. 173,
quantifies slopes in the open unit ball. Scaling the potential and its
actual weak gradient by one half satisfies that condition. The source
mean flux scales with them, so the resulting bounds apply to unit slopes
without a change to the source contract.
-/

open MeasureTheory Filter
open scoped Topology ENNReal

namespace EinsteinRelation.Correctors

open External.AKM Environment.AKMTestIntegralSupport

private theorem locallyIntegrableOn_const_mul {d : ℕ} {U : Set (Vec d)}
    {f : Vec d → ℝ} (hf : LocallyIntegrableOn f U volume) (c : ℝ) :
    LocallyIntegrableOn (fun x => c * f x) U volume :=
  fun x hx => (hf x hx).smul c

/-- Positive scalar multiplication of a spatial weak gradient.
Source: `paper/main.tex:948–955`. -/
theorem hasWeakGradient_const_mul {d : ℕ} {U : Set (Vec d)}
    {f : Vec d → ℝ} {G : Vec d → Vec d} (h : HasWeakGradient U f G) (c : ℝ) :
    HasWeakGradient U (fun x => c * f x) (fun x => c • G x) := by
  intro j
  refine ⟨locallyIntegrableOn_const_mul (h j).1 c,
    locallyIntegrableOn_const_mul (h j).2.1 c, ?_⟩
  intro ψ hψ
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
  rw [(h j).2.2 ψ hψ, mul_neg]

/-- Scalar multiplication of a weak divergence. Source:
`paper/main.tex:948–955`. -/
theorem hasWeakDivergence_const_mul {d : ℕ} {U : Set (Vec d)}
    {F : Vec d → Vec d} {h : Vec d → ℝ} (hF : HasWeakDivergence U F h) (c : ℝ) :
    HasWeakDivergence U (fun x => c • F x) (fun x => c * h x) := by
  refine ⟨fun j => locallyIntegrableOn_const_mul (hF.1 j) c,
    locallyIntegrableOn_const_mul hF.2.1 c, ?_⟩
  intro ψ hψ
  have hdot (x : Vec d) : dot (c • F x) (gradient ψ x) = c * dot (F x) (gradient ψ x) := by
    simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  simp only [hdot, mul_assoc, integral_const_mul]
  rw [hF.2.2 ψ hψ, mul_neg]

/-- Homogeneity of the source's normalized root mean square.
Source: `paper/main.tex:948–955`. -/
theorem scalarRms_const_mul {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (U : Set X) (f : X → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    scalarRms ν U (fun x => c * f x) = c * scalarRms ν U f := by
  unfold scalarRms
  simp_rw [mul_pow]
  rw [average, integral_const_mul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]
  rfl

/-- Scaling preserves every defining property of the source corrector;
zero gradient mean and expected energy are not assumed here.
Source: `paper/main.tex:948–955`. -/
theorem isFirstOrderCorrector_const_mul {d : ℕ} {K : ℝ}
    {P : Measure (Coefficient d K)} {e : Vec d}
    {φ : Coefficient d K → Vec d → ℝ} {G : Coefficient d K → Vec d → Vec d}
    (h : IsFirstOrderCorrector P e φ G) {c : ℝ} (hc : 0 ≤ c) :
    IsFirstOrderCorrector P (c • e) (fun A x => c * φ A x) (fun A x => c • G A x) := by
  refine ⟨⟨measurable_const.smul h.1.1, ?_⟩, ?_⟩
  · intro z
    filter_upwards [h.1.2 z] with A hA
    filter_upwards [hA] with x hx
    exact congrArg (c • ·) hx
  · filter_upwards [h.2] with A hA
    refine ⟨?_, hasWeakGradient_const_mul hA.2.1 c, ?_, ?_⟩
    · intro R hR
      refine ⟨(hA.1 R hR).1.const_mul c, ?_⟩
      simpa only [euclideanNorm_smul c hc] using (hA.1 R hR).2.const_mul c
    · have hd := hasWeakDivergence_const_mul hA.2.2.1 c
      simpa only [← smul_add, Matrix.mulVec_smul, mul_zero] using hd
    · simpa only [scalarRms_const_mul volume _ _ hc, mul_div_assoc, mul_zero] using
        (tendsto_const_nhds.mul hA.2.2.2 :
          Tendsto (fun R => c * (scalarRms volume (originBall d R) (φ A) / R)) atTop (𝓝 (c * 0)))

/-- The lattice-cell mean flux scales together with the slope and gradient.
This does not require an integrability premise: scalar multiplication
commutes even with the total Bochner integral. Source: `paper/main.tex:948–955`. -/
theorem meanFlux_const_mul {d : ℕ} {K : ℝ} (P : Measure (Coefficient d K))
    (e : Vec d) (G : Coefficient d K → Vec d → Vec d) (c : ℝ) :
    firstOrderMeanFlux P (c • e) (fun A x => c • G A x) = c • firstOrderMeanFlux P e G := by
  ext j
  simp only [firstOrderMeanFlux, ← smul_add, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul,
    integral_const_mul]


/-- The joint smooth-test estimate extends to slopes in the closed unit
ball by applying the printed estimate to one half of the same corrector.
The constant is still chosen before the law, slope, scale and test.
Source: `paper/main.tex:948–955`; AKM (4.126), p. 173. -/
theorem correctorWeakH2_test_moments_unit (hAKM : CorrectorWeakH2)
    (K s m : ℝ) (hK : 1 < K) (hs : 0 < s) (hs2 : s < 2) (hm : 0 < m) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : Measure (Coefficient 2 K), IsAdmissibleLaw P →
      ∀ e : Vec 2, euclideanNorm e ≤ 1 →
        ∀ (φ : Coefficient 2 K → Vec 2 → ℝ) (G : Coefficient 2 K → Vec 2 → Vec 2),
          IsFirstOrderCorrector P e φ G →
          ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
            ∀ ψ : Vec 2 → ℝ, IsSpatialTest (originBall 2 1) ψ →
              h2TestNorm (originBall 2 1) ψ ≤ 1 → ∀ j : Fin 2,
                eLpNorm (fun A => ⨍ x in originBall 2 1, G A (ε⁻¹ • x) j * ψ x)
                    (ENNReal.ofReal m) P +
                  eLpNorm (fun A => ⨍ x in originBall 2 1,
                    (((A (ε⁻¹ • x)).mulVec (e + G A (ε⁻¹ • x)) - firstOrderMeanFlux P e G) j) * ψ x)
                    (ENNReal.ofReal m) P ≤ ENNReal.ofReal (C * ε) := by
  obtain ⟨C, hC, htest⟩ := correctorWeakH2_test_moments hAKM K s m hK hs hs2 hm
  refine ⟨2 * C, mul_pos two_pos hC, ?_⟩
  intro P hP e he φ G hc ε hε hεhalf ψ hψ hnorm j
  have hehalf : euclideanNorm ((1 / 2 : ℝ) • e) < 1 := by
    rw [euclideanNorm_smul _ (by norm_num)]
    linarith
  have ht := htest P hP ((1 / 2 : ℝ) • e) hehalf
    (fun A x => (1 / 2 : ℝ) * φ A x) (fun A x => (1 / 2 : ℝ) • G A x)
    (isFirstOrderCorrector_const_mul hc (by norm_num)) ε hε hεhalf ψ hψ hnorm j
  let f : Coefficient 2 K → ℝ := fun A =>
    ⨍ x in originBall 2 1, G A (ε⁻¹ • x) j * ψ x
  let q : Coefficient 2 K → ℝ := fun A => ⨍ x in originBall 2 1,
    (((A (ε⁻¹ • x)).mulVec (e + G A (ε⁻¹ • x)) - firstOrderMeanFlux P e G) j) * ψ x
  have hflux (A : Coefficient 2 K) (x : Vec 2) :
      ((A (ε⁻¹ • x)).mulVec ((1 / 2 : ℝ) • e + (1 / 2 : ℝ) • G A (ε⁻¹ • x)) -
        firstOrderMeanFlux P ((1 / 2 : ℝ) • e) (fun B z => (1 / 2 : ℝ) • G B z)) j * ψ x =
      (1 / 2 : ℝ) *
        ((((A (ε⁻¹ • x)).mulVec (e + G A (ε⁻¹ • x)) - firstOrderMeanFlux P e G) j) * ψ x) := by
    rw [meanFlux_const_mul, ← smul_add, Matrix.mulVec_smul, ← smul_sub]
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  simp only [hflux, Pi.smul_apply, smul_eq_mul, mul_assoc, average, integral_const_mul] at ht
  have ht' : eLpNorm ((1 / 2 : ℝ) • f) (ENNReal.ofReal m) P +
      eLpNorm ((1 / 2 : ℝ) • q) (ENNReal.ofReal m) P ≤ ENNReal.ofReal (C * ε) := ht
  have hf : f = (2 : ℝ) • ((1 / 2 : ℝ) • f) := by ext A; simp
  have hq : q = (2 : ℝ) • ((1 / 2 : ℝ) • q) := by ext A; simp
  change eLpNorm f _ P + eLpNorm q _ P ≤ _
  calc
    _ = (2 : ℝ≥0∞) * (eLpNorm ((1 / 2 : ℝ) • f) (ENNReal.ofReal m) P +
        eLpNorm ((1 / 2 : ℝ) • q) (ENNReal.ofReal m) P) := by
      conv_lhs => rw [hf, hq]; simp only [eLpNorm_const_smul]
      norm_num [eLpNorm_const_smul, mul_add, enorm_eq_nnnorm]
    _ ≤ 2 * ENNReal.ofReal (C * ε) := mul_le_mul_right ht' 2
    _ = ENNReal.ofReal ((2 * C) * ε) := by
      rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      ring

end EinsteinRelation.Correctors
