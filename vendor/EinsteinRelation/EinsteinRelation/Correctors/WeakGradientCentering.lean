import EinsteinRelation.Calculus.Weak
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
open MeasureTheory
namespace EinsteinRelation.Correctors

private theorem integral_coordinateDerivative_zero_center {d : ℕ} {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) (i : Fin d) :
    (∫ x, coordinateDerivative i φ x) = 0 := by
  have hφ_cont : Continuous φ := hφ.continuous
  have hφ_diff : Differentiable ℝ φ :=
    hφ.differentiable (by simp)
  have hd : Continuous (coordinateDerivative i φ) := by
    exact (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdc : HasCompactSupport (coordinateDerivative i φ) :=
    hφc.fderiv_apply ℝ (unitVector i)
  have hdint : Integrable (fun x => coordinateDerivative i φ x) volume :=
    hd.integrable_of_hasCompactSupport hdc
  have hsecond : Integrable (fun x => (fun _ : Vec d => (1 : ℝ)) x * coordinateDerivative i φ x)
      volume := by
    simpa using hdint
  have hproduct : Integrable (fun x => (fun _ : Vec d => (1 : ℝ)) x * φ x) volume := by
    simpa using hφ_cont.integrable_of_hasCompactSupport hφc
  have hfirst : Integrable
      (fun x => coordinateDerivative i (fun _ : Vec d => (1 : ℝ)) x * φ x) volume := by
    simp [coordinateDerivative]
  have hparts := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    hfirst hsecond hproduct (fun x _ => differentiableAt_const (1 : ℝ)) (fun x _ => hφ_diff x)
  simpa [coordinateDerivative] using hparts

private theorem coordinateDerivative_eq_zero_outside_center {d : ℕ} {U : Set (Vec d)}
    {φ : Vec d → ℝ} (hφ : IsSpatialTest U φ) (i : Fin d) (x : Vec d) (hx : x ∉ U) :
    coordinateDerivative i φ x = 0 := by
  have hnot : x ∉ tsupport φ := fun h => hx (hφ.2.2 h)
  rw [coordinateDerivative, fderiv_of_notMem_tsupport ℝ hnot, ContinuousLinearMap.zero_apply]

/-- Centering a scalar orbit preserves its weak gradient; source `paper/main.tex:693-698,727-729`. -/
theorem hasWeakGradient_sub_const {d : ℕ} (U : Set (Vec d))
    {u : Vec d → ℝ} {g : Vec d → Vec d} (h : HasWeakGradient U u g) (c : ℝ) :
    HasWeakGradient U (fun x => u x - c) g := by
  unfold HasWeakGradient at h ⊢
  intro i
  refine ⟨(h i).1.sub ((locallyIntegrable_const c).locallyIntegrableOn U), (h i).2.1, ?_⟩
  intro φ hφ
  have hd : Continuous (coordinateDerivative i φ) := by
    exact (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdc : HasCompactSupport (coordinateDerivative i φ) :=
    hφ.2.1.fderiv_apply ℝ (unitVector i)
  obtain ⟨B, hB⟩ := hdc.exists_bound_of_continuous hd
  have hKc : IsCompact (tsupport φ) := hφ.2.1.isCompact
  have hu : Integrable u (volume.restrict (tsupport φ)) :=
    (h i).1.integrableOn_compact_subset hφ.2.2 hKc
  have hKint : IntegrableOn (fun x => u x * coordinateDerivative i φ x) (tsupport φ) :=
    hu.mul_bdd hd.aestronglyMeasurable (ae_of_all _ hB)
  -- The integrand vanishes off `tsupport φ`, so it is globally integrable.
  have hglob : Integrable (fun x => u x * coordinateDerivative i φ x) volume := by
    have hind := hKint.integrable_indicator (isClosed_tsupport φ).measurableSet
    refine hind.congr (ae_of_all _ fun x => ?_)
    by_cases hx : x ∈ tsupport φ
    · simp only [Set.indicator_of_mem hx]
    · simp only [Set.indicator_of_notMem hx, coordinateDerivative,
        fderiv_of_notMem_tsupport ℝ hx, ContinuousLinearMap.zero_apply, mul_zero]
  have hint : Integrable (fun x => u x * coordinateDerivative i φ x) (volume.restrict U) :=
    hglob.restrict
  have hdi : Integrable (coordinateDerivative i φ) (volume.restrict U) :=
    (hd.integrable_of_hasCompactSupport hdc).restrict
  have hzero : (∫ x in U, coordinateDerivative i φ x) = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (coordinateDerivative_eq_zero_outside_center hφ i)]
    exact integral_coordinateDerivative_zero_center hφ.1 hφ.2.1 i
  simp_rw [sub_mul]
  rw [integral_sub hint (hdi.const_mul c), integral_const_mul, hzero, mul_zero, sub_zero]
  exact (h i).2.2 φ hφ

end EinsteinRelation.Correctors
