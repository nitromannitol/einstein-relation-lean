import EinsteinRelation.Correctors.PoissonLiftHeightDerivative
import EinsteinRelation.Correctors.PoissonLiftHorizontalDerivative
import EinsteinRelation.Calculus.ClassicalSpatialDerivative

/-! Source: `paper/main.tex:735-739`. Distributional differentiation of
the literal higher dimensional potential used for flux regularity. -/
open MeasureTheory
namespace EinsteinRelation.Correctors

private theorem locallyIntegrable_of_weakGradient {d : ℕ}
    {u : Vec d → ℝ} {g : Vec d → Vec d} (hw : HasWeakGradient Set.univ u g) :
    LocallyIntegrable u volume := by
  by_cases hd : 0 < d
  · exact locallyIntegrableOn_univ.mp (hw ⟨0, hd⟩).1
  · have hd0 : d = 0 := by omega
    subst d
    have heq : u = fun _ => u 0 := by
      funext x
      exact congrArg u (Subsingleton.elim x 0)
    rw [heq]
    exact continuous_const.locallyIntegrable

/-- A base potential has its given horizontal gradient and zero height
derivative on the actual product Lebesgue space. -/
theorem hasWeakGradient_poissonLiftBase {d : ℕ} (u : Vec d → ℝ)
    (g : Vec d → Vec d) (hw : HasWeakGradient Set.univ u g) :
    HasWeakGradient Set.univ (fun x => u (poissonLiftBase x))
      (poissonLiftGradient g 0) := by
  have hlu := locallyIntegrable_of_weakGradient hw
  have hlup := locallyIntegrableOn_univ.mpr (locallyIntegrable_poissonLiftBase u hlu)
  intro j
  refine Fin.cases ?_ (fun k => ?_) j
  · refine ⟨hlup, ?_, ?_⟩
    · simpa only [poissonLiftGradient, Fin.cons_zero] using
        (continuous_const.locallyIntegrable.locallyIntegrableOn Set.univ :
          LocallyIntegrableOn (fun _ : Vec (d + 1) => (0 : ℝ)) Set.univ volume)
    · intro ψ hψ
      simpa only [setIntegral_univ, poissonLiftGradient, Fin.cons_zero, zero_mul,
        integral_zero, neg_zero] using integral_height_derivative_poissonLift_zero u hlu ψ hψ
  · have hlg := locallyIntegrableOn_univ.mp (hw k).2.1
    refine ⟨hlup, ?_, ?_⟩
    · simpa only [poissonLiftGradient, Fin.cons_succ] using
        locallyIntegrableOn_univ.mpr (locallyIntegrable_poissonLiftBase (fun x => g x k) hlg)
    · intro ψ hψ
      have hD : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative k.succ ψ) :=
        ((contDiff_infty_iff_fderiv.mp hψ.1).2).clm_apply contDiff_const
      have hDc : HasCompactSupport (coordinateDerivative k.succ ψ) :=
        hψ.2.1.fderiv_apply ℝ (unitVector k.succ)
      have hinner (t : ℝ) :
          (∫ y : Vec d, u y * coordinateDerivative k.succ ψ (Fin.cons t y)) =
            -(∫ y : Vec d, g y k * ψ (Fin.cons t y)) := by
        have h := (hw k).2.2 _ (isSpatialTest_poissonLiftSlice hψ t)
        simpa only [setIntegral_univ, coordinateDerivative_poissonLiftSlice
          (hψ.1.differentiable (by simp))] using h
      simp only [setIntegral_univ, poissonLiftGradient, Fin.cons_succ]
      rw [integral_poissonLiftBase_mul_test u hlu _ hD.continuous hDc,
        integral_poissonLiftBase_mul_test (fun x => g x k) hlg ψ hψ.1.continuous hψ.2.1]
      simp_rw [hinner, integral_neg]

private theorem weakPartial_add {d : ℕ} {j : Fin d}
    {u v g h : Vec d → ℝ} (hu : HasWeakPartialDerivative Set.univ j u g)
    (hv : HasWeakPartialDerivative Set.univ j v h) :
    HasWeakPartialDerivative Set.univ j (fun x => u x + v x) (fun x => g x + h x) := by
  refine ⟨hu.1.add hv.1, hu.2.1.add hv.2.1, ?_⟩
  intro ψ hψ
  have hD : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative j ψ) :=
    ((contDiff_infty_iff_fderiv.mp hψ.1).2).clm_apply contDiff_const
  have hDc : HasCompactSupport (coordinateDerivative j ψ) :=
    hψ.2.1.fderiv_apply ℝ (unitVector j)
  have hiu := (locallyIntegrableOn_univ.mp hu.1).integrable_smul_right_of_hasCompactSupport
    hD.continuous hDc
  have hiv := (locallyIntegrableOn_univ.mp hv.1).integrable_smul_right_of_hasCompactSupport
    hD.continuous hDc
  have hig := (locallyIntegrableOn_univ.mp hu.2.1).integrable_smul_right_of_hasCompactSupport
    hψ.1.continuous hψ.2.1
  have hih := (locallyIntegrableOn_univ.mp hv.2.1).integrable_smul_right_of_hasCompactSupport
    hψ.1.continuous hψ.2.1
  simp only [smul_eq_mul] at hiu hiv hig hih
  have hwu := hu.2.2 ψ hψ
  have hwv := hv.2.2 ψ hψ
  simp only [setIntegral_univ] at hwu hwv ⊢
  simp_rw [add_mul]
  rw [integral_add hiu hiv, integral_add hig hih, hwu, hwv]
  ring

/-- The explicit potential has exactly the stated weak gradient; no
regular representative or higher dimensional PDE is assumed. -/
theorem hasWeakGradient_poissonLift {d : ℕ} (u : Vec d → ℝ)
    (g : Vec d → Vec d) (hw : HasWeakGradient Set.univ u g) (M : ℝ) :
    HasWeakGradient Set.univ (poissonLiftPotential u M) (poissonLiftGradient g M) := by
  have hb := hasWeakGradient_poissonLiftBase u g hw
  have hc : ContDiff ℝ 1 (fun x : Vec (d + 1) => M * x 0) :=
    contDiff_const.mul (contDiff_apply ℝ ℝ 0)
  have hD (j : Fin (d + 1)) (x : Vec (d + 1)) :
      coordinateDerivative j (fun y : Vec (d + 1) => M * y 0) x =
        (Fin.cons M (fun _ : Fin d => (0 : ℝ)) : Vec (d + 1)) j := by
    have hF : HasFDerivAt (fun y : Vec (d + 1) => M * y 0)
        (M • (ContinuousLinearMap.proj 0 : Vec (d + 1) →L[ℝ] ℝ)) x := by
      simpa only [smul_eq_mul] using
        (ContinuousLinearMap.proj 0 : Vec (d + 1) →L[ℝ] ℝ).hasFDerivAt.const_mul M
    unfold coordinateDerivative
    rw [hF.fderiv]
    refine Fin.cases ?_ (fun k => ?_) j <;> simp [unitVector]
  intro j
  have hh := hasWeakPartialDerivative_of_contDiff j _ hc
  have h := weakPartial_add (hb j) hh
  have heq : (fun x : Vec (d + 1) => poissonLiftGradient g 0 x j +
      coordinateDerivative j (fun y : Vec (d + 1) => M * y 0) x) =
      (fun x => poissonLiftGradient g M x j) := by
    funext x
    rw [hD]
    refine Fin.cases ?_ (fun k => ?_) j <;> simp [poissonLiftGradient]
  rw [heq] at h
  exact h

end EinsteinRelation.Correctors
