import EinsteinRelation.Correctors.PoissonLiftLocalIntegrability
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! Source: `paper/main.tex:735-739`. The vertical component of the
lifted flux has zero weak divergence, by one-dimensional integration
by parts and Fubini for the actual coordinate Lebesgue measure. -/
open MeasureTheory
namespace EinsteinRelation.Correctors

private theorem integral_height_coordinateDerivative_zero {d : ℕ}
    {ψ : Vec (d + 1) → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (y : Vec d) :
    (∫ t : ℝ, coordinateDerivative 0 ψ (Fin.cons t y)) = 0 := by
  let f : ℝ → ℝ := fun t => ψ (Fin.cons t y)
  have hcons (t : ℝ) :
      HasDerivAt (fun s : ℝ => Fin.cons s y) (unitVector 0) t := by
    apply hasDerivAt_pi.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [unitVector] using hasDerivAt_id t
    · simpa [unitVector] using hasDerivAt_const t (y j)
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := by
    apply hψ.comp
    apply contDiff_pi.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using (contDiff_id : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => t))
    · simpa using (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ => y j))
  have hfc : HasCompactSupport f := by
    apply HasCompactSupport.intro (hψc.image (continuous_apply 0))
    intro t ht
    by_contra hn
    apply ht
    exact ⟨Fin.cons t y, subset_tsupport _ hn, rfl⟩
  have hderiv (t : ℝ) : HasDerivAt f (coordinateDerivative 0 ψ (Fin.cons t y)) t :=
    (hψ.differentiable (by simp) (Fin.cons t y)).hasFDerivAt.comp_hasDerivAt t (hcons t)
  obtain ⟨K, hK⟩ := hf.lipschitzWith_of_hasCompactSupport hfc (by simp) (𝕂 := ℝ)
  have h := (LipschitzWith.const (α := ℝ) (1 : ℝ)).integral_lineDeriv_mul_eq
    (μ := volume) hK hfc (1 : ℝ)
  have hline (t : ℝ) : lineDeriv ℝ f t (-1) =
      -coordinateDerivative 0 ψ (Fin.cons t y) := by
    rw [(hderiv t).differentiableAt.lineDeriv_eq_fderiv, (hderiv t).hasFDerivAt.fderiv]
    simp
  have hconst (t : ℝ) : lineDeriv ℝ (fun _ : ℝ => (1 : ℝ)) t 1 = 0 := by
    simp [lineDeriv]
  simp only [hconst, zero_mul, integral_zero, hline, mul_one, integral_neg] at h
  exact neg_eq_zero.mp h.symm

/-- A height-independent vertical flux pairs to zero against every
smooth compact test. Local integrability justifies the Fubini step. -/
theorem integral_height_derivative_poissonLift_zero {d : ℕ}
    (B : Vec d → ℝ) (hB : LocallyIntegrable B volume)
    (ψ : Vec (d + 1) → ℝ) (hψ : IsSpatialTest Set.univ ψ) :
    (∫ x : Vec (d + 1), B (poissonLiftBase x) * coordinateDerivative 0 ψ x ∂volume) = 0 := by
  have hD : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative 0 ψ) :=
    ((contDiff_infty_iff_fderiv.mp hψ.1).2).clm_apply contDiff_const
  have hDc : HasCompactSupport (coordinateDerivative 0 ψ) :=
    hψ.2.1.fderiv_apply ℝ (unitVector 0)
  have hi : Integrable (fun x : Vec (d + 1) =>
      B (poissonLiftBase x) * coordinateDerivative 0 ψ x) volume := by
    simpa only [smul_eq_mul] using
      (locallyIntegrable_poissonLiftBase B hB).integrable_smul_right_of_hasCompactSupport
        hD.continuous hDc
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0
  have he := volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0
  have heinv (p : ℝ × Vec d) : e.symm p = Fin.cons p.1 p.2 := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;>
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  have he' := MeasurePreserving.symm e he
  have hp : Integrable (fun p : ℝ × Vec d =>
      B p.2 * coordinateDerivative 0 ψ (Fin.cons p.1 p.2)) volume := by
    simpa [Function.comp_def, heinv, poissonLiftBase] using he'.integrable_comp_of_integrable hi
  have hchange : (∫ x : Vec (d + 1), B (poissonLiftBase x) * coordinateDerivative 0 ψ x) =
      ∫ p : ℝ × Vec d, B p.2 * coordinateDerivative 0 ψ (Fin.cons p.1 p.2) := by
    simpa [heinv, poissonLiftBase] using
      (he'.integral_comp' (fun x => B (poissonLiftBase x) * coordinateDerivative 0 ψ x)).symm
  rw [hchange, Measure.volume_eq_prod ℝ (Vec d)]
  rw [integral_prod_symm _ (by simpa only [Measure.volume_eq_prod] using hp)]
  simp_rw [integral_const_mul, integral_height_coordinateDerivative_zero hψ.1 hψ.2.1,
    mul_zero, integral_zero]

end EinsteinRelation.Correctors
