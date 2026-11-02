import EinsteinRelation.Calculus.Weak

/-! Source: `paper/main.tex:727-731`. The weak Poisson equation supplies
the divergence-free flux used by the explicit scalar lift. -/
open MeasureTheory
namespace EinsteinRelation.Correctors

private theorem smooth_coordinateDerivative {d : ℕ} {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative i ψ) := by
  exact ((contDiff_infty_iff_fderiv.mp hψ).2).clm_apply contDiff_const

private theorem compact_coordinateDerivative {d : ℕ} {ψ : Vec d → ℝ}
    (hψ : HasCompactSupport ψ) (i : Fin d) :
    HasCompactSupport (coordinateDerivative i ψ) := by
  exact hψ.fderiv_apply ℝ (unitVector i)

/-- Integration by parts turns the scalar Poisson equation into the weak
zero-divergence equation for the actual flux `g - F`. -/
theorem hasWeakDivergence_gradient_sub_of_poisson {d : ℕ}
    {u : Vec d → ℝ} {g F : Vec d → Vec d}
    (hw : HasWeakGradient Set.univ u g)
    (hF : ∀ i, LocallyIntegrable (fun x => F x i) volume)
    (hP : ∀ ψ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      (∫ x, u x * (-(∑ i : Fin d,
        coordinateDerivative i (coordinateDerivative i ψ) x))) =
        ∫ x, dot (F x) (gradient ψ x)) :
    HasWeakDivergence Set.univ (fun x => g x - F x) 0 := by
  refine ⟨?_, locallyIntegrableOn_zero, ?_⟩
  · intro i
    exact (hw i).2.1.sub (locallyIntegrableOn_univ.mpr (hF i))
  intro ψ hψ
  have hD (i : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative i ψ) :=
    smooth_coordinateDerivative hψ.1 i
  have hDc (i : Fin d) : HasCompactSupport (coordinateDerivative i ψ) :=
    compact_coordinateDerivative hψ.2.1 i
  have hgint (i : Fin d) : Integrable
      (fun x => g x i * coordinateDerivative i ψ x) volume := by
    simpa only [smul_eq_mul] using (locallyIntegrableOn_univ.mp (hw i).2.1).integrable_smul_right_of_hasCompactSupport (hD i).continuous (hDc i)
  have hFint (i : Fin d) : Integrable
      (fun x => F x i * coordinateDerivative i ψ x) volume := by
    simpa only [smul_eq_mul] using (hF i).integrable_smul_right_of_hasCompactSupport (hD i).continuous (hDc i)
  have huint (i : Fin d) : Integrable
      (fun x => u x * coordinateDerivative i (coordinateDerivative i ψ) x) volume := by
    simpa only [smul_eq_mul] using (locallyIntegrableOn_univ.mp (hw i).1).integrable_smul_right_of_hasCompactSupport
        (smooth_coordinateDerivative (hD i) i).continuous
        (compact_coordinateDerivative (hDc i) i)
  have hweak (i : Fin d) :
      (∫ x, u x * coordinateDerivative i (coordinateDerivative i ψ) x) =
        -(∫ x, g x i * coordinateDerivative i ψ x) := by
    simpa only [setIntegral_univ] using
      (hw i).2.2 (coordinateDerivative i ψ) ⟨hD i, hDc i, Set.subset_univ _⟩
  have hparts : (∫ x, u x * (-(∑ i : Fin d,
      coordinateDerivative i (coordinateDerivative i ψ) x))) =
        ∫ x, dot (g x) (gradient ψ x) := by
    simp_rw [mul_neg, Finset.mul_sum]
    rw [integral_neg, integral_finsetSum _ (fun i _ => huint i)]
    simp_rw [hweak, Finset.sum_neg_distrib, neg_neg]
    symm
    exact integral_finsetSum _ (fun i _ => hgint i)
  have heq : (∫ x, dot (g x) (gradient ψ x)) =
      ∫ x, dot (F x) (gradient ψ x) := hparts.symm.trans (hP ψ hψ.1 hψ.2.1)
  have hgi : Integrable (fun x => dot (g x) (gradient ψ x)) volume :=
    integrable_finsetSum _ (fun i _ => hgint i)
  have hFi : Integrable (fun x => dot (F x) (gradient ψ x)) volume :=
    integrable_finsetSum _ (fun i _ => hFint i)
  simp only [setIntegral_univ, Pi.zero_apply, zero_mul, integral_zero, neg_zero]
  have hid (x : Vec d) : dot (g x - F x) (gradient ψ x) =
      dot (g x) (gradient ψ x) - dot (F x) (gradient ψ x) := by
    simp only [dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  simp_rw [hid]
  rw [integral_sub hgi hFi, heq, sub_self]

end EinsteinRelation.Correctors
