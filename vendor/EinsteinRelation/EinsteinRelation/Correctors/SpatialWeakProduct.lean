import EinsteinRelation.Calculus.Weak
import EinsteinRelation.Calculus.HorizontalIntegration

/-! # Product rules for spatial weak equations

Source: `paper/main.tex:916–928`. Multiplying a weak gradient or row
divergence by a smooth spatial weight produces the terms called `H_R`
and `K_R` in the center average. All equations below use actual compactly
supported tests and retain local integrability of every field.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- Local integrability suffices for the pairing with a smooth test
supported inside the domain. Source: `paper/main.tex:916–928`. -/
theorem integrableOn_mul_spatialTest {d : ℕ} {U : Set (Vec d)}
    {f ψ : Vec d → ℝ} (hf : LocallyIntegrableOn f U volume)
    (hψ : IsSpatialTest U ψ) : IntegrableOn (fun x => f x * ψ x) U volume := by
  have hfK := hf.integrableOn_compact_subset hψ.2.2 hψ.2.1
  have hint := hfK.mul_continuousOn hψ.1.continuous.continuousOn hψ.2.1
  have hs : Function.support (fun x => f x * ψ x) ⊆ tsupport ψ := by
    intro x hx
    apply subset_tsupport ψ
    exact (mul_ne_zero_iff.mp hx).2
  exact ((integrableOn_iff_integrable_of_support_subset hs).mp hint).integrableOn

private theorem spatialTest_mul_smooth {d : ℕ} {U : Set (Vec d)}
    {φ ψ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hψ : IsSpatialTest U ψ) : IsSpatialTest U (fun x => φ x * ψ x) := by
  refine ⟨hφ.mul hψ.1, hψ.2.1.mul_left, ?_⟩
  exact (tsupport_mul_subset_right (f := φ) (g := ψ)).trans hψ.2.2

private theorem spatialTest_coordinateDerivative {d : ℕ} {U : Set (Vec d)}
    {ψ : Vec d → ℝ} (hψ : IsSpatialTest U ψ) (j : Fin d) :
    IsSpatialTest U (coordinateDerivative j ψ) := by
  refine ⟨?_, hψ.2.1.fderiv_apply ℝ (unitVector j), ?_⟩
  · exact (contDiff_infty_iff_fderiv.mp hψ.1).2.clm_apply contDiff_const
  · apply Set.Subset.trans ?_ hψ.2.2
    apply closure_minimal ?_ isClosed_closure
    intro x hx
    by_contra hxs
    have hz := fderiv_of_notMem_tsupport (𝕜 := ℝ) hxs
    exact hx (by simp only [coordinateDerivative, hz, ContinuousLinearMap.zero_apply])

/-- The spatial weak product rule, including the derivative of the weight.
Source: `paper/main.tex:921–928`. -/
theorem hasWeakPartialDerivative_mul_smooth {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) (j : Fin d) {f g φ : Vec d → ℝ}
    (hfg : HasWeakPartialDerivative U j f g)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    HasWeakPartialDerivative U j (fun x => φ x * f x)
      (fun x => φ x * g x + f x * coordinateDerivative j φ x) := by
  have hdφ : Continuous (coordinateDerivative j φ) :=
    ((contDiff_infty_iff_fderiv.mp hφ).2.clm_apply contDiff_const).continuous
  have hφf := hfg.1.continuousOn_mul hφ.continuous.continuousOn hU.isLocallyClosed
  have hφg := hfg.2.1.continuousOn_mul hφ.continuous.continuousOn hU.isLocallyClosed
  have hfdφ := hfg.1.mul_continuousOn hdφ.continuousOn hU.isLocallyClosed
  refine ⟨hφf, hφg.add hfdφ, ?_⟩
  intro ψ hψ
  have ha := integrableOn_mul_spatialTest hφf (spatialTest_coordinateDerivative hψ j)
  have hb := integrableOn_mul_spatialTest hfdφ hψ
  have hc := integrableOn_mul_spatialTest hφg hψ
  have heq := hfg.2.2 _ (spatialTest_mul_smooth hφ hψ)
  have hsplit :
      (∫ x in U, φ x * f x * coordinateDerivative j ψ x) +
        (∫ x in U, f x * coordinateDerivative j φ x * ψ x) =
        -(∫ x in U, φ x * g x * ψ x) := by
    rw [← integral_add ha hb]
    calc
      _ = ∫ x in U, f x * coordinateDerivative j (fun y => φ y * ψ y) x := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          dsimp only
          rw [coordinateDerivative_mul j φ ψ x
            (hφ.differentiable (by simp) x)
            (hψ.1.differentiable (by simp) x)]
          ring
      _ = -(∫ x in U, g x * (φ x * ψ x)) := heq
      _ = _ := by congr 1; apply integral_congr_ae; exact Filter.Eventually.of_forall fun x => by ring
  have hrhs : (∫ x in U, (φ x * g x + f x * coordinateDerivative j φ x) * ψ x) =
      (∫ x in U, φ x * g x * ψ x) +
        (∫ x in U, f x * coordinateDerivative j φ x * ψ x) := by
    simp_rw [add_mul]
    exact integral_add hc hb
  rw [hrhs]
  linarith only [hsplit]

/-- Vector form of the weak product rule. This is the gradient identity
that yields `H_R` after averaging centers. Source: `paper/main.tex:921–928`. -/
theorem hasWeakGradient_mul_smooth {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) {f φ : Vec d → ℝ} {G : Vec d → Vec d}
    (hG : HasWeakGradient U f G) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    HasWeakGradient U (fun x => φ x * f x)
      (fun x j => φ x * G x j + f x * coordinateDerivative j φ x) := by
  intro j
  exact hasWeakPartialDerivative_mul_smooth hU j (hG j) hφ

/-- The weak divergence product rule. In particular, the error is the
contraction of the original vector field with the gradient of the weight.
Source: `paper/main.tex:921–928`. -/
theorem hasWeakDivergence_mul_smooth {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) {F : Vec d → Vec d} {h φ : Vec d → ℝ}
    (hF : HasWeakDivergence U F h) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    HasWeakDivergence U (fun x j => φ x * F x j)
      (fun x => φ x * h x + dot (F x) (gradient φ x)) := by
  have hφF (j : Fin d) := (hF.1 j).continuousOn_mul
    hφ.continuous.continuousOn hU.isLocallyClosed
  have hdφ (j : Fin d) : Continuous (coordinateDerivative j φ) :=
    ((contDiff_infty_iff_fderiv.mp hφ).2.clm_apply contDiff_const).continuous
  have hFdφ (j : Fin d) := (hF.1 j).mul_continuousOn
    (hdφ j).continuousOn hU.isLocallyClosed
  have hdot : LocallyIntegrableOn (fun x => dot (F x) (gradient φ x)) U volume := by
    rw [locallyIntegrableOn_iff hU.isLocallyClosed]
    intro K hKU hK
    exact integrable_finsetSum Finset.univ fun j _ =>
      (hFdφ j).integrableOn_compact_subset hKU hK
  have hφh := hF.2.1.continuousOn_mul hφ.continuous.continuousOn hU.isLocallyClosed
  refine ⟨hφF, hφh.add hdot, ?_⟩
  intro ψ hψ
  have ha : IntegrableOn (fun x => dot (fun j => φ x * F x j) (gradient ψ x)) U volume :=
    integrable_finsetSum Finset.univ fun j _ =>
      integrableOn_mul_spatialTest (hφF j) (spatialTest_coordinateDerivative hψ j)
  have hb := integrableOn_mul_spatialTest hdot hψ
  have hc := integrableOn_mul_spatialTest hφh hψ
  have hprod (x : Vec d) : dot (F x) (gradient (fun y => φ y * ψ y) x) =
      dot (fun j => φ x * F x j) (gradient ψ x) + dot (F x) (gradient φ x) * ψ x := by
    calc
      _ = ∑ j : Fin d, (φ x * F x j * coordinateDerivative j ψ x +
          F x j * coordinateDerivative j φ x * ψ x) := by
        apply Finset.sum_congr rfl
        intro j _
        change F x j * coordinateDerivative j (fun y => φ y * ψ y) x = _
        rw [coordinateDerivative_mul j φ ψ x
          (hφ.differentiable (by simp) x)
          (hψ.1.differentiable (by simp) x)]
        ring
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_mul]; rfl
  have hsplit :
      (∫ x in U, dot (fun j => φ x * F x j) (gradient ψ x)) +
        (∫ x in U, dot (F x) (gradient φ x) * ψ x) =
        -(∫ x in U, φ x * h x * ψ x) := by
    rw [← integral_add ha hb]
    calc
      _ = ∫ x in U, dot (F x) (gradient (fun y => φ y * ψ y) x) :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => (hprod x).symm)
      _ = -(∫ x in U, h x * (φ x * ψ x)) :=
        hF.2.2 _ (spatialTest_mul_smooth hφ hψ)
      _ = _ := by congr 1; apply integral_congr_ae; exact Filter.Eventually.of_forall fun x => by ring
  have hrhs : (∫ x in U, (φ x * h x + dot (F x) (gradient φ x)) * ψ x) =
      (∫ x in U, φ x * h x * ψ x) +
        (∫ x in U, dot (F x) (gradient φ x) * ψ x) := by
    simp_rw [add_mul]
    exact integral_add hc hb
  rw [hrhs]
  linarith only [hsplit]

/-- Applying the product rule row by row gives exactly the contraction
`S ∇φ` used for `K_R`, with the manuscript's row-divergence convention.
Source: `paper/main.tex:921–928`. -/
theorem hasWeakRowDivergence_mul_smooth {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) {S : Vec d → Mat d} {g : Vec d → Vec d} {φ : Vec d → ℝ}
    (hS : HasWeakRowDivergence U S g) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    HasWeakRowDivergence U (fun x j k => φ x * S x j k)
      (fun x j => φ x * g x j + ((S x).mulVec (gradient φ x)) j) := by
  intro j
  exact hasWeakDivergence_mul_smooth hU (hS j) hφ

end EinsteinRelation.Correctors
