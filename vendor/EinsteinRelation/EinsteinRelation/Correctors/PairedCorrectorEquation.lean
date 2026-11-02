import EinsteinRelation.Correctors.PairedParabolicEquation
import EinsteinRelation.Correctors.PlanarFluxCorrector
import EinsteinRelation.Correctors.SpatialWeakCongruence

/-! # Equations for two locally agreeing correctors

Source: `paper/main.tex:850–873`. The corrector and flux-corrector
weak equations are subtracted on the region of coefficient agreement.
The common slope and mean flux cancel; neither their values nor an
isotropy hypothesis enter the resulting homogeneous equations.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- Subtraction of actual weak divergences, with the integrability needed
for subtracting their test integrals. Source: `paper/main.tex:850–873`. -/
theorem hasWeakDivergence_sub {d : ℕ} {U : Set (Vec d)}
    {F₁ F₂ : Vec d → Vec d} {h₁ h₂ : Vec d → ℝ}
    (hF₁ : HasWeakDivergence U F₁ h₁) (hF₂ : HasWeakDivergence U F₂ h₂) :
    HasWeakDivergence U (fun x => F₁ x - F₂ x) (fun x => h₁ x - h₂ x) := by
  refine ⟨fun j => (hF₁.1 j).sub (hF₂.1 j), hF₁.2.1.sub hF₂.2.1, ?_⟩
  intro ψ hψ
  have hgrad (j : Fin d) : IsSpatialTest U (coordinateDerivative j ψ) :=
    isSpatialTest_coordinateDerivative hψ j
  have hint₁ : IntegrableOn (fun x => dot (F₁ x) (gradient ψ x)) U volume :=
    integrable_finset_sum Finset.univ fun j _ =>
      integrableOn_mul_spatialTest (hF₁.1 j) (hgrad j)
  have hint₂ : IntegrableOn (fun x => dot (F₂ x) (gradient ψ x)) U volume :=
    integrable_finset_sum Finset.univ fun j _ =>
      integrableOn_mul_spatialTest (hF₂.1 j) (hgrad j)
  simp only [dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  change (∫ x in U, dot (F₁ x) (gradient ψ x) - dot (F₂ x) (gradient ψ x)) =
    -(∫ x in U, h₁ x * ψ x - h₂ x * ψ x)
  rw [integral_sub hint₁ hint₂, integral_sub
    (integrableOn_mul_spatialTest hF₁.2.1 hψ)
    (integrableOn_mul_spatialTest hF₂.2.1 hψ), hF₁.2.2 ψ hψ, hF₂.2.2 ψ hψ]
  ring

/-- Subtraction preserves the row-divergence convention.
Source: `paper/main.tex:864–873`. -/
theorem hasWeakRowDivergence_sub {d : ℕ} {U : Set (Vec d)}
    {S₁ S₂ : Vec d → Mat d} {g₁ g₂ : Vec d → Vec d}
    (h₁ : HasWeakRowDivergence U S₁ g₁) (h₂ : HasWeakRowDivergence U S₂ g₂) :
    HasWeakRowDivergence U (fun x => S₁ x - S₂ x) (fun x => g₁ x - g₂ x) := by
  intro j
  exact hasWeakDivergence_sub (h₁ j) (h₂ j)

/-- Two correctors with a common slope have a harmonic difference wherever
their coefficients agree. Source: `paper/main.tex:850–858`. -/
theorem paired_corrector_harmonic {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    {a₁ a₂ : Vec d → Mat d} (ha : Set.EqOn a₁ a₂ U) (e : Vec d)
    {φ₁ φ₂ : Vec d → ℝ} {G₁ G₂ : Vec d → Vec d}
    (hgrad₁ : HasWeakGradient U φ₁ G₁) (hgrad₂ : HasWeakGradient U φ₂ G₂)
    (hdiv₁ : HasWeakDivergence U (fun x => (a₁ x).mulVec (e + G₁ x)) (fun _ => 0))
    (hdiv₂ : HasWeakDivergence U (fun x => (a₂ x).mulVec (e + G₂ x)) (fun _ => 0)) :
    HasWeakGradient U (fun x => φ₁ x - φ₂ x) (fun x => G₁ x - G₂ x) ∧
      HasWeakDivergence U (fun x => (a₁ x).mulVec (G₁ x - G₂ x)) (fun _ => 0) := by
  refine ⟨hasWeakGradient_sub hgrad₁ hgrad₂, ?_⟩
  apply hasWeakDivergence_congr_ae hU (hasWeakDivergence_sub hdiv₁ hdiv₂)
  · filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    rw [← ha hx, ← Matrix.mulVec_sub]
    congr 1
    abel
  · exact Filter.Eventually.of_forall fun _ => sub_self _

/-- The common slope and mean flux cancel in the paired skew equation.
Source: `paper/main.tex:864–873`. -/
theorem paired_fluxCorrector_rowDivergence {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    {a₁ a₂ : Vec d → Mat d} (ha : Set.EqOn a₁ a₂ U) (e m : Vec d)
    {G₁ G₂ : Vec d → Vec d} {S₁ S₂ : Vec d → Mat d}
    (h₁ : HasWeakRowDivergence U S₁ (fun x => (a₁ x).mulVec (e + G₁ x) - m))
    (h₂ : HasWeakRowDivergence U S₂ (fun x => (a₂ x).mulVec (e + G₂ x) - m)) :
    HasWeakRowDivergence U (fun x => S₁ x - S₂ x)
      (fun x => (a₁ x).mulVec (G₁ x - G₂ x)) := by
  apply hasWeakRowDivergence_congr_ae hU (hasWeakRowDivergence_sub h₁ h₂)
    Filter.EventuallyEq.rfl
  filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
  rw [← ha hx]
  rw [show (a₁ x).mulVec (e + G₁ x) - m - ((a₁ x).mulVec (e + G₂ x) - m) =
    (a₁ x).mulVec (e + G₁ x) - (a₁ x).mulVec (e + G₂ x) by abel,
    ← Matrix.mulVec_sub]
  congr 1
  abel

/-- In dimension two the independent paired skew entry has gradient
`J a₁ (G₁-G₂)`, with the paper's signs. Source: `paper/main.tex:864–873`. -/
theorem paired_planar_fluxCorrector_gradient {U : Set (Vec 2)} (hU : IsOpen U)
    {a₁ a₂ : Vec 2 → Mat 2} (ha : Set.EqOn a₁ a₂ U) (e m : Vec 2)
    {G₁ G₂ : Vec 2 → Vec 2} {S₁ S₂ : Vec 2 → Mat 2}
    (hS₁ : ∀ x, (S₁ x).transpose = -(S₁ x))
    (hS₂ : ∀ x, (S₂ x).transpose = -(S₂ x))
    (h₁ : HasWeakRowDivergence U S₁ (fun x => (a₁ x).mulVec (e + G₁ x) - m))
    (h₂ : HasWeakRowDivergence U S₂ (fun x => (a₂ x).mulVec (e + G₂ x) - m)) :
    HasWeakGradient U (fun x => S₁ x 0 1 - S₂ x 0 1)
      (fun x => ![-((a₁ x).mulVec (G₁ x - G₂ x)) 1,
        ((a₁ x).mulVec (G₁ x - G₂ x)) 0]) := by
  apply hasWeakGradient_planar_skew_entry (fun x => S₁ x - S₂ x) _
    (fun x => ?_) (paired_fluxCorrector_rowDivergence hU ha e m h₁ h₂)
  rw [Matrix.transpose_sub, hS₁ x, hS₂ x]
  ext j k
  simp only [Matrix.sub_apply, Matrix.neg_apply]
  ring

end EinsteinRelation.Correctors
