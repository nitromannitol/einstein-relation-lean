import EinsteinRelation.Correctors.SpatialWeakProduct
import EinsteinRelation.Correctors.SpatialWeakCongruence
import EinsteinRelation.Correctors.WeakEquationAveraging

/-! # Averaging spatially weighted weak equations

Source: `paper/main.tex:926–938`. The smooth weight depends on both the
center and the spatial argument. Differentiation of the averaged field
produces the averaged derivative and the term involving the derivative of
the weight. This proves the product and Fubini steps for the fields `H_R`
and `K_R`, without requiring pointwise derivatives of conditional versions.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- A weak gradient commutes with center averaging after including the
derivative of the center weight. Source: `paper/main.tex:931–938`. -/
theorem hasWeakGradient_weighted_integral {Y : Type*} [MeasurableSpace Y]
    {d : ℕ} (μ : Measure Y) [SFinite μ] {U : Set (Vec d)} (hU : IsOpen U)
    (w u : Y → Vec d → ℝ) (G : Y → Vec d → Vec d)
    (hw : ∀ y, ContDiff ℝ (⊤ : ℕ∞) (w y))
    (hu : Integrable (fun z : Y × Vec d => w z.1 z.2 * u z.1 z.2)
      (μ.prod (volume.restrict U)))
    (hG : ∀ j, Integrable (fun z : Y × Vec d => w z.1 z.2 * G z.1 z.2 j)
      (μ.prod (volume.restrict U)))
    (hDw : ∀ j, Integrable (fun z : Y × Vec d =>
      u z.1 z.2 * coordinateDerivative j (w z.1) z.2) (μ.prod (volume.restrict U)))
    (hweak : ∀ᵐ y ∂μ, HasWeakGradient U (u y) (G y)) :
    HasWeakGradient U (fun x => ∫ y, w y x * u y x ∂μ)
      (fun x j => (∫ y, w y x * G y x j ∂μ) +
        ∫ y, u y x * coordinateDerivative j (w y) x ∂μ) := by
  have hweighted := hasWeakGradient_integral μ U
    (fun y x => w y x * u y x)
    (fun y x j => w y x * G y x j + u y x * coordinateDerivative j (w y) x)
    hu (fun j => (hG j).add (hDw j))
    (hweak.mono fun y hy => hasWeakGradient_mul_smooth hU hy (hw y))
  apply hasWeakGradient_congr_ae hU hweighted Filter.EventuallyEq.rfl
  have hsections : ∀ᵐ x ∂volume.restrict U, ∀ j : Fin d,
      Integrable (fun y => w y x * G y x j) μ ∧
        Integrable (fun y => u y x * coordinateDerivative j (w y) x) μ :=
    ae_all_iff.mpr fun j => (hG j).prod_left_ae.and (hDw j).prod_left_ae
  filter_upwards [hsections] with x hx
  funext j
  exact integral_add (hx j).1 (hx j).2

/-- The divergence of a weighted average includes the contraction with
the spatial derivative of the weight. Source: `paper/main.tex:931–938`. -/
theorem hasWeakDivergence_weighted_integral {Y : Type*} [MeasurableSpace Y]
    {d : ℕ} (μ : Measure Y) [SFinite μ] {U : Set (Vec d)} (hU : IsOpen U)
    (w : Y → Vec d → ℝ) (F : Y → Vec d → Vec d) (h : Y → Vec d → ℝ)
    (hw : ∀ y, ContDiff ℝ (⊤ : ℕ∞) (w y))
    (hF : ∀ j, Integrable (fun z : Y × Vec d => w z.1 z.2 * F z.1 z.2 j)
      (μ.prod (volume.restrict U)))
    (hh : Integrable (fun z : Y × Vec d => w z.1 z.2 * h z.1 z.2)
      (μ.prod (volume.restrict U)))
    (hDw : Integrable (fun z : Y × Vec d => dot (F z.1 z.2) (gradient (w z.1) z.2))
      (μ.prod (volume.restrict U)))
    (hweak : ∀ᵐ y ∂μ, HasWeakDivergence U (F y) (h y)) :
    HasWeakDivergence U (fun x j => ∫ y, w y x * F y x j ∂μ)
      (fun x => (∫ y, w y x * h y x ∂μ) +
        ∫ y, dot (F y x) (gradient (w y) x) ∂μ) := by
  have hweighted := hasWeakDivergence_integral μ U
    (fun y x j => w y x * F y x j)
    (fun y x => w y x * h y x + dot (F y x) (gradient (w y) x))
    hF (hh.add hDw)
    (hweak.mono fun y hy => hasWeakDivergence_mul_smooth hU hy (hw y))
  apply hasWeakDivergence_congr_ae hU hweighted Filter.EventuallyEq.rfl
  filter_upwards [hh.prod_left_ae, hDw.prod_left_ae] with x hx hx'
  exact integral_add hx hx'

/-- Row divergence gives the matrix contraction defining `K_R`.
Source: `paper/main.tex:931–938`. -/
theorem hasWeakRowDivergence_weighted_integral {Y : Type*} [MeasurableSpace Y]
    {d : ℕ} (μ : Measure Y) [SFinite μ] {U : Set (Vec d)} (hU : IsOpen U)
    (w : Y → Vec d → ℝ) (S : Y → Vec d → Mat d) (g : Y → Vec d → Vec d)
    (hw : ∀ y, ContDiff ℝ (⊤ : ℕ∞) (w y))
    (hS : ∀ j k, Integrable (fun z : Y × Vec d => w z.1 z.2 * S z.1 z.2 j k)
      (μ.prod (volume.restrict U)))
    (hg : ∀ j, Integrable (fun z : Y × Vec d => w z.1 z.2 * g z.1 z.2 j)
      (μ.prod (volume.restrict U)))
    (hDw : ∀ j, Integrable (fun z : Y × Vec d =>
      ((S z.1 z.2).mulVec (gradient (w z.1) z.2)) j) (μ.prod (volume.restrict U)))
    (hweak : ∀ᵐ y ∂μ, HasWeakRowDivergence U (S y) (g y)) :
    HasWeakRowDivergence U (fun x j k => ∫ y, w y x * S y x j k ∂μ)
      (fun x j => (∫ y, w y x * g y x j ∂μ) +
        ∫ y, ((S y x).mulVec (gradient (w y) x)) j ∂μ) := by
  intro j
  exact hasWeakDivergence_weighted_integral μ hU w (fun y x k => S y x j k)
    (fun y x => g y x j) hw (hS j) (hg j) (hDw j)
    (hweak.mono fun _ hy => hy j)

end EinsteinRelation.Correctors
