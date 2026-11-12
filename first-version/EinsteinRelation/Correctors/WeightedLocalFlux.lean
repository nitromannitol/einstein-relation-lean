import EinsteinRelation.Correctors.WeightedSpatialAveraging

/-! # The flux equation after averaging centers

Source: `paper/main.tex:926–938`. Averaging the conditioned scalar and skew
fields produces a weak gradient and row divergence. The product-rule terms
are exactly `H_R` and `K_R`, and the remaining flux is `a H_R - K_R`.
This deterministic step uses the original weak equations and ordinary
product integrability. It does not assume the averaged flux equation.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- A weight with integral one commutes with an affine coefficient action
that is independent of the center variable. Source: `paper/main.tex:936–938`. -/
theorem integral_weight_mulVec_add {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) {d : ℕ} (w : Y → ℝ) (G : Y → Vec d) (A : Mat d) (e b : Vec d)
    (hw : Integrable w μ) (hG : ∀ k, Integrable (fun y => w y * G y k) μ)
    (hmass : ∫ y, w y ∂μ = 1) (j : Fin d) :
    (∫ y, w y * ((A.mulVec (e + G y) - b) j) ∂μ) =
      (A.mulVec (e + fun k => ∫ y, w y * G y k ∂μ) - b) j := by
  have hsplit (y : Y) : w y * ((A.mulVec (e + G y) - b) j) =
      w y * (A.mulVec e j - b j) + ∑ k : Fin d, A j k * (w y * G y k) := by
    have hsum : w y * A.mulVec (G y) j = ∑ k : Fin d, A j k * (w y * G y k) := by
      change w y * (∑ k : Fin d, A j k * G y k) = _
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp only [Matrix.mulVec_add, Pi.add_apply, Pi.sub_apply, mul_sub, mul_add, hsum]
    ring
  simp_rw [hsplit]
  rw [integral_add (hw.mul_const _) (integrable_finset_sum Finset.univ
    (fun k _ => (hG k).const_mul _)), integral_mul_const, hmass, one_mul,
    integral_finset_sum Finset.univ (fun k _ => (hG k).const_mul _)]
  simp only [integral_const_mul, Matrix.mulVec_add, Pi.add_apply, Pi.sub_apply,
    Matrix.mulVec, dotProduct]
  ring

/-- Center averaging preserves skew symmetry, including at exceptional
spatial points. Source: `paper/main.tex:926–938`. -/
theorem integral_weight_skew {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) {d : ℕ} (w : Y → ℝ) (S : Y → Mat d)
    (hS : ∀ y, (S y).transpose = -(S y)) :
    Matrix.transpose (fun j k => ∫ y, w y * S y j k ∂μ) =
      -(fun j k => ∫ y, w y * S y j k ∂μ) := by
  ext j k
  change (∫ y, w y * S y k j ∂μ) = -(∫ y, w y * S y j k ∂μ)
  have hentry (y : Y) : S y k j = -S y j k := congrFun (congrFun (hS y) j) k
  simp_rw [hentry, mul_neg, integral_neg]

/-- The weighted scalar and skew averages satisfy the local flux equation
with error `a H - K`, where `H` and `K` are the actual weight-derivative
integrals. Source: `paper/main.tex:931–938`. -/
theorem hasWeakGradient_and_flux_weighted_integral {Y : Type*} [MeasurableSpace Y]
    {d : ℕ} (μ : Measure Y) [SFinite μ] {U : Set (Vec d)} (hU : IsOpen U)
    (w u : Y → Vec d → ℝ) (G : Y → Vec d → Vec d) (S : Y → Vec d → Mat d)
    (A : Vec d → Mat d) (e b : Vec d)
    (hw : ∀ y, ContDiff ℝ (⊤ : ℕ∞) (w y))
    (hwi : Integrable (fun z : Y × Vec d => w z.1 z.2) (μ.prod (volume.restrict U)))
    (hmass : ∀ x ∈ U, ∫ y, w y x ∂μ = 1)
    (hui : Integrable (fun z : Y × Vec d => w z.1 z.2 * u z.1 z.2)
      (μ.prod (volume.restrict U)))
    (hGi : ∀ j, Integrable (fun z : Y × Vec d => w z.1 z.2 * G z.1 z.2 j)
      (μ.prod (volume.restrict U)))
    (hDu : ∀ j, Integrable (fun z : Y × Vec d =>
      u z.1 z.2 * coordinateDerivative j (w z.1) z.2) (μ.prod (volume.restrict U)))
    (hSi : ∀ j k, Integrable (fun z : Y × Vec d => w z.1 z.2 * S z.1 z.2 j k)
      (μ.prod (volume.restrict U)))
    (hfluxi : ∀ j, Integrable (fun z : Y × Vec d =>
      w z.1 z.2 * ((A z.2).mulVec (e + G z.1 z.2) - b) j)
      (μ.prod (volume.restrict U)))
    (hDS : ∀ j, Integrable (fun z : Y × Vec d =>
      ((S z.1 z.2).mulVec (gradient (w z.1) z.2)) j) (μ.prod (volume.restrict U)))
    (hweak : ∀ᵐ y ∂μ, HasWeakGradient U (u y) (G y) ∧
      HasWeakRowDivergence U (S y) (fun x => (A x).mulVec (e + G y x) - b)) :
    let H : Vec d → Vec d := fun x j =>
      ∫ y, u y x * coordinateDerivative j (w y) x ∂μ
    let K : Vec d → Vec d := fun x j =>
      ∫ y, ((S y x).mulVec (gradient (w y) x)) j ∂μ
    let D : Vec d → Vec d := fun x j => (∫ y, w y x * G y x j ∂μ) + H x j
    HasWeakGradient U (fun x => ∫ y, w y x * u y x ∂μ) D ∧
      HasWeakRowDivergence U (fun x j k => ∫ y, w y x * S y x j k ∂μ)
        (fun x => (A x).mulVec (e + D x) - b - ((A x).mulVec (H x) - K x)) := by
  dsimp only
  refine ⟨hasWeakGradient_weighted_integral μ hU w u G hw hui hGi hDu
    (hweak.mono fun _ h => h.1), ?_⟩
  have hdiv := hasWeakRowDivergence_weighted_integral μ hU w S
    (fun y x => (A x).mulVec (e + G y x) - b) hw hSi hfluxi hDS
    (hweak.mono fun _ h => h.2)
  apply hasWeakRowDivergence_congr_ae hU hdiv Filter.EventuallyEq.rfl
  have hsections : ∀ᵐ x ∂volume.restrict U,
      Integrable (fun y => w y x) μ ∧
        ∀ j : Fin d, Integrable (fun y => w y x * G y x j) μ :=
    hwi.prod_left_ae.and (ae_all_iff.mpr fun j => (hGi j).prod_left_ae)
  filter_upwards [hsections, ae_restrict_mem hU.measurableSet] with x hx hxU
  ext j
  rw [integral_weight_mulVec_add μ (fun y => w y x) (fun y => G y x) (A x) e b
    hx.1 hx.2 (hmass x hxU) j]
  simp only [Matrix.mulVec, dotProduct, Pi.sub_apply, Pi.add_apply,
    Finset.sum_add_distrib, mul_add]
  ring

end EinsteinRelation.Correctors
