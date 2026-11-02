import EinsteinRelation.Correctors.WeakDivergenceCompactH1Testing
import EinsteinRelation.Correctors.SpatialTestL2Localization
import EinsteinRelation.Correctors.LocalizedEnergyProducts

open MeasureTheory
namespace EinsteinRelation.Correctors

/-- Compact H¹ localization is an admissible test of an actual L² divergence
identity. Source: `paper/main.tex:792`; AKM Lemma 8.2 time-slice energy. -/
theorem weakDivergence_test_cutoff_H1 {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) {u h : Vec d → ℝ} {G F : Vec d → Vec d}
    (hu : MemLp u 2 (volume.restrict U))
    (hG : ∀ j, MemLp (fun x => G x j) 2 (volume.restrict U))
    (hF : ∀ j, MemLp (fun x => F x j) 2 (volume.restrict U))
    (hh : MemLp h 2 (volume.restrict U))
    (hw : HasWeakGradient U u G) (hdiv : HasWeakDivergence U F h)
    {χ : Vec d → ℝ} (hχ : IsSpatialTest U χ) :
    (∫ x in U, dot (F x)
      (fun j => χ x ^ 2 * G x j + 2 * χ x * u x * coordinateDerivative j χ x)) =
      -(∫ x in U, h x * (χ x ^ 2 * u x)) := by
  let w : Vec d → ℝ := fun x => dot (F x) (gradient χ x)
  have huχ := memLp_mul_spatialTest_univ hU.measurableSet hu hχ
  have hhχ := memLp_mul_spatialTest_univ hU.measurableSet hh hχ
  have hFχ j := memLp_mul_spatialTest_univ hU.measurableSet (hF j) hχ
  have hGχ j := memLp_mul_spatialTest_univ hU.measurableSet (hG j) hχ
  have huD j := memLp_mul_spatialTest_univ hU.measurableSet hu
    (isSpatialTest_coordinateDerivative hχ j)
  have hFD j := memLp_mul_spatialTest_univ hU.measurableSet (hF j)
    (isSpatialTest_coordinateDerivative hχ j)
  have hwu : MemLp w 2 volume := by
    unfold w dot gradient
    simpa only [mul_comm] using memLp_finset_sum Finset.univ (fun j _ => hFD j)
  have h0 := weakDivergence_test_compact_H1
    (hasWeakDivergence_mul_spatialTest hdiv hχ)
    (hasWeakGradient_mul_spatialTest hw hχ) huχ hχ.2.1.mul_right
    (fun j => (hGχ j).add (by simpa only [mul_comm] using huD j)) hFχ (hhχ.add hwu)
  have hz {x : Vec d} (hx : x ∉ U) : χ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hs => hx (hχ.2.2 hs))
  have hl : (∫ x, dot (fun j => χ x * F x j)
      (fun j => χ x * G x j + u x * coordinateDerivative j χ x)) =
      ∫ x in U, dot (fun j => χ x * F x j)
        (fun j => χ x * G x j + u x * coordinateDerivative j χ x) := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    simp [hz hx, dot]
  have hr : (∫ x, (χ x * h x + w x) * (χ x * u x)) =
      ∫ x in U, (χ x * h x + w x) * (χ x * u x) := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    simp [hz hx]
  rw [hl,hr] at h0
  obtain ⟨_,_,hcross,henergy⟩ := localized_H1_energy_products_integrable hχ hu hF hG
  have hsource : Integrable (fun x => h x * (χ x ^ 2 * u x)) (volume.restrict U) := by
    have hi : Integrable ((fun x => χ x * h x) * (fun x => χ x * u x))
        (volume.restrict U) :=
      (hhχ.mono_measure (Measure.restrict_le_self (s := U))).integrable_mul
        (huχ.mono_measure (Measure.restrict_le_self (s := U)))
    convert hi using 1
    ext x
    simp only [Pi.mul_apply]
    ring
  have he1 : (∫ x in U, dot (fun j => χ x * F x j)
      (fun j => χ x * G x j + u x * coordinateDerivative j χ x)) =
      (∫ x in U, χ x ^ 2 * dot (F x) (G x)) +
        ∫ x in U, χ x * u x * w x := by
    rw [← integral_add henergy hcross]
    apply integral_congr_ae
    filter_upwards with x
    simp only [dot,gradient,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring
  have he2 : (∫ x in U, (χ x * h x + w x) * (χ x * u x)) =
      (∫ x in U, h x * (χ x ^ 2 * u x)) +
        ∫ x in U, χ x * u x * w x := by
    rw [← integral_add hsource hcross]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by ring
  rw [he1,he2] at h0
  have he3 : (∫ x in U, dot (F x)
      (fun j => χ x ^ 2 * G x j + 2 * χ x * u x * coordinateDerivative j χ x)) =
      (∫ x in U, χ x ^ 2 * dot (F x) (G x)) +
        2 * (∫ x in U, χ x * u x * w x) := by
    rw [← integral_const_mul, ← integral_add henergy (hcross.const_mul 2)]
    apply integral_congr_ae
    filter_upwards with x
    simp only [dot,gradient,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring
  rw [he3]
  linarith only [h0]

end EinsteinRelation.Correctors
